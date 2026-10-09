import Lean
import Blaster.Optimize.Env.HashConsing
import Blaster.Optimize.Env.InstantiateMVars

open Lean Meta Blaster.Data.HashMap

namespace Blaster.Optimize

inductive InstantiateStack where
  | WaitAppFun (e a : Expr) (offset : USize)
  | WaitAppArg (e f : Expr) (offset : USize)
  | WaitForallType (e b : Expr) (offset : USize)
  | WaitForallBody (e t : Expr) (offset : USize)
  | WaitLambdaType (e b : Expr) (offset : USize)
  | WaitLambdaBody (e t : Expr) (offset : USize)
  | WaitLetType (e v b : Expr) (offset : USize)
  | WaitLetValue (e t b : Expr) (offset : USize)
  | WaitLetBody (e t v : Expr) (offset : USize)
  | WaitMData (e : Expr) (offset : USize)
  | WaitProjExpr (e : Expr) (offset : USize)
deriving Repr


@[always_inline, inline]
private unsafe def instantiateSharedRevRangeAux (e : Expr) (offset s n : USize) (subst : Array Expr) : TranslateEnvT Expr := do
 let rec go (cur : Expr) (isResult : Bool) (offset : USize) (stk : Array InstantiateStack) (cache : InstCache) : TranslateEnvT Expr := do
  if isResult then
      let r := cur
      if stk.usize > 0 then
        let topIdx := stk.usize - 1
        let next := stk.uget topIdx lcProof
        match next with
        | .WaitAppFun e a offset' =>
             let stk := stk.uset topIdx (.WaitAppArg e r offset') lcProof
             go a false offset' stk cache
        | .WaitAppArg e f offset' =>
             let r' ← e.updateAppExpr! f r
             go r' true offset stk.pop (cache.insert (mkInstKey e offset') r')
        | .WaitForallType e b offset' =>
             let stk := stk.uset topIdx (.WaitForallBody e r offset') lcProof
             go b false (offset' + 1) stk cache
        | .WaitForallBody e t offset' =>
             let r' ← e.updateForallExpr! t r
             go r' true offset stk.pop (cache.insert (mkInstKey e offset') r')
        | .WaitLambdaType e b offset' =>
             let stk := stk.uset topIdx (.WaitLambdaBody e r offset') lcProof
             go b false (offset' + 1) stk cache
        | .WaitLambdaBody e t offset' =>
             let r' ← e.updateLambdaExpr! t r
             go r' true offset stk.pop (cache.insert (mkInstKey e offset') r')
        | .WaitLetType e v b offset' =>
             let stk := stk.uset topIdx (.WaitLetValue e r b offset') lcProof
             go v false offset' stk cache
        | .WaitLetValue e t b offset' =>
             let stk := stk.uset topIdx (.WaitLetBody e t r offset') lcProof
             go b false (offset' + 1) stk cache
        | .WaitLetBody e t v offset' =>
             let r' ← e.updateLetExpr! t v r
             go r' true offset stk.pop (cache.insert (mkInstKey e offset') r')
        | .WaitMData e offset' =>
             let r' ← e.updateMDataExpr! r
             go r' true offset stk.pop (cache.insert (mkInstKey e offset') r')
        | .WaitProjExpr e offset' =>
             let r' ← e.updateProjExpr! r
             go r' true offset stk.pop (cache.insert (mkInstKey e offset') r')
      else return r
  else
      let e := cur
      let s' := s + offset
      if s'.toNat >= e.looseBVarRange
      then go e true offset stk cache
      else
        let cached := cache.getD (mkInstKey e offset) instCacheMiss
        if !exprEq cached instCacheMiss then go cached true offset stk cache
        else
           match e with
           | .bvar idx =>
               let idx' := idx.toUSize
               if idx' >= s' then
                 if idx' < offset + n then
                    let r := subst.uget (n - (idx' - offset) - 1) lcProof
                    go r true offset stk (cache.insert (mkInstKey e offset) r)
                 else
                   let r ← mkBVarExpr (idx - n.toNat)
                   go r true offset stk (cache.insert (mkInstKey e offset) r)
               else go e true offset stk (cache.insert (mkInstKey e offset) e)
           | .app f a =>
                let stk := stk.push (.WaitAppFun e a offset)
                go f false offset stk cache
           | .letE _ t v b _ =>
                let stk := stk.push (.WaitLetType e v b offset)
                go t false offset stk cache
           | .forallE _ t b _ =>
                let stk := stk.push (.WaitForallType e b offset)
                go t false offset stk cache
           | .lam _ t b _ =>
                let stk := stk.push (.WaitLambdaType e b offset)
                go t false offset stk cache
           | .mdata _ b =>
                let stk := stk.push (.WaitMData e offset)
                go b false offset stk cache
           | .proj _ _ b =>
                let stk := stk.push (.WaitProjExpr e offset)
                go b false offset stk cache
           | _ => unreachable! -- const/fvar/mvar/sort/lit are unreachable
 go e false offset (Array.emptyWithCapacity (e.approxDepth.toNat + 16)) (HashMap.emptyWithCapacity 64)

/--
Similar to `Lean.Expr.instantiateRevRange` but assume the input is maximally shared and ensure
that the result is also maximally shared.
Assume `beginIdx ≤ endIdx` and `endIdx ≤ subst.size`
-/
def instantiateSharedRevRange (e : Expr) (beginIdx endIdx : Nat) (subst : Array Expr) : TranslateEnvT Expr :=
  if _ : beginIdx > endIdx then unreachable! else
  if _ : endIdx > subst.size then unreachable! else
  let s := beginIdx.toUSize
  let n := endIdx.toUSize - s
  unsafe instantiateSharedRevRangeAux e 0 s n subst


@[always_inline, inline]
def instantiateShared1 (e : Expr) (subst : Expr) : TranslateEnvT Expr := do
  if e.hasLooseBVars then instantiateSharedRevRange e 0 1 #[subst] else return e


/-- Given a fun body `λ α₀ → ... λ αₙ → body` and `params` the implicit parameters info
    for the corresponding function, perform the following actions:
      - let A := [α₀, ..., αₙ]
      - let B := [ A[i] | i ∈ [0..n] ∧ ¬ params[i].isInstance ]
      - let S := [ A[i] | i ∈ [0..n] ∧ params[i].isInstance ]
      - let R := [ params[i].effectiveArg | i ∈ [0..n] ∧ params[i].isInstance ]
      - let β₀, .., βₘ = B
      - return `λ β₀ → ... λ βₘ → body [S[0]/R[0]] ... [S[k]/R[k]]` with k = S.size-1

    Assume that params.size ≤ n
    Assume that inputs are maximally shared and ensure that the result is also maximally shared.
-/
partial def specializeLambda (fbody : Expr) (params : ImplicitParameters) : TranslateEnvT Expr :=
  let rec visit (idx : Nat) (stop : Nat) (e : Expr) : TranslateEnvT Expr := do
    if idx ≥ stop then return e
    else
      match e with
      | Expr.lam _ t b _ =>
         let p := params[idx]!
         if !p.isInstance
         then e.updateLambdaExpr! t (← visit (idx + 1) stop b)
         else visit (idx + 1) stop (← instantiateShared1 b p.effectiveArg)
      | _ => return e
  visit 0 params.size fbody

/-- Given `e` of the form `∀ (a₁ : A₁) ... (aₙ : Aₙ), B[a₁, ..., aₙ]`
    and `p₁ : A₁, ... pₘ : Aₙ`, return `B[p₁, ..., pₘ]`.
    Assume that inputs are maximally shared
    Guarantee that result is also maximally shared

-/
partial def betaForAll (e : Expr) (args : Array Expr) : TranslateEnvT Expr :=
  let finish (e : Expr) (i : Nat) : TranslateEnvT Expr :=
    if !e.hasLooseBVars then return e
    else instantiateSharedRevRange e 0 i args
  let rec visit (i : Nat) (e : Expr) : TranslateEnvT Expr := do
    if i < args.size then
       match e with
       | Expr.forallE _ _ b _ => visit (i + 1) b
       | _ => finish e i
    else finish e i
  visit 0 e


@[always_inline, inline]
def betaLambdaSharedRange (e : Expr) (beginIdx : Nat) (endIdx : Nat) (args : Array Expr) : TranslateEnvT Expr :=
  let finish (e : Expr) (i : Nat) : TranslateEnvT Expr :=
    if !e.hasLooseBVars then return e
    else instantiateSharedRevRange e 0 i args
  let rec visit (e : Expr) (i : Nat) : TranslateEnvT Expr := do
    if i < endIdx then
      match e with
      | .lam _ _ b _ => visit b (i + 1)
      | _ => mkAppRangeExpr (← finish e i) i endIdx args
    else finish e i
  if args.isEmpty then return e
  else visit e beginIdx

@[always_inline, inline]
def betaLambdaShared (e : Expr) (args : Array Expr) : TranslateEnvT Expr :=
  betaLambdaSharedRange e 0 args.size args

/-- `(fun x => e) a` ==> `e[x/a]`. -/
def headBetaShared (e : Expr) : TranslateEnvT Expr :=
  let f := e.getAppFn'
  if f.isLambda then betaLambdaShared f e.getAppArgs else return e

end Blaster.Optimize
