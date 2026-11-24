import Lean
import Blaster.Optimize.Env.Instantiate

open Lean Meta Blaster.Data.HashSet Blaster.Data.HashMap

namespace Blaster.Optimize

@[always_inline, inline]
private unsafe def abstractFVarsAux (e : Expr) (endIdx : USize) (xs : Array Expr) : TranslateEnvT Expr := do
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
      if e.hasFVar then
        let cached := cache.getD (mkInstKey e offset) instCacheMiss
        if !exprEq cached instCacheMiss then go cached true offset stk cache
        else
          match e with
          | .fvar _ =>
               if let some bidx := toDeBruijn? e then
                 let r ← mkBVarExpr (offset.toNat + bidx)
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
          | _ => unreachable! -- const/bvar/mvar/sort/lit are unreachable
       else go e true offset stk cache
 go e false 0 (Array.emptyWithCapacity (e.approxDepth.toNat + 16)) (HashMap.emptyWithCapacity 64)

 where
  toDeBruijn? (fvar : Expr) : Option Nat :=
    let rec go (bidx : Nat) (i : USize) : Option Nat :=
      if exprEq (xs.uget i lcProof) fvar then
        some bidx
      else if i > 0 then
        go (bidx + 1) (i - 1)
      else
        none
    go 0 endIdx

/--
Abstract free variables `xs[0...endIdx]` in expression `e`, converting them to de Bruijn indices.
Aassume the input is maximally shared and ensure that the result is also maximally shared.
-/
def abstractFVarsRange (e : Expr) (endIdx : Nat) (xs : Array Expr) : TranslateEnvT Expr :=
  if !e.hasFVar then return e
  else if endIdx < xs.size then
    unsafe abstractFVarsAux e endIdx.toUSize xs
  else return e

/--
Abstracts free variables `xs` in expression `e`, converting them to de Bruijn indices.
It is an abbreviation for `abstractFVarsRange e 0 xs`.
-/
abbrev abstractFVars (e : Expr) (xs : Array Expr) : TranslateEnvT Expr := abstractFVarsRange e (xs.size - 1)  xs

structure FVarsEnv where
  visited : HashSet PtrExpr
  fvars : HashSet PtrExpr

instance : Inhabited FVarsEnv where
  default := ⟨{},{}⟩

abbrev FVarsEnvT := StateRefT FVarsEnv TranslateEnvT

@[always_inline, inline]
def visitedExpr (e : PtrExpr) : FVarsEnvT Unit := do
  modify fun ⟨visited, fvars⟩ => ⟨visited.insert e, fvars⟩

@[always_inline, inline]
def visitedFVar (e : PtrExpr) : FVarsEnvT Unit := do
  modify fun ⟨visited, fvars⟩ => ⟨visited.insert e, fvars.insert e⟩

@[always_inline, inline]
private unsafe def fVarsInExprAux (e : Expr) : TranslateEnvT (HashSet PtrExpr) := do
 let rec go (entry : Option Expr) (stk : Array HashConsStack) : FVarsEnvT (HashSet PtrExpr) := do
  match entry with
  | none =>
      if stk.usize > 0 then
        let topIdx := stk.usize - 1
        let next := stk.uget topIdx lcProof
        match next with
        | .WaitAppFun e a =>
             let stk := stk.uset topIdx (.WaitAppArg e e) lcProof
             go (some a) stk
        | .WaitAppArg e _ =>
             visitedExpr e
             go none stk.pop
        | .WaitForallType e b =>
             let stk := stk.uset topIdx (.WaitForallBody e e) lcProof
             go (some b) stk
        | .WaitForallBody e _ =>
             visitedExpr e
             go none stk.pop
        | .WaitLambdaType e b =>
             let stk := stk.uset topIdx (.WaitLambdaBody e e) lcProof
             go (some b) stk
        | .WaitLambdaBody e _ =>
             visitedExpr e
             go none stk.pop
        | .WaitLetType e v b =>
             let stk := stk.uset topIdx (.WaitLetValue e e b) lcProof
             go (some v) stk
        | .WaitLetValue e _ b =>
             let stk := stk.uset topIdx (.WaitLetBody e e e) lcProof
             go (some b) stk
        | .WaitLetBody e _ _
        | .WaitMData e
        | .WaitProjExpr e =>
             visitedExpr e
             go none stk.pop
      else return (← get).fvars
  | some e =>
      if (← get).visited.contains e
      then go none stk
      else
        if e.hasFVar then
         match e with
         | .bvar _ | .mvar _ | .const .. | .sort .. | .lit .. => unreachable!
         | .fvar .. =>
              visitedFVar e
              go (some $ ← inferTypeEnv e) stk
         | .app f a =>
              let stk := stk.push (.WaitAppFun e a)
              go (some f) stk
         | .letE _ t v b _ =>
              let stk := stk.push (.WaitLetType e v b)
              go (some t) stk
         | .forallE _ t b _ =>
              let stk := stk.push (.WaitForallType e b)
              go (some t) stk
         | .lam _ t b _ =>
              let stk := stk.push (.WaitLambdaType e b)
              go (some t) stk
         | .mdata _ b =>
              let stk := stk.push (.WaitMData e)
              go (some b) stk
         | .proj _ _ b =>
              let stk := stk.push (.WaitProjExpr e)
              go (some b) stk
        else
          visitedExpr e
          go none stk
 go (some e) (Array.emptyWithCapacity e.approxDepth.toNat)|>.run' ⟨HashSet.emptyWithCapacity e.approxDepth.toNat, {}⟩

/-- Return all fvar expressions in `e`. Assume input is maximally shared. -/
@[always_inline, inline]
def fVarsInExpr (e : Expr) : TranslateEnvT (HashSet PtrExpr) :=
  unsafe fVarsInExprAux e

@[always_inline, inline]
private def referencedFVars (xs : Array Expr) (e : Expr) (usedOnly : Bool) : TranslateEnvT (Array Expr) := do
  if usedOnly then
    let usedSet ← fVarsInExpr e
    let rec go (idx : Nat) (stop : Nat) (acc : Array Expr) : Array Expr :=
      if idx ≥ stop then acc
      else
        let fv := xs[idx]!
        if usedSet.contains fv
        then go (idx + 1) stop (acc.push fv)
        else go (idx + 1) stop acc
     return go 0 xs.size (Array.emptyWithCapacity xs.size)
  else return xs

/--
Similar to `mkLambdaFVars`, but assume the input is maximally shared and ensure
that the result is also maximally shared.
When `usedOnly = true` then only variables that the expression body depends on will appear.
-/
def mkLambdaFVarsExpr (xs : Array Expr) (e : Expr) (usedOnly := false) : TranslateEnvT Expr := do
  let xs ← referencedFVars xs e usedOnly
  let b ← abstractFVars e xs
  xs.size.foldRevM (init := b) fun i _ b => do
    let x := xs[i]
    let decl ← x.fvarId!.getEnvDecl
    -- We need to hash cons type for x, especially if x is a globally declared fvar
    let type ← abstractFVarsRange (← inferTypeEnv x) (i - 1) xs
    mkLambdaExpr decl.userName decl.binderInfo type b


def mkLambdaFVarExpr (x : Expr) (e : Expr) : TranslateEnvT Expr := do
  if containsFVar e x then
    mkLambdaFVarsExpr #[x] e
  else
    let decl ← x.fvarId!.getEnvDecl
    mkLambdaExpr decl.userName decl.binderInfo decl.type e

/--
Similar to `mkForallFVars`, but assume the input is maximally shared and ensure
that the result is also maximally shared.
When `usedOnly = true` then only variables that the expression body depends on will appear.
-/
def mkForallFVarsExpr (xs : Array Expr) (e : Expr) (usedOnly := false) : TranslateEnvT Expr := do
  let xs ← referencedFVars xs e usedOnly
  let b ← abstractFVars e xs
  xs.size.foldRevM (init := b) fun i _ b => do
    let x := xs[i]
    let decl ← x.fvarId!.getEnvDecl
    -- We need to hash cons type for x, especially if x is a globally declared fvar
    let type ← abstractFVarsRange (← inferTypeEnv x) i xs
    mkForallExpr decl.userName decl.binderInfo type b

def mkForallFVarExpr (x : Expr) (e : Expr) : TranslateEnvT Expr := do
  if containsFVar e x then
    mkForallFVarsExpr #[x] e
  else
    let decl ← x.fvarId!.getEnvDecl
    mkForallExpr decl.userName decl.binderInfo decl.type e

/--
Similar to `mkLetFVars`, but assume the input is maximally shared and ensure
that the result is also maximally shared.
-/
def mkLetFVarsExpr (xs : Array Expr) (e : Expr) : TranslateEnvT Expr := do
  let b ← abstractFVars e xs
  xs.size.foldRevM (init := b) fun i _ b => do
    let x := xs[i]
    let LocalDecl.ldecl _ _ n _type value nondep _ ← x.fvarId!.getEnvDecl |
      throwEnvError "mkLetFVarsExpr: let declaration expected for {x}"
    -- We need to hash cons type for x
    let type ← abstractFVarsRange (← inferTypeEnv x) i xs
    let value ← abstractFVarsRange value i xs
    mkLetExpr n type value b nondep


end Blaster.Optimize
