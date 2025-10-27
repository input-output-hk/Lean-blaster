import Lean
import Solver.Optimize.Rewriting.OptimizeForAll
import Solver.Optimize.Rewriting.Utils
import Solver.Optimize.Env

open Lean Meta Elab
namespace Solver.Optimize


/-- Given `#[s c d t e]` corresponding to the arguments of an `ite` or `dite`, such that:
      - s is the sort parameter
      - c is the `cond` operand
      - d is the current decidable instance for the ite cond
      - t is the `then` operand
      - e is the `else` operand

    This function returns `#[s c d' t e] such that `d'` corresponds to the synthesize instance
    obtained for `[Decidable c]`.

    NOTE: This function needs to be called for each ITE as `c` may have been modified
    due to simplification/normalization rules.

    Do nothing if args.size < 3.
-/
def updateITEDecidable (args : Array Expr) : TranslateEnvT (Array Expr) := do
  if Nat.blt args.size 3 then return args
  pure (args.set! 2 (← synthDecidableWithNotFound! args[1]!))

/-- Given `#[s c d t e]` corresponding to the arguments of an `ite` or `dite`, such that:
      - s is the sort parameter
      - c is the `cond` operand
      - d is the current decidable instance for the ite cond
      - t is the `then` operand
      - e is the `else` operand
    This function returns `#[[s c d' e t]` such that `d'` corresponds to the synthesize instance
    obtained for `[Decidable c]`. As can be seen, the `then` and `else` operands are also swapped.
-/
def swapITEAndUpdateDecidable (args : Array Expr) : TranslateEnvT (Array Expr) := do
  -- synthesize decidable instance for cond operand and check if instance is in cache
  let args ← updateITEDecidable args
  -- swap then and else expression
  pure (args.swapIfInBounds 3 4)


/-- Given `c`, `t` and `e` corresponding respectively to the `cond`, `then` and `else` terms
    of an `ite` expression, perform the following normalization rules:
      - When `Type(t) = Prop`
          - return `(c → e1) ∧ (¬ c → e2)`
      - Otherwise:
          - return `none`
-/
def iteToPropExpr? (iteType: Expr) (c : Expr) (t : Expr) (e : Expr) : TranslateEnvT (Option Expr) := do
  if !iteType.isProp then return none
  setRestart
  let leftAnd ← mkImpliesExpr c t
  let rightAnd ← mkImpliesExpr (mkApp (← mkPropNotOp) c) e
  return mkApp2 (← mkPropAndOp) leftAnd rightAnd

/-- Given `thn` and `els` corresponding respectively to the `then` and `else` terms
    of a `dite` expression, perform the following normalization rules:
      - When `Type(t) = Prop ∧ t := fun h : c => e1 ∧ e := fun h : ¬ c => e2`
          - return `(h : c → e1) ∧ (h : ¬ c → e2)`
      - When `Type(t) = Prop ∧ t := c → Prop ∧ e := ¬ c → Prop`
          - return `(h : c → t h) ∧ (h : ¬ c → e h)`
      - When `Type(t) ≠ Prop:
          - return `none`
      - Otherwise
           - return ⊥
-/
def diteToPropExpr? (iteType: Expr) (cond : Expr) (thn : Expr) (els : Expr) : TranslateEnvT (Option Expr) := do
  if !iteType.isProp then return none
  setRestart
  let leftAnd ← toImpliesExpr thn cond
  let rightAnd ← toImpliesExpr els (mkApp (← mkPropNotOp) cond)
  return mkApp2 (← mkPropAndOp) leftAnd rightAnd

  where
    toImpliesExpr (ite : Expr) (c : Expr) : TranslateEnvT Expr := do
     match ite with
     | Expr.lam n t b bi => return mkForall n bi t b
     | _ =>
         if !(← isQuantifiedFun ite) then
            throwEnvError "diteToPropExpr? : lambda/quantified function expected but got {reprStr ite}"
         else
           -- Need to create a lambda term embedding the following application
           -- `fun x : cond => ite x`
           withLocalDecl (← Term.mkFreshBinderName) BinderInfo.default c fun x => do
             mkForallFVars #[x] (ite.beta #[x])


/-- Return `some (true = c')` only when `c := false = c'`.
    This function also checks if `true = c'` is already in cache.
    Otherwise `none`.
-/
def isITEBoolSwap? (c : Expr) : TranslateEnvT (Option Expr) := do
  match eq? c with
  | some (eq_sort, Expr.const ``false _, op2) =>
      setRestart
      return (mkApp3 c.getAppFn eq_sort (← mkBoolTrue) op2)
  | _ => return none

/-- Given `e` a `dite` then/else expression perform the following:
      - When `e := fun h : c => b`:
         - return `b`
      - When `Type(e) := h : c → b`:
         - return `e`
      - Otherwise:
         - return ⊥
-/
def extractDependentITEExpr (e : Expr) : TranslateEnvT Expr := do
  match e with
  | Expr.lam _n _t b _bi => return b
  | _ =>
    if !(← isQuantifiedFun e) then
      throwEnvError "extractDependentITEExpr : lambda/quantified function expected but got {reprStr e}"
    else return e -- case when then/else clause is a quantified function (see theorem `dite_true`).

/-- Given an ite/dite expression:
      - return `some if c' then e2 else e1` when `c := ¬ c'`
      - return `some if true = c' then e2 else e1` when `c := false = c'`
    Otherwise none.
    NOTE: No need to restart as updated hypothesis context
    has already considered negated condition.
-/
def isITESwap? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
 let c := args[1]!
 if let Expr.app (Expr.const ``Not _) ne := c then
    return mkAppN f (← swapITEAndUpdateDecidable (args.set! 1 ne))
 if let some c' ← (isITEBoolSwap? c) then
    return mkAppN f (← swapITEAndUpdateDecidable (args.set! 1 c'))
 return none

/-- Apply the following simplification/normalization rules on `ite` :
     - if c then e1 else e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - if True then e1 else e2 ==> e1
     - if False then e1 else e2 ==> e2
     - if c then e1 else e2 ==> e1 (if c := _ ∈ hypothesisContext.hypothesisMap)
     - if c then e1 else e2 ==> e2 (if ∃ e := _ ∈ hypothesisContext.hypothesisMap ∧ e = ¬ c)
     - if c then e1 else e2 ==> (c → e1) ∧ (¬ c → e2) (if Type(e1) = Prop)
     - if c then e1 else e2 ==> if c' then e2 else e1 (if c := ¬ c')
     - if c then e1 else e2 ==> if true = c' then e2 else e1 (if c := false = c')
     - if a then (if c1 then e1 else e2) else (if c2 then e1 else e2) ==>
          if (a ∧ c1) ∨ (¬ a ∧ c2) then e1 else e2

     - if a then (if c then e1 else e2) else (if c then e1 else e3) ==>
          if c then e1 else (if a then e2 else e3)

     - if a then (if c then e1 else e2) else (if c then e3 else e2) ==>
          if c then (if a then e1 else e3) else e2

     - if a then (dite c (fun h : c => e1) (fun h : ¬ c => e2)
            else (dite c (fun h : c => e1) (fun h : ¬ c => e3) ==>
          dite c (fun h : c => e1) (fun h : ¬ c => if a then e2 else e3)

     - if a then (dite c (fun h : c => e1) (fun h : ¬ c => e2)
            else (dite c (fun h : c => e3) (fun h : ¬ c => e2) ==>
          dite c (fun h : c => if a then e1 else e3) (fun h : ¬ c => e2)

     - if a then (if c then e1 else e2) else (if c then e2 else e1) ==>
          if a = c then e1 else e2

   Assume that f = Expr.const ``ite
   An error is triggered when args.size ≠ 5 (i.e., only fully applied `ite` expected at this stage)
   TODO: consider additional simplification rules.
-/
def optimizeITE (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 5 then throwEnvError "optimizeITE: exactly five arguments expected"
 -- args[0] is sort parmeter
 -- args[1] is cond operand
 -- args[2] is decidable instance parameter on cond
 -- args[3] is then operand
 -- args[4] is else operand
 let iteType := args[0]!
 let c := args[1]!
 let t := args[3]!
 let e := args[4]!
 if (← exprEq t e) then return t
 if let Expr.const ``True _ := c then return t
 if let Expr.const ``False _ := c then return e
 if let some r ← iteReduce? c t e then return r
 if let some r ← iteToPropExpr? iteType c t e then return r
 if let some r ← isITESwap? f args then return r
 if let some r ← iteIteFactorize? c t e then return r
 if let some r ← iteDiteFactorize? c t e then return r
 return mkAppN f (← updateITEDecidable args)

 where
   /-- Given `a`, 't` and `e` the condition, then and else expressions for an ite,
        - When `t := if c1 then e1 else e2` ∧ `e := if c2 then e1 else e2`:
           - return `some $ if (a ∧ c1) ∨ (¬ a ∧ c2) then e1 else e2`
        - When `t := if c then e1 else e2` ∧ `e := if c then e1 else e3`:
           - return `some $ if c then e1 else (if a then e2 else e3)`
        - When `t := if c then e1 else e2` ∧ `e := if c then e3 else e2`:
           - return `some $ if c then (if a then e1 else e3) else e2`
        - When `t := if c then e1 else e2` ∧ `e := if c then e2 else e1`:
           - return `some $ if a = c then e1 else e2`
   -/
   iteIteFactorize? (a : Expr) (t : Expr) (e : Expr) : TranslateEnvT (Option Expr) := do
    let some (sort1, c1, d1, t1, e1) := ite? t | return none
    let some (_sort2, c2, _d2, t2, e2) := ite? e | return none
    if ← exprEq t1 t2 then
      if ← exprEq e1 e2 then
        setRestart
        let and_op ← mkPropAndOp
        let and_e1 := mkApp2 and_op a c1
        let and_e2 := mkApp2 and_op (mkApp (← mkPropNotOp) a) c2
        let or_e := mkApp2 (← mkPropOrOp) and_e1 and_e2
        return mkApp5 f sort1 or_e d1 t1 e1
    if ← exprEq c1 c2 then
      if ← exprEq t1 t2 then
        setRestart
        let ite := mkApp5 f sort1 a d1 e1 e2
        return mkApp5 f sort1 c1 d1 t1 ite
      if (← exprEq e1 e2) then
        setRestart
        let ite := mkApp5 f sort1 a d1 t1 t2
        return mkApp5 f sort1 c1 d1 ite e1
      if ← exprEq t1 e2 <&&> exprEq t2 e1 then
        setRestart
        let eq_cond := mkApp3 (← mkEqOp) (← mkPropType) a c1
        return mkApp5 f sort1 eq_cond d1 t1 e1
    return none

   /-- Given `a`, 't` and `e` the condition, then and else expressions for an ite,
        - When `t := dite c (fun h : c => e1) (fun h : ¬ c => e2)` ∧
               `e := dite c (fun h : c => e1) (fun h : ¬ c => e3)`:
           - return `some $ dite c (fun h : c => e1) (fun h : ¬ c => if a then e2 else e3)`
        - When `t := dite c (fun h : c => e1) (fun h : ¬ c => e2)` ∧
               `e := dite c (fun h : c => e3) (fun h : ¬ c => e2)`:
           - return `some $ dite c (fun h : c => if a then e1 else e3) (fun h : ¬ c => e2)`
   -/
   iteDiteFactorize? (a : Expr) (t : Expr) (e : Expr) : TranslateEnvT (Option Expr) := do
    let some (sort1, c1, d1, t1, e1) := dite? t | return none
    let some (_sort2, c2, _d2, t2, e2) := dite? e | return none
    if ← exprEq c1 c2 then
      if ← exprEq t1 t2 then
        match e1, e2 with
        | Expr.lam x1 tc1 e1' bi1, Expr.lam _x2 _tc2 e2' _bi2 =>
            setRestart
            withLocalDecl x1 bi1 tc1 fun x1' => do
              let ite := mkApp5 f sort1 a d1 (e1'.instantiate1 x1') (e2'.instantiate1 x1')
              let lam ← mkLambdaFVars #[x1'] ite
              return mkApp5 f sort1 c1 d1 t1 lam
        | _, _ => return none
      else if (← exprEq e1 e2) then
        match t1, t2 with
        | Expr.lam x1 tc1 t1' bi1, Expr.lam _x2 _tc2 t2' _bi2 =>
            setRestart
            withLocalDecl x1 bi1 tc1 fun x1' => do
              let ite := mkApp5 f sort1 a d1 (t1'.instantiate1 x1') (t2'.instantiate1 x1')
              let lam ← mkLambdaFVars #[x1'] ite
              return mkApp5 f sort1 c1 d1 lam e1
        | _, _ => return none
      else return none
    else return none

   /-- Given `c`, `t` and `e`, the condition, then and else expressions for an ite,
       perform the following:
        - When `c := _ ∈ hypothesisContext.hypothesisMap`
            - return `some t`
        - When `∃ e := _ ∈ hypothesisContext.hypothesisMap ∧ e = ¬ c`
            - return `some e`
        - Otherwise
            - return `none`
   -/
   iteReduce? (c : Expr) (t : Expr) (e : Expr) : TranslateEnvT (Option Expr) := do
     let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
     if (← inHypMap c hyps).isSome then return t
     if (← notInHypMap c hyps)
     then return e
     else return none

/--  Given `s`, `c`, `decInst`, 't` and `e` corresponding respectively to
     the sort type, ite condition, decidable instance for ite condition,
     then expression and else expression for a `dite`,
     perform the following:
      - When `t : fun h : c => e1` ∧ `e := fun h : ¬ c => e2` ∧ ¬ e1.hasLooseBVars ∧ ¬ e2.hasLooseBVars:
         - return `some (if c then e1 else e2)`
      - Otherwise
         - return `none`
-/
def diteToIte? (s : Expr) (c : Expr) (decInst : Expr) (t : Expr) (e : Expr) : TranslateEnvT (Option Expr) := do
  match t, e with
  | Expr.lam _n1 _c1 e1 _b1, Expr.lam _n2 _c2 e2 _b2 =>
      if !e1.hasLooseBVars && !e2.hasLooseBVars
      then
        setRestart
        return mkApp5 (← mkIteOp) s c decInst e1 e2
      else return none
  | _, _ => return none

/-- Apply simplification/normalization rules on `dite`.
    Note that dependent ite is written with notation `if h : c then t else e`, which
    is the syntactic sugar for `dite c (fun h : c => t) (fun h : ¬ c => e)`.

    The simplifcation/normalization rules applied are:
     - dite c (fun h : c => e1) (fun h : ¬ c => e2) ==> e1 (if e1 =ₚₜᵣ e2)
     - dite True (fun h : True => e1) (fun h : False => e2) ==> e1
     - dite False (fun h : True => e1) (fun h : False => e2) ==> e2
     - dite c (fun h : c => e1) (fun h : ¬ c => e2) ==> e1 (if c := _ ∈ hypothesisContext.hypothesisMap ∧ ¬ e1.hasLooseBVars)
     - dite c (fun h : c => e1) (fun h : ¬ c => e2) ==> e2 (if ∃ e := _ ∈ hypothesisContext.hypothesisMap ∧ ¬ e2.hasLooseBVars ∧ e = ¬ c )
     - dite c (fun h : c => e1) (fun h : ¬ c => e2) ==> e1[h/h'] (if c := some h' ∈ hypothesisContext.hypothesisMap ∧ e1.hasLooseBVars)
     - dite c (fun h : c => e1) (fun h : ¬ c => e2) ==> e1[h/h'] (if ∃ e := some h' ∈ hypothesisContext.hypothesisMap ∧ e2.hasLooseBVars ∧ e = ¬ c)
     - dite c (fun h : c => e1) (fun h : ¬ c => e2) ==> (c → e1) ∧ (¬ c → e2) (if Type(e1) = Prop)
     - dite c (fun h : c => e1) (fun h : ¬ c => e2) ==> dite c' (fun h : c' => e2) (fun h : ¬ c' => e1) (if c = ¬ c')
     - dite c (fun h : c => e1) (fun h : ¬ c => e2) ==> dite true = c' (fun h : true = c' => e2) (fun h : false = c' => e1) (if c := false = c')
     - dite c (fun h : c => e1) (fun h : ¬ c => e2) ==> if c then e1 else e2 (if ¬ e1.hasLooseBVars ∧ ¬ e2.hasLooseBVars)

     - dite a (fun h : a => if c then e1 else e2) (fun h : ¬ a => if c then e1 else e3) ==>
          if c then e1 else (dite a (fun h : a => e2) (fun h : ¬ a => e3) (if ¬ e1.hasLooseBVars)

     - dite a (fun h : a => if c then e1 else e2) (fun h : ¬ a => if c then e3 else e2) ==>
          if c then (dite a (fun h : a => e1) (fun h : ¬ a => e3) else e2 (if ¬ e1.hasLooseBVars)

     - dite a (fun h : a => dite c (fun h : c => e1) (fun h : ¬ c => e2)
               (fun h : ¬ a => dite c (fun h : c => e1) (fun h : ¬ c => e3) ==>
          dite c (fun h : c => e1) (fun h : ¬ c => dite a (fun h : a => e2) (fun h : ¬ a => e3))

     - dite a (fun h : a => dite c (fun h : c => e1) (fun h : ¬ c => e2))
               (fun h : ¬ a => dite c (fun h : c => e3) (fun h : ¬ c => e2)) ==>
          dite c (fun h : c => dite a (fun h : a => e1) (fun h : ¬ a => e3)) (fun h : ¬ c => e2)

    Assume that f = Expr.const ``dite
    An error is triggered when args.size ≠ 5 (i.e., only fully applied `dite` expected at this stage)
    TODO: consider additional simplification rules.
-/
def optimizeDITE (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 5 then throwEnvError "optimizeDITE: exactly five arguments expected"
 -- args[0] is sort parameter
 -- args[1] is cond operand
 -- args[2] is decidable instance parameter on cond
 -- args[3] is then operand
 -- args[4] is else operand
 let iteType := args[0]!
 let c := args[1]!
 let t := args[3]!
 let e := args[4]!
 let thenExpr ← extractDependentITEExpr t
 let elseExpr ← extractDependentITEExpr e
 if (← exprEq thenExpr elseExpr) then return t.beta #[← mkOfDecideEqProof c true]
 if let Expr.const ``True _ := c then return t.beta #[← mkTrueIntro]
 if let Expr.const ``False _ := c then return e.beta #[← mkNotFalse]
 if let some r ← diteReduce? c t then return r
 if let some r ← diteReduce? (← optimizeNot (← mkPropNotOp) #[c] (cacheResult := false)) e then return r
 if let some r ← diteToPropExpr? iteType c t e then return r
 if let some r ← isITESwap? f args then return r
 if let some r ← diteToIte? iteType c args[2]! t e then return r
 if let some r ← diteIteFactorize? c t e then return r
 if let some r ← diteDiteFactorize? c t e then return r
 return mkAppN f (← updateITEDecidable args)

 where

   /-- Given `a`, 't` and `e` the condition, then and else expressions for an dite,
        - When `t := fun : a => if c then e1 else e2` ∧
               `e := fun : ¬ a => if c then e1 else e3` ∧ ¬ e1.hasLooseBVars:
           - return `some $ if c then e1 else (dite a (fun h : a => e2) (fun h : ¬ a => e3)`

        - When `t := fun : a => if c then e1 else e2` ∧
               `e := fun : ¬ a => if c then e3 else e2` ∧ ¬ e2.hasLooseBVars:
           - return `some $ if c then (dite a (fun h : a => e1) (fun h : ¬ a => e3)) else e2`
   -/
   diteIteFactorize? (a : Expr) (t : Expr) (e : Expr) : TranslateEnvT (Option Expr) := do
    match t, e with
    | Expr.lam n1 dc1 thn bi1, Expr.lam n2 dc2 els bi2 =>
        let some (sort1, c1, d1, t1, e1) := ite? thn | return none
        let some (_sort2, c2, _d2, t2, e2) := ite? els | return none
        if ← exprEq c1 c2 then
          if (← exprEq t1 t2) && !t1.hasLooseBVars then
            setRestart
            let lam1 := mkLambda n1 bi1 dc1 e1
            let lam2 := mkLambda n2 bi2 dc2 e2
            let dite := mkApp5 f sort1 a args[2]! lam1 lam2
            return mkApp5 (← mkIteOp) sort1 c1 d1 t1 dite
          if (← exprEq e1 e2) && !e1.hasLooseBVars then
            setRestart
            let lam1 := mkLambda n1 bi1 dc1 t1
            let lam2 := mkLambda n2 bi2 dc2 t2
            let dite := mkApp5 f sort1 a args[2]! lam1 lam2
            return mkApp5 (← mkIteOp) sort1 c1 d1 dite e1
        return none
    | _, _ => return none

   /-- Given `a`, 't` and `e` the condition, then and else expressions for an dite,
        - When `t := fun h : a => dite c (fun h : c => e1) (fun h : ¬ c => e2)` ∧
               `e := fun h : ¬ a => dite c (fun h : c => e1) (fun h : ¬ c => e3)`:
           - return `some $ dite c (fun h : c => e1) (fun h : ¬ c => dite a (fun h : a => e2) (fun h : ¬ a => e3))`

        - When `t := fun h : a => dite c (fun h : c => e1) (fun h : ¬ c => e2)` ∧
               `e := fun h : ¬ a => dite c (fun h : c => e3) (fun h : ¬ c => e2)`:
           - return `some $ dite c (fun h : c => dite a (fun h : a => e1) (fun h : ¬ a => e3)) (fun h : ¬ c => e2)`
   -/
   diteDiteFactorize? (a : Expr) (t : Expr) (e : Expr) : TranslateEnvT (Option Expr) := do
    match t, e with
    | Expr.lam n1 dc1 thn bi1, Expr.lam n2 dc2 els bi2 =>
        let some (sort1, c1, d1, t1, e1) := dite? thn | return none
        let some (_sort2, c2, _d2, t2, e2) := dite? els | return none
        if ← exprEq c1 c2 then
          withLocalDecl n1 bi1 dc1 fun n1' => do
            withLocalDecl n2 bi2 dc2 fun n2' => do
              if (← exprEq t1 t2) then
                match e1.instantiate1 n1', e2.instantiate1 n2' with
                | Expr.lam x1 tc1 e1' bi1', Expr.lam _x2 _tc2 e2' _bi2' =>
                    setRestart
                    withLocalDecl x1 bi1' tc1 fun x1' => do
                      let lam1 ← mkLambdaFVars #[n1'] (e1'.instantiate1 x1')
                      let lam2 ← mkLambdaFVars #[n2'] (e2'.instantiate1 x1')
                      let dite ← mkLambdaFVars #[x1'] (mkApp5 f sort1 a args[2]! lam1 lam2)
                      return mkApp5 f sort1 c1 d1 t1 dite
                |_, _ => return none
              else if (← exprEq e1 e2) then
                match t1.instantiate1 n1', t2.instantiate1 n2' with
                | Expr.lam x1 tc1 t1' bi1', Expr.lam _x2 _tc2 t2' _bi2' =>
                    setRestart
                    withLocalDecl x1 bi1' tc1 fun x1' => do
                      let lam1 ← mkLambdaFVars #[n1'] (t1'.instantiate1 x1')
                      let lam2 ← mkLambdaFVars #[n2'] (t2'.instantiate1 x1')
                      let dite ← mkLambdaFVars #[x1'] (mkApp5 f sort1 a args[2]! lam1 lam2)
                      return mkApp5 f sort1 c1 d1 dite e1
                |_, _ => return none
              else return none
         else return none
    | _, _ => return none

   /-- Given `cond` and `t` the condition and then/else expression for a dite expression,
       perform the following:
        - When `t := fun h : c => e ∧ c := _ ∈ hypothesisContext.hypothesisMap ∧ ¬ e.hasLooseBVars`
            - return `some e`
        - When `t := fun h : c => e ∧ c := some h' ∈ hypothesisContext.hypothesisMap ∧ e.hasLooseBVars`
            - return `some e[h/h']`
        - When `t := c → α ∧ c := some h ∈ hypothesisContext.hypothesisMap`
            - return `some t h`
        - Otherwise
            - return `none`
   -/
   diteReduce? (cond : Expr) (t : Expr) : TranslateEnvT (Option Expr) := do
     let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
     match t with
     | Expr.lam _h c b _bi =>
         match hyps.get? c with
         | none => return none
         | some m =>
            if !b.hasLooseBVars then return b
            if let some h' := m then return (t.beta #[h'])
            return none
     | _ =>
        if !(← isQuantifiedFun t) then
          throwEnvError "diteReduce?: lambda/quantified function expression expected but got {reprStr t}"
        match hyps.get? cond with
        | some (some h') => return (t.beta #[h'])
        | _ => return none

/-- Apply simplification/normalization rules of if then else expressions. -/
def optimizeIfThenElse? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const n _ := f | return none
  match n with
  | ``ite => optimizeITE f args
  | ``dite => optimizeDITE f args
  | _ => return none

end Solver.Optimize
