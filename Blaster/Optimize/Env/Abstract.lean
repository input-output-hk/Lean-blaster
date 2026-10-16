import Lean
import Blaster.Optimize.Env.Instantiate

open Lean Meta Blaster.Data.HashSet Blaster.Data.HashMap

namespace Blaster.Optimize

@[always_inline, inline]
private def fvarUniqIdx (id : FVarId) : Nat :=
  match id.name with
  | .num _ n => n + 1
  | _ => 0

/-- Max fvar `_uniq` watermark of `e`: the largest `_uniq` index of an fvar in
    `e`, `0` when fvar-free (memoized in `RewriteDependencies.fvarMax`). A
    target fvar with a uniq index above it does not occur in `e` — an O(1)
    occurs-check for the dominant "close a freshly introduced binder over an
    old payload" pattern. Fvars whose id is not a `_uniq` numeral count as `0`
    on the query side, which disables the skip for them. Iterative two-pass
    walk; each distinct subtree is computed once per translation. -/
private def maxFVarUniq (root : Expr) : TranslateEnvT Nat := do
  if !root.hasFVar then return 0
  -- `cache0` is a read-only snapshot; new results accumulate in the local
  -- `fresh` map (exclusive, in-place) and are merged back with one `modify`.
  let ref ← getRewriteDependencies
  let cache0 := (← ref.get).fvarMax
  if let some v := cache0.find? ⟨root⟩ then return v
  let childrenOf : Expr → Array Expr := fun e =>
    match e with
    | .app f a => #[f, a]
    | .lam _ t b _ | .forallE _ t b _ => #[t, b]
    | .letE _ t v b _ => #[t, v, b]
    | .mdata _ b | .proj _ _ b => #[b]
    | _ => #[]
  let known : Std.HashMap PtrExpr Nat → Expr → Option Nat := fun fresh e =>
    match cache0.find? ⟨e⟩ with
    | some v => some v
    | none => fresh.get? ⟨e⟩
  let mut fresh : Std.HashMap PtrExpr Nat := {}
  let mut stk : Array Expr := #[root]
  while !stk.isEmpty do
    let e := stk.back!
    if !e.hasFVar then
      stk := stk.pop
    else if (known fresh e).isSome then
      stk := stk.pop
    else if let .fvar id := e then
      -- unknown-name fvars watermark as `1`: nonzero (present) but below any
      -- `_uniq` numeral only when the query side is also unknown (idx 0),
      -- where the skip is disabled anyway.
      fresh := fresh.insert ⟨e⟩ (max 1 (fvarUniqIdx id))
      stk := stk.pop
    else
      let cs := childrenOf e
      let mut pending : Array Expr := #[]
      for c in cs do
        if c.hasFVar && (known fresh c).isNone then
          pending := pending.push c
      if pending.isEmpty then
        let mut v := 0
        for c in cs do
          if c.hasFVar then
            v := max v ((known fresh c).getD 0)
        fresh := fresh.insert ⟨e⟩ v
        stk := stk.pop
      else
        stk := stk ++ pending
  let res := (fresh.get? ⟨root⟩).getD 0
  ref.modify fun st => {st with fvarMax := fresh.fold (init := st.fvarMax) fun m k v => m.insert k v}
  return res

/-- Memoized `containsFVar`, with the watermark fast path: re-closing the same
    (body, fvar) pair — which the optimizer does constantly — is O(1), and a
    freshly created fvar is O(1)-absent from any older subtree. -/
def containsFVarCached (e : Expr) (x : Expr) : TranslateEnvT Bool := do
  if !e.hasFVar then return false
  let xi := fvarUniqIdx x.fvarId!
  if xi > 0 then
    if (← maxFVarUniq e) < xi then return false
  let ref ← getRewriteDependencies
  let key := ((⟨e⟩ : PtrExpr), x.fvarId!)
  match (← ref.get).fvarOccurs.find? key with
  | some b => return b
  | none =>
      let b := containsFVar e x
      ref.modify fun st => {st with fvarOccurs := st.fvarOccurs.insert key b}
      return b

@[always_inline, inline]
private unsafe def abstractFVarsAux (e : Expr) (endIdx : USize) (xs : Array Expr) : TranslateEnvT Expr := do
 -- Watermark for the whole target window: a subtree whose max fvar uniq index
 -- is below the smallest target index cannot mention any target, so it is
 -- returned unchanged without being walked.  `0` (an unknown-name target)
 -- disables the skip.
 let minTarget : Nat := Id.run do
   let mut m := 0
   for i in [0:endIdx.toNat+1] do
     let ti := fvarUniqIdx xs[i]!.fvarId!
     if ti == 0 then return 0
     m := if m == 0 then ti else min m ti
   return m
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
             inheritCtorChoiceInfo e r'
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
             inheritCtorChoiceInfo e r'
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
        else if minTarget > 0 && (← maxFVarUniq e) < minTarget then
          -- provably mentions no target fvar: unchanged, subtree not walked
          go e true offset stk (cache.insert (mkInstKey e offset) e)
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
  if ← containsFVarCached e x then
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
  if ← containsFVarCached e x then
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
