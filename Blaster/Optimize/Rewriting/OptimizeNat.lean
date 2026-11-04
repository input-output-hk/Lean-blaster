import Lean
import Blaster.Optimize.Rewriting.OptimizeEq
import Blaster.Optimize.Rewriting.OptimizeRelational
import Blaster.Optimize.Rewriting.Utils
import Blaster.Optimize.Env

open Lean Meta
namespace Blaster.Optimize

/-- Apply the following simplification/normalization rules on `Nat.add` :
     - 0 + n ==> n
     - N1 + N2 ===> N1 "+" N2
     - N1 + (N2 + n) ==> (N1 "+" N2) + n
     - n1 + n2 ==> n2 + n1 (if n2 <ₒ n1)
   Assume that f = Expr.const ``Nat.add.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Nat.add` expected at this stage)
-/
def optimizeNatAdd (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeNatAdd: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 match isNatValue? op1, isNatValue? op2 with
 | some 0, _ =>  return op2
 | some n1, some n2 => evalBinNatOp Nat.add n1 n2
 | nv1,  _ =>
    if let some r ← cstAddProp? nv1 op2 then return r
    return (mkApp2 f op1 op2)

 where
   /- Given `mv1` and `op2`, return `some ((N1 "+" N2) + n)` when
      `mv1 := some N1 ∧ op2 := N2 + n`.
      Otherwise `none`
   -/
   cstAddProp? (mv1 : Option Nat) (op2 : Expr) : TranslateEnvT (Option Expr) := do
    match mv1, toNatCstOpExpr? op2 with
    | some n1, (NatCstOpInfo.NatAddExpr n2 e2) => return (mkApp2 f (← evalBinNatOp Nat.add n1 n2) e2)
    | _, _ => return none


/-- Apply the following simplification/normalization rules on `Nat.sub` :
     - n1 - n2 ==> 0 (if n1 =ₚₜᵣ n2)
     - 0 - n ==> 0
     - n - 0 ==> n
     - N1 - N2 ==> N1 "-" N2
     - N1 - (N2 + n) ==> (N1 "-" N2) - n
     - (N1 - n) - N2 ==> (N1 "-" N2) - n
     - (n - N1) - N2 ==> n - (N1 "+" N2)
     - (N1 + n) - N2 ==> (N1 "-" N2) + n (if N1 ≥ N2)
   Assume that f = Expr.const ``Nat.sub.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Nat.sub` expected at this stage)
-/
def optimizeNatSub (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeNatSub: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 if exprEq op1 op2 then return (← mkNatLitExpr 0)
 match isNatValue? op1, isNatValue? op2 with
 | some 0, _
 | _, some 0 => return op1
 | some n1, some n2 => evalBinNatOp Nat.sub n1 n2
 | nv1, nv2 =>
   if let some r ← cstSubPropRight? nv1 op2 then return r
   if let some r ← cstSubPropLeft? op1 nv2 then return r
   return (mkApp2 f op1 op2)

 where
   /- Given `mv1` and `op2` return `some ((N1 "-" N2) - n)` when
      `mv1 := some N1 ∧ op2 := (N2 + n)`. Otherwise `none`.
   -/
   cstSubPropRight? (mv1 : Option Nat) (op2 : Expr) : TranslateEnvT (Option Expr) := do
    match mv1, toNatCstOpExpr? op2 with
    | some n1, NatCstOpInfo.NatAddExpr n2 e2 =>
        setRestart
        return mkApp2 f (← evalBinNatOp Nat.sub n1 n2) e2
    | _, _ => return none

   /- Given `op1` and `mv2`,
       - return `some ((N1 "-" N2) - n)` when `op1 := (N1 - n) ∧ mv2 := some N2`
       - return `some (n - (N1 "+" N2))` when `op1 := (n - N1) ∧ mv2 := some N2`
       - return `some ((N1 "-" N2) + n)` when `op1 := N1 + n ∧ mv2 := some N2 ∧ N1 ≥ N2`
      Otherwise `none`
   -/
   cstSubPropLeft? (op1 : Expr) (mv2 : Option Nat) : TranslateEnvT (Option Expr) := do
     match mv2 with
     | some n2 =>
          match toNatCstOpExpr? op1 with
          | some (NatCstOpInfo.NatSubLeftExpr n1 e1) =>
              setRestart
              return mkApp2 f (← evalBinNatOp Nat.sub n1 n2) e1
          | some (NatCstOpInfo.NatSubRightExpr e1 n1) =>
              -- no need to restart here
              return (mkApp2 f e1 (← evalBinNatOp Nat.add n1 n2))
          | some (NatCstOpInfo.NatAddExpr n1 e1) =>
              if Nat.ble n2 n1 then
                setRestart
                return mkApp2 (← mkNatAddOp) (← evalBinNatOp Nat.sub n1 n2) e1
              else return none
          | _ => return none
     | _ => return none

-- /-- TODO: Apply the following advanced constant propagation rules on `Nat.add` and `Nat.sub`:
--      - (N1 + n1) + (N2 + n2) ==> (N1 "+" N2) + (n1 + n2) (TODO)
--      - (N1 - n1) - (N2 - n2) ==> (N1 "-" N2) + (n2 - n1) (TODO)
--      - (N1 - n1) - (n2 - N2) ==> (N1 "+" N2) - (n1 + n2) (TODO)
--      - (n1 - N1) - (N2 - n2) ==> (n1 + n2) - ("N1 "+" N2) (TODO)
--      - (n1 - N1) - (n2 - N2) ==> ("N2 "-" N1) + (n1 - n2) (TODO)
--    NOTE: `(x - y) + (p + q)` is normalized as `(p + q) + (x - y)` via `reorderArgs`
-- -/

/-- Apply the following simplification/normalization rules on `Nat.pow` :
     - n ^ 0 ==> 1
     - N1 ^ N2 ==> N1 "^" N2
   Assume that f = Expr.const ``Nat.pow.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Nat.pow` expected at this stage)

-/
def optimizeNatPow (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeNatPow: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 match isNatValue? op1, isNatValue? op2 with
 | _, some 0 => return (← mkNatLitExpr 1)
 | some n1, some n2 => evalBinNatOp Nat.pow n1 n2
 | _, _ => return (mkApp2 f op1 op2)

/-- Apply the following simplification/normalization rules on `Nat.mul` :
     - 0 * n ==> 0
     - 1 * n ==> n
     - N1 + N2 ==> N1 "*" N2
     - N1 * (N2 * n) ==> (N1 "*" N2) * n
     - n1 * n2 ==> n2 * n1 (if n2 <ₒ n1)
     - n * n^m ===> n ^ (m + 1)
   Assume that f = Expr.const ``Nat.mul.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Nat.mul` expected at this stage)
-/
def optimizeNatMul (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeNatMul: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 match isNatValue? op1, isNatValue? op2 with
 | some 0, _ => return op1
 | some 1, _ => return op2
 | some n1, some n2 => evalBinNatOp Nat.mul n1 n2
 | nv1, _ =>
   if let some r ← cstMulProp? nv1 op2 then return r
   if let some r ← mulPowReduceExpr? op1 op2 then return r
   return (mkApp2 f op1 op2)

 where
   /- Given `mv1` and `op2`, return `some ((N1 "*" N2) * n)`
      when `mv1 := some N1 ∧ op2 := (N2 * n)`
      Otherwise `none`.
   -/
   cstMulProp? (mv1 : Option Nat) (op2 : Expr) : TranslateEnvT (Option Expr) := do
     match mv1, toNatCstOpExpr? op2 with
     | some n1, some (NatCstOpInfo.NatMulExpr n2 e2) =>
         return (mkApp2 f (← evalBinNatOp Nat.mul n1 n2) e2)
     | _, _ => return none

   /-- Given `e1` and `e2` corresponding to the operands for `Nat.mul`,
       return some e1^(m + 1) only when `e2 := e1 ^ m`
   -/
   mulPowReduceExpr? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
    match natPow? e2 with
    | some (op1, op2) =>
       if exprEq e1 op1 then
         setRestart
         let addExpr := mkApp2 (← mkNatAddOp) (← mkNatLitExpr 1) op2
         return mkApp2 (← mkNatPowOp) e1 addExpr
       return none
    | none => return none

/-! ## Bitwise operators

`Nat.land`, `Nat.lor` and `Nat.xor` are opaque (see `opaqueFuns`): they are not unfolded to
`Nat.bitwise`, whose well-founded recursion cannot be handled. The rules below rewrite them to
arithmetic whenever the bit layout of the operands is syntactically known, which is the usual
case for masking and packing in word-level code (e.g. EVM bytecode). Any remaining application
is translated to an exact recursive Smt definition (see `defineNatBitwise`).
-/

/-- Bound used as the number of trailing zero bits of `0`. -/
def natBitwiseZeroTZ : Nat := 1048576

/-- Return `some k` only when `n = 2^k`. -/
def natLog2Exact? (n : Nat) : Option Nat :=
  if n == 0 then none
  else
    let k := Nat.log2 n
    if 2 ^ k == n then some k else none

/-- Number of trailing zero bits of `n` (`natBitwiseZeroTZ` for `0`). -/
def natTrailingZeros (n : Nat) : Nat :=
  if n == 0 then natBitwiseZeroTZ
  else go (Nat.log2 n + 1) n 0
 where
   go : Nat → Nat → Nat → Nat
   | 0, _, acc => acc
   | fuel + 1, n, acc => if n % 2 == 1 then acc else go fuel (n / 2) (acc + 1)

/-- Smallest `k` such that `n ≤ 2^k`. -/
def natCeilLog2 (n : Nat) : Nat :=
  if n ≤ 1 then 0
  else
    let k := Nat.log2 n
    if 2 ^ k == n then k else k + 1

/-! ### Bit support

`natBitSupport e` over-approximates the set of bits that may be set in `e`, as sorted,
disjoint intervals `[lo, hi)` of bit positions (`hi = natBitwiseZeroTZ` stands for
unbounded), computed from the syntactic shape of `e`: literals, `% 2^k`, `/ 2^k`,
`* 2^k`, sums of operands with disjoint supports, and bitwise operators.
-/

/-- Sort intervals and merge the overlapping or adjacent ones. -/
def bitsNormalize (s : List (Nat × Nat)) : List (Nat × Nat) :=
  let sorted := (s.filter (fun (lo, hi) => lo < hi)).mergeSort (fun a b => a.1 ≤ b.1)
  sorted.foldr (fun (lo, hi) acc =>
    match acc with
    | (lo', hi') :: rest => if lo' ≤ hi then (lo, max hi hi') :: rest else (lo, hi) :: acc
    | [] => [(lo, hi)]) []

def bitsUnion (a b : List (Nat × Nat)) : List (Nat × Nat) := bitsNormalize (a ++ b)

def bitsInter (a b : List (Nat × Nat)) : List (Nat × Nat) :=
  bitsNormalize (a.flatMap fun (lo, hi) => b.filterMap fun (lo', hi') =>
    if max lo lo' < min hi hi' then some (max lo lo', min hi hi') else none)

def bitsDisjoint (a b : List (Nat × Nat)) : Bool := (bitsInter a b).isEmpty

def bitsSubset (a b : List (Nat × Nat)) : Bool := bitsInter a b == bitsNormalize a

def bitsShiftUp (s : List (Nat × Nat)) (k : Nat) : List (Nat × Nat) :=
  s.map fun (lo, hi) => (min (lo + k) natBitwiseZeroTZ, min (hi + k) natBitwiseZeroTZ)

def bitsShiftDown (s : List (Nat × Nat)) (k : Nat) : List (Nat × Nat) :=
  bitsNormalize (s.map fun (lo, hi) => (lo - k, if hi == natBitwiseZeroTZ then hi else hi - k))

/-- The highest bound of a support (`0` when empty). -/
def bitsTop (s : List (Nat × Nat)) : Nat := s.foldl (fun acc (_, hi) => max acc hi) 0

/-- The lowest bound of a support (`natBitwiseZeroTZ` when empty). -/
def bitsBottom (s : List (Nat × Nat)) : Nat := s.foldl (fun acc (lo, _) => min acc lo) natBitwiseZeroTZ

/-- The maximal runs of one bits of `n`, as intervals. -/
def natRuns (n : Nat) : List (Nat × Nat) :=
  go (Nat.log2 n + 1) n 0 []
 where
   go : Nat → Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
   | 0, _, _, acc => acc.reverse
   | fuel + 1, n, pos, acc =>
     if n == 0 then acc.reverse
     else
       let k := natTrailingZeros n
       let rest := n / 2 ^ k
       let w := natTrailingZeros (rest + 1)
       go fuel (rest / 2 ^ w) (pos + k + w) ((pos + k, pos + k + w) :: acc)

/-- Return `true` when `h` is a hypothesis in scope. -/
def hypothesisInScope (h : Expr) : TranslateEnvT Bool :=
  return (← get).optEnv.hypothesisContext.hypothesisMap.contains h

/-- Bit widths tried when looking for a bound `e < 2^k` among the hypotheses. -/
def natBitBoundCandidates : List Nat := [1, 8, 16, 32, 64, 128, 160, 192, 224, 256]

/-- Atoms whose bounds are looked up among the hypotheses: variables, projections of
    atoms (e.g. `env.msg.caller`) and applications of a variable (e.g. `world q`). -/
partial def isBoundAtom (e : Expr) : Bool :=
  match e with
  | Expr.fvar _ => true
  | Expr.proj _ _ s => isBoundAtom s
  | Expr.mdata _ e => isBoundAtom e
  | Expr.app .. => e.getAppFn.isFVar
  | _ => false

/-- `[(0, k)]` for the smallest candidate `k` such that `e < 2^k` is a hypothesis in scope,
    when `e` is an atom (`isBoundAtom`); unbounded otherwise. Only atoms are looked up:
    each lookup builds (and hash-conses) the expressions `e < 2^k`, which for arbitrary
    subterms of a large term would fill the hash-consing cache. -/
def natBitSupportFromHyps (e : Expr) : TranslateEnvT (List (Nat × Nat)) := do
  if !isBoundAtom e then return [(0, natBitwiseZeroTZ)]
  for k in natBitBoundCandidates do
    if ← hypothesisInScope (← mkNatLtExpr e (← mkNatLitExpr (2 ^ k))) then return [(0, k)]
  return [(0, natBitwiseZeroTZ)]

/-- How deep `natBitSupport` looks into a term. The patterns it serves (masks, packed
    fields) are shallow, while the operands of `% 2^k` and `/ 2^k` along a long symbolic
    execution can be large: the bound keeps each call cheap. -/
def natBitSupportDepth : Nat := 6

/-- See the section comment. Terms whose shape gives no bound (variables, applications of
    other functions, or terms below the depth bound) are bounded by the hypotheses in scope,
    e.g. `x < 2^160`. -/
partial def natBitSupport (e : Expr) (depth := natBitSupportDepth) :
    TranslateEnvT (List (Nat × Nat)) := do
  let unbounded := [(0, natBitwiseZeroTZ)]
  let natBitSupport (e : Expr) := natBitSupport e (depth - 1)
  match isNatValue? e with
  | some n => return if n == 0 then [] else natRuns n
  | none =>
    if depth == 0 then return ← natBitSupportFromHyps e
    match e.getAppFn, e.getAppArgs with
    | Expr.const ``Nat.mod _, #[x, m] =>
        let sx ← natBitSupport x
        match isNatValue? m with
        | some m =>
          if m == 0 then return sx
          -- `x % 2^k` keeps the low bits of `x`
          else if (natLog2Exact? m).isSome then return bitsInter sx [(0, natCeilLog2 m)]
          -- otherwise only `x % m ≤ x` and `x % m < m` are known
          else return upTo (min (natCeilLog2 m) (bitsTop sx))
        | none => return upTo (min (bitsTop (← natBitSupport m)) (bitsTop sx))
    | Expr.const ``Nat.div _, #[x, d] =>
        match isNatValue? d with
        | some d =>
          if d == 0 then return []
          else match natLog2Exact? d with
            | some k => return bitsShiftDown (← natBitSupport x) k
            | none =>
              let t := bitsTop (← natBitSupport x)
              return if t == natBitwiseZeroTZ then unbounded else [(0, t - Nat.log2 d)]
        | none => return upTo (bitsTop (← natBitSupport x))
    | Expr.const ``Nat.mul _, #[a, b] =>
        match isNatValue? a with
        | some c =>
          match natLog2Exact? c with
          | some k => return bitsShiftUp (← natBitSupport b) k
          | none => return mulSupport (natRuns c) (← natBitSupport b)
        | none => return mulSupport (← natBitSupport a) (← natBitSupport b)
    | Expr.const ``Nat.add _, #[a, b] =>
        let sa ← natBitSupport a
        let sb ← natBitSupport b
        if bitsDisjoint sa sb then return bitsUnion sa sb
        else
          let t := max (bitsTop sa) (bitsTop sb)
          return [(min (bitsBottom sa) (bitsBottom sb), if t == natBitwiseZeroTZ then t else t + 1)]
    | Expr.const ``Nat.sub _, #[a, _] => return upTo (bitsTop (← natBitSupport a))
    | Expr.const ``Nat.lor _, #[a, b]
    | Expr.const ``Nat.xor _, #[a, b] => return bitsUnion (← natBitSupport a) (← natBitSupport b)
    | Expr.const ``Nat.land _, #[a, b] => return bitsInter (← natBitSupport a) (← natBitSupport b)
    | Expr.const ``Blaster.dite' _, #[_, _, t, f] =>
        match t, f with
        | Expr.lam _ _ tb _, Expr.lam _ _ fb _ =>
          if tb.hasLooseBVars || fb.hasLooseBVars then natBitSupportFromHyps e
          else return bitsUnion (← natBitSupport tb) (← natBitSupport fb)
        | _, _ => natBitSupportFromHyps e
    | _, _ => natBitSupportFromHyps e
 where
   /-- Every bit below `t`. -/
   upTo (t : Nat) : List (Nat × Nat) := if t == 0 then [] else [(0, t)]

   /-- `a * b`: the trailing zeros add up and the widths add up. -/
   mulSupport (sa sb : List (Nat × Nat)) : List (Nat × Nat) :=
     if sa.isEmpty || sb.isEmpty then []
     else
       let lo := bitsBottom sa + bitsBottom sb
       let ta := bitsTop sa
       let tb := bitsTop sb
       if ta == natBitwiseZeroTZ || tb == natBitwiseZeroTZ then [(min lo natBitwiseZeroTZ, natBitwiseZeroTZ)]
       else [(lo, ta + tb)]

/-- Return `true` when `e1` and `e2` have disjoint bits (see `natBitSupport`). -/
def natDisjointBits (e1 e2 : Expr) : TranslateEnvT Bool :=
  return bitsDisjoint (← natBitSupport e1) (← natBitSupport e2)

/-- `e` restricted to the bits `[lo, hi)`, i.e. `2^lo * ((e % 2^hi) / 2^lo)`, omitting the
    parts that the support `s` of `e` makes unnecessary. -/
def mkBitExtract (e : Expr) (s : List (Nat × Nat)) (lo hi : Nat) : TranslateEnvT Expr := do
  let e ← if hi ≥ bitsTop s then pure e else pure (mkApp2 (← mkNatModOp) e (← mkNatLitExpr (2 ^ hi)))
  if lo ≤ bitsBottom s then return e
  let d := mkApp2 (← mkNatDivOp) e (← mkNatLitExpr (2 ^ lo))
  return mkApp2 (← mkNatMulOp) (← mkNatLitExpr (2 ^ lo)) d

/-- The addends of a sum, i.e. the leaves of a `Nat.add` tree. -/
partial def natAddends (e : Expr) : List Expr :=
  match e.getAppFn, e.getAppArgs with
  | Expr.const ``Nat.add _, #[a, b] => natAddends a ++ natAddends b
  | _, _ => [e]

/-- The sum of `es` (`0` when empty). -/
def mkNatSum (es : List Expr) : TranslateEnvT Expr := do
  match es with
  | [] => mkNatLitExpr 0
  | e :: rest => rest.foldlM (fun acc x => do return mkApp2 (← mkNatAddOp) acc x) e

/-- Given `e % 2^k` (`m = 2^k`), return:
     - `some e` when `e < 2^k` by its bit support;
     - `some ((Σ parts') % 2^k)` when `e` is a sum some of whose addends are multiples of
       `2^k` by their bit support, `parts'` being the other addends (without the `% 2^k`
       when `Σ parts' < 2^k` by its bit support);
     - `none` otherwise.
   The result is built from optimized subterms and needs no further rewriting, so no
   restart is requested: a restart inside an `ite`/`match` branch may re-optimize the
   branch from its original body, where the rule fires again, indefinitely.
-/
def bitModReduce? (f : Expr) (e : Expr) (m : Nat) : TranslateEnvT (Option Expr) := do
  let some k := natLog2Exact? m | return none
  if bitsTop (← natBitSupport e) ≤ k then return some e
  let parts := natAddends e
  if parts.length ≤ 1 then return none
  let kept ← parts.filterM fun p => return bitsBottom (← natBitSupport p) < k
  if kept.length == parts.length then return none
  let rest ← mkNatSum kept
  if bitsTop (← natBitSupport rest) ≤ k then return some rest
  return some (mkApp2 f rest (← mkNatLitExpr m))

/-- Given `e / 2^k` (`d = 2^k`, `k > 0`), return:
     - `some 0` when `e < 2^k` by its bit support;
     - `some (Σ (hᵢ / 2^k) + (Σ lⱼ) / 2^k)` when `e` is a sum whose addends `hᵢ` are
       multiples of `2^k` by their bit support (division distributes over them exactly);
       the last term is omitted when `Σ lⱼ < 2^k` by its bit support;
     - `none` otherwise.
   Each `hᵢ / 2^k` is simplified directly (see `divPart`) rather than by requesting a
   restart (see `bitModReduce?`).
-/
partial def bitDivReduce? (f : Expr) (e : Expr) (d : Nat) : TranslateEnvT (Option Expr) := do
  let some k := natLog2Exact? d | return none
  if k == 0 then return none
  if bitsTop (← natBitSupport e) ≤ k then return some (← mkNatLitExpr 0)
  let parts := natAddends e
  if parts.length ≤ 1 then return none
  let hi ← parts.filterM fun p => return k ≤ bitsBottom (← natBitSupport p)
  let lo ← parts.filterM fun p => return bitsBottom (← natBitSupport p) < k
  if hi.isEmpty then return none
  let hiDivs ← hi.mapM fun p => divPart f p k
  let loSum ← mkNatSum lo
  let loDiv ← if lo.isEmpty || bitsTop (← natBitSupport loSum) ≤ k then pure []
              else pure [mkApp2 f loSum (← mkNatLitExpr d)]
  return some (← mkNatSum (hiDivs ++ loDiv))
 where
   /-- `p / 2^k` for an optimized `p`: literals are divided, a constant factor `c * y`
       absorbs the division when `2^k ∣ c` (`(c / 2^k) * y`) or when `c = 2^j`, `j < k`
       (`y / 2^(k - j)`, exact), and sums are distributed over recursively. -/
   divPart (f p : Expr) (k : Nat) : TranslateEnvT Expr := do
     if k == 0 then return p
     if let some n := isNatValue? p then return ← mkNatLitExpr (n / 2 ^ k)
     match toNatCstOpExpr? p with
     | some (NatCstOpInfo.NatMulExpr c y) =>
       if c % 2 ^ k == 0 then
         let c' := c / 2 ^ k
         if c' == 1 then return y
         return mkApp2 (← mkNatMulOp) (← mkNatLitExpr c') y
       if let some j := natLog2Exact? c then return ← divBy f y (k - j)
     | _ => pure ()
     divBy f p k
   /-- `y / 2^k`, through `bitDivReduce?` when it applies. -/
   divBy (f y : Expr) (k : Nat) : TranslateEnvT Expr := do
     if k == 0 then return y
     if let some r ← bitDivReduce? f y (2 ^ k) then return r
     return mkApp2 f y (← mkNatLitExpr (2 ^ k))

/-- Given `e1` and `e2` corresponding to the operands for `Nat.div` (i.e., `e1 / e2`),
    return `some n` only when one of the following conditions is satisfied:
     - `e1 := m * n` ∧ e2 = m ∧
        (0 < m := _ ∈ hypothesisContext.hypothesisMap ∨ ¬ (0 = m) := _ ∈ hypothesisContext.hypothesisMap); or
     - `e1 := n * m` ∧ e2 = m ∧
        (0 < m := _ ∈ hypothesisContext.hypothesisMap ∨ ¬ (0 = m) := _ ∈ hypothesisContext.hypothesisMap);
    Otherwise, return none.
-/
def mulNatDivReduceExpr? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
  match natMul? e1 with
  | some (op1, op2) =>
     if exprEq op1 e2 then if (← nonZeroNatInHyps e2) then return some op2
     if exprEq op2 e2 then if (← nonZeroNatInHyps e2) then return some op1
     return none
  | none => return none

/-- Given `e1` and `e2` corresponding to the operands for `Nat.div` (i.e., `e1 / e2`),
    return `some 1` only when the following conditions are satisfied:
      - e1 =ₚₜᵣ e2 ∧
      - 0 < e1 := _ ∈ hypothesisContext.hypothesisMap ∨ ¬ (0 = e1) := _ ∈ hypothesisContext.hypothesisMap
    Otherwise, return none.
-/
def natDivSelfReduce? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
  if !(exprEq e1 e2) then return none
  if (← nonZeroNatInHyps e1)
  then return ← mkNatLitExpr 1
  else return none

/-- Apply the following simplification/normalization rules on `Nat.div` :
     - n / 0 ==> 0
     - n / 1 ==> n
     - 0 / n ==> 0
     - N1 / N2 ==> N1 "/" N2
     - (n / N1) / N2 ==> n / (N1 "*" N2)
     - (N1 * n) / N2 ===> ((N1 "/" Nat.gcd N1 N2) * n) / (N2 "/" Nat.gcd N1 N2) (if N2 > 0 ∧ Nat.gcd N1 N2 ≠ 1)
     - n / n ==> 1 (if 0 < n := _ ∈ hypothesisContext.hypothesisMap ∨
                       ¬ (0 = n) := _ ∈ hypothesisContext.hypothesisMap)
     - (m * n) / m | (n * m) / m ==> n (if 0 < m := _ ∈ hypothesisContext.hypothesisMap ∨
                                           ¬ (0 = m) := _ ∈ hypothesisContext.hypothesisMap)
     - bit-field rules for `n / 2^k` (see `bitDivReduce?`)

   Assume that f = Expr.const ``Nat.div.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Nat.div` expected at this stage)

-/
def optimizeNatDiv (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeNatDiv: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 match isNatValue? op1, isNatValue? op2 with
 | _, some 0 => return op2
 | _, some 1
 | some 0, _ => return op1
 | some n1, some n2 => evalBinNatOp Nat.div n1 n2
 | _, nv2 =>
   if let some r ← cstDivProp? op1 nv2 then return r
   if let some r ← natDivSelfReduce? op1 op2 then return r
   if let some r ← mulNatDivReduceExpr? op1 op2 then return r
   if let some d := nv2 then
     if let some r ← bitDivReduce? f op1 d then return r
   return (mkApp2 f op1 op2)

 where

   /- Given `op1` and `mv2`,
        - return `some (n / (N1 "*" N2))` when `op1 := (n / N1) ∧ mv2 := some N2`
        - return `some (((N1 "/" Nat.gcd N1 N2) * n) / (N2 "/" Nat.gcd N1 N2))`
          when `op1 := (N1 * n) ∧ mv2 := some N2`
      Otherwise `none`.
      Assumes that N2 > 0
   -/
   cstDivProp? (op1 : Expr) (mv2 : Option Nat) : TranslateEnvT (Option Expr) := do
     match mv2 with
     | some n2 =>
         match toNatCstOpExpr? op1 with
         | some (NatCstOpInfo.NatDivRightExpr e1 n1) =>
             -- no need to restart here
             return (mkApp2 f e1 (← evalBinNatOp Nat.mul n1 n2))
         | some (NatCstOpInfo.NatMulExpr n1 e1) =>
             let gcd := if n1 < n2 then Nat.gcd n1 n2 else Nat.gcd n2 n1
             if gcd == 1 then return none
             setRestart
             let mulExpr := mkApp2 (← mkNatMulOp) (← evalBinNatOp Nat.div n1 gcd) e1
             return mkApp2 f mulExpr (← evalBinNatOp Nat.div n2 gcd)
         | _ => return none
     | _ => return none

/-- Given `e1` and `e2` corresponding to the operands for `Nat.mod` (i.e., `e1 % e2`),
    return `some 0` only when one of the following conditions is satisfied:
     - e1 =ₚₜᵣ e2; or
     - `e1 := m * n` ∧ e2 = m; or
     - `e1 := n * m` ∧ e2 = m;
    Otherwise, return none.
-/
def natModToZeroExpr? (e1 : Expr) (e2 : Expr) : TranslateEnvT (Option Expr) := do
  if exprEq e1 e2 then return (some (← mkNatLitExpr 0))
  match natMul? e1 with
  | some (op1, op2) =>
     if exprEq op1 e2 || exprEq op2 e2 then return (← mkNatLitExpr 0)
     return none
  | none => return none

/-- Return `true` when `e1 < e2 := _ ∈ hypothesisContext.hypothesisMap`, in which case
    `e1 % e2 = e1`. (Typical in word-level code: a value known to fit in `N` bits masked to
    `N` bits, e.g. an address `a < 2^160` masked with `2^160 - 1`.)
-/
def modBoundedInHyps (e1 : Expr) (e2 : Expr) : TranslateEnvT Bool := do
  hypothesisInScope (← mkNatLtExpr e1 e2)

/-- Apply the following simplification/normalization rules on `Nat.mod` :
     - n % 0 ==> n
     - n % 1 ==> 0
     - 0 % n ==> 0
     - N1 % N2 ==> N1 "%" N2
     - (N1 * n) % N2 ==> 0 (if N1 % N2 = 0)
     - n1 % n2 ==> 0 (if n1 =ₚₜᵣ n2)
     - (m * n) % m | (n * m) % m ==> 0
     - n % m ==> n (if n < m := _ ∈ hypothesisContext.hypothesisMap)
     - bit-field rules for `n % 2^k` (see `bitModReduce?`)
   Assume that f = Expr.const ``Nat.mod.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Nat.mod` expected at this stage)
-/

def optimizeNatMod (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeNatMod: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 match isNatValue? op1, isNatValue? op2 with
 | _, some 0 => return op1
 | _, some 1 => mkNatLitExpr 0
 | some 0, _ => return op1
 | some n1, some n2 => evalBinNatOp Nat.mod n1 n2
 | _, nv2 =>
   if let some r ← cstModProp? op1 nv2 then return r
   if let some r ← natModToZeroExpr? op1 op2 then return r
   if (← modBoundedInHyps op1 op2) then return op1
   if let some m := nv2 then
     if let some r ← bitModReduce? f op1 m then return r
   return (mkApp2 f op1 op2)

 where
   /- Given `op1` and `mv2`, return `some 0`
      when `op1 := N1 * n ∧ mv2 := N2 ∧ N1 % N2 = 0`
      Otherwise `none`.
      Assumes that N2 > 0
   -/
   cstModProp? (op1 : Expr) (mv2 : Option Nat) : TranslateEnvT (Option Expr) := do
    match toNatCstOpExpr? op1, mv2 with
    | some (NatCstOpInfo.NatMulExpr n1 _e1), some n2 =>
        if Nat.mod n1 n2 == 0
        then some <$> mkNatLitExpr 0
        else return none
    | _, _ => return none

/-- Normalize `Nat.beq x y` to `x == y` only when option normalizeFunCall is set to `true`.
    Assume that f = Expr.const ``Nat.beq
    NOTE: This normalization rule is still required here mainly
    to properly handle the case where another rec function is equivalent to `Nat.beq`
--/
def optimizeNatBeq (f : Expr) (b_args : Array Expr) : TranslateEnvT Expr := do
  if !(← isOptimizeRecCall) then return mkAppN f b_args
  setRestart
  return mkAppN (← mkNatBEqOp) b_args

/-- Normalize `Nat.ble x y` to `decide' (x ≤ y)` only when option normalizeFunCall is set to `true`.
    Assume that f = Expr.const ``Nat.ble
    NOTE: This normalization rule is still required here mainly
    to properly handle the case where another rec function is equivalent to `Nat.beq`
-/
def optimizeNatble (f : Expr) (b_args : Array Expr) : TranslateEnvT Expr := do
  if !(← isOptimizeRecCall) then return mkAppN f b_args
  setRestart
  let leExpr := mkAppN (← mkNatLeOp) b_args
  return mkApp (← mkBlasterDecideConst) leExpr

/-- `some (x, p, w, q)` when `e` is the bit field `((x / 2^p) % 2^w) * 2^q`, i.e. bits
    `[p, p + w)` of `x` moved to position `q`. The division is absent when `p = 0`, the
    product when `q = 0`, and the modulo when the field is unbounded
    (`w = natBitwiseZeroTZ`). Literals are not fields (they are folded elsewhere). -/
def natBitField? (e : Expr) : Option (Expr × Nat × Nat × Nat) :=
  let pow2Lit? (n : Expr) : Option Nat := (isNatValue? n).bind natLog2Exact?
  let (q, e) := match e.getAppFn, e.getAppArgs with
    | Expr.const ``Nat.mul _, #[c, y] => match pow2Lit? c with | some q => (q, y) | none => (0, e)
    | _, _ => (0, e)
  let (w, e) := match e.getAppFn, e.getAppArgs with
    | Expr.const ``Nat.mod _, #[y, m] =>
        match pow2Lit? m with | some w => (w, y) | none => (natBitwiseZeroTZ, e)
    | _, _ => (natBitwiseZeroTZ, e)
  let (p, x) := match e.getAppFn, e.getAppArgs with
    | Expr.const ``Nat.div _, #[y, d] => match pow2Lit? d with | some p => (p, y) | none => (0, e)
    | _, _ => (0, e)
  if (isNatValue? x).isSome then none else some (x, p, w, q)

/-- The bit field `((x / 2^p) % 2^w) * 2^q` (see `natBitField?`). -/
def mkNatBitField (x : Expr) (p w q : Nat) : TranslateEnvT Expr := do
  let mut e := x
  if p > 0 then e := mkApp2 (← mkNatDivOp) e (← mkNatLitExpr (2 ^ p))
  if w != natBitwiseZeroTZ then e := mkApp2 (← mkNatModOp) e (← mkNatLitExpr (2 ^ w))
  if q > 0 then e := mkApp2 (← mkNatMulOp) (← mkNatLitExpr (2 ^ q)) e
  return e

/-- Merge two adjacent bit fields `(p, w, q)` of the same value, the first being the lower:
      ((x / 2^p) % 2^w) * 2^q + ((x / 2^(p+w)) % 2^v) * 2^(q+w) = ((x / 2^p) % 2^(w+v)) * 2^q
    (with an unbounded upper field, the result is unbounded too). -/
def mergeAdjacentFields (lo hi : Nat × Nat × Nat) : Option (Nat × Nat × Nat) :=
  let (pl, wl, ql) := lo
  let (ph, wh, qh) := hi
  if wl != natBitwiseZeroTZ && ph == pl + wl && qh == ql + wl then
    some (pl, if wh == natBitwiseZeroTZ then wh else wl + wh, ql)
  else none

/-- An addend of a sum during field merging: unchanged, or a merged bit field. -/
inductive FieldPart where
  | orig (e : Expr) (field : Option (Expr × Nat × Nat × Nat))
  | merged (x : Expr) (p w q : Nat)

def FieldPart.field? : FieldPart → Option (Expr × Nat × Nat × Nat)
  | .orig _ f => f
  | .merged x p w q => some (x, p, w, q)

/-- Merge one pair of adjacent bit fields of the same value, if any. -/
def mergeOnePair (ps : List FieldPart) : Option (List FieldPart) :=
  let idx := ps.zipIdx
  let pair := idx.findSome? fun (a, i) => a.field?.bind fun (x1, p1, w1, q1) =>
    idx.findSome? fun (b, j) =>
      if i == j then none
      else b.field?.bind fun (x2, p2, w2, q2) =>
        if exprEq x1 x2 then
          (mergeAdjacentFields (p1, w1, q1) (p2, w2, q2)).map fun r => (i, j, x1, r)
        else none
  pair.map fun (i, j, x, (p, w, q)) =>
    FieldPart.merged x p w q :: (idx.filter fun (_, k) => k != i && k != j).map (·.1)

/-- Merge, among the addends of `e1 + e2`, the adjacent bit fields of the same value
    (`mergeAdjacentFields`) until none remain; `none` when nothing merges. The whole sum is
    considered because the addends of a sum are reordered: adjacent fields need not be
    siblings. On a word read byte by byte, this reassembles a single field of the word. -/
def mergeBitFields? (e1 e2 : Expr) : TranslateEnvT (Option Expr) := do
  let parts := natAddends e1 ++ natAddends e2
  if parts.length > 64 then return none
  let ps := parts.map fun e => FieldPart.orig e (natBitField? e)
  if (ps.filter (·.field?.isSome)).length < 2 then return none
  let rec loop : Nat → List FieldPart → Bool → List FieldPart × Bool
    | 0, ps, merged => (ps, merged)
    | fuel + 1, ps, merged =>
      match mergeOnePair ps with
      | some ps' => loop fuel ps' true
      | none => (ps, merged)
  let (ps, merged) := loop parts.length ps false
  if !merged then return none
  setRestart
  let es ← ps.mapM fun
    | .orig e _ => pure e
    | .merged x p w q => mkNatBitField x p w q
  return some (← mkNatSum es)

/-- `Nat.add` with bit-field merging (`mergeBitFields?`) before the rules of
    `optimizeNatAdd`. -/
def optimizeNatAddFields (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  if args.size == 2 then
    if let some r ← mergeBitFields? args[0]! args[1]! then return r
  optimizeNatAdd f args

/-- Apply the following simplification/normalization rules on `Nat.land` :
     - 0 &&& n ==> 0
     - n &&& n ==> n
     - N1 &&& N2 ==> N1 "&&&" N2
     - n1 &&& n2 ==> 0 (if n1 and n2 have syntactically disjoint bits)
     - N &&& n ==> n (if the bits of `n` are among those of `N`)
     - N &&& n ==> Σ 2^lo * ((n % 2^hi) / 2^lo), over the runs `[lo, hi)` of one bits of
       `N` that meet the bits of `n` (at most four runs), e.g.
         (2^k - 1) &&& n ==> n % 2^k and (2^m - 2^k) &&& n ==> 2^k * ((n % 2^m) / 2^k)
   Assume that f = Expr.const ``Nat.land and that literal operands appear first (see `reorderNatOp`).
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Nat.land` expected at this stage)
-/
def optimizeNatLand (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeNatLand: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 if exprEq op1 op2 then return op1
 match isNatValue? op1, isNatValue? op2 with
 | some 0, _ => return op1
 | some n1, some n2 => evalBinNatOp Nat.land n1 n2
 | some n1, none =>
    let s ← natBitSupport op2
    let runs := bitsInter (natRuns n1) s
    if runs.isEmpty then return ← mkNatLitExpr 0
    if bitsSubset s (natRuns n1) then return op2
    if runs.length ≤ 4 then
      setRestart
      let parts ← runs.mapM fun (lo, hi) => mkBitExtract op2 s lo hi
      let add ← mkNatAddOp
      return parts.tail.foldl (fun acc p => mkApp2 add acc p) parts.head!
    return mkApp2 f op1 op2
 | _, _ =>
    if ← natDisjointBits op1 op2 then return ← mkNatLitExpr 0
    return mkApp2 f op1 op2

/-- Apply the following simplification/normalization rules on `Nat.lor` :
     - 0 ||| n ==> n
     - n ||| n ==> n
     - N1 ||| N2 ==> N1 "|||" N2
     - n1 ||| n2 ==> n1 + n2 (if n1 and n2 have syntactically disjoint bits)
   Assume that f = Expr.const ``Nat.lor and that literal operands appear first (see `reorderNatOp`).
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Nat.lor` expected at this stage)
-/
def optimizeNatLor (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeNatLor: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 if exprEq op1 op2 then return op1
 match isNatValue? op1, isNatValue? op2 with
 | some 0, _ => return op2
 | some n1, some n2 => evalBinNatOp Nat.lor n1 n2
 | _, _ =>
    if ← natDisjointBits op1 op2 then
      setRestart
      return mkApp2 (← mkNatAddOp) op1 op2
    return mkApp2 f op1 op2

/-- Apply the following simplification/normalization rules on `Nat.xor` :
     - 0 ^^^ n ==> n
     - n ^^^ n ==> 0
     - N1 ^^^ N2 ==> N1 "^^^" N2
     - n1 ^^^ n2 ==> n1 + n2 (if n1 and n2 have syntactically disjoint bits)
   Assume that f = Expr.const ``Nat.xor and that literal operands appear first (see `reorderNatOp`).
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Nat.xor` expected at this stage)
-/
def optimizeNatXor (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeNatXor: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 if exprEq op1 op2 then return ← mkNatLitExpr 0
 match isNatValue? op1, isNatValue? op2 with
 | some 0, _ => return op2
 | some n1, some n2 => evalBinNatOp Nat.xor n1 n2
 | _, _ =>
    if ← natDisjointBits op1 op2 then
      setRestart
      return mkApp2 (← mkNatAddOp) op1 op2
    return mkApp2 f op1 op2

/-- Apply simplification/normalization rules on `Nat` operators. -/
@[always_inline, inline]
def optimizeNat? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const n _ := f | return none
  match n with
  | ``Nat.add => optimizeNatAddFields f args
  | ``Nat.sub => optimizeNatSub f args
  | ``Nat.mul => optimizeNatMul f args
  | ``Nat.div => optimizeNatDiv f args
  | ``Nat.mod => optimizeNatMod f args
  | ``Nat.beq => optimizeNatBeq f args
  | ``Nat.ble => optimizeNatble f args
  | ``Nat.pow => optimizeNatPow f args
  | ``Nat.land => optimizeNatLand f args
  | ``Nat.lor => optimizeNatLor f args
  | ``Nat.xor => optimizeNatXor f args
  | _=> return none

end Blaster.Optimize
