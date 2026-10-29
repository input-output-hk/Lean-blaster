import Lean
import Blaster.Optimize.Expr
import Blaster.Optimize.Env

open Lean Meta Elab

namespace Blaster.Optimize

/-- Return `true` only when e correspond to `List.nil`. -/
def isNilList (e : Expr) : Bool :=
  match e with
  | Expr.app (Expr.const ``List.nil _) _sort => true
  | _ => false

/-- Return `some u` only when e correspond to `List.nil u`. -/
def isNilList? (e : Expr) : Option (List Level) :=
  match e with
  | Expr.app (Expr.const ``List.nil u) _sort => u
  | _ => none

/-- Given `f := Expr.const ``List.get?Internal`, `lsort` the corresponding list sort, `slist` the list argument and
    `idx` the index argument, perform the following:
      - When some n := isNatValue? idx
          - When `slist := [e₀, e₁, ..., eₖ]`
              - return `some $ mkOptionExpr lsort u (some eₙ)`  (if n ≤ k)
              - return `some $ mkOptionExpr lsort u none`      (otherwise)
          - When `slist := e₀ :: e₁ :: ... :: eₖ :: x`
              - return `some $ mkOptionExpr lsort u (some eₙ)` (if n ≤ k)
              - return `some (List.get?Internal x (n - k))`   (otherwise)
          - Otherwise:
              - return `none`
      - Otherwise
          - return `none`
-/
@[always_inline, inline]
def isListNCtor? (f lsort slist idx : Expr) : TranslateEnvT (Option Expr) :=
 let rec visit (e : Expr) (n : Nat) (start : Nat) : TranslateEnvT (Option Expr) := do
  match e with
  | Expr.app (Expr.const ``List.nil u) lsort => mkOptionExpr lsort u none
  | Expr.app (Expr.app (Expr.app (Expr.const ``List.cons u) lsort) a) as =>
      if n == 0 then mkOptionExpr lsort u (some a)
      else visit as (n - 1) start
  | _ => if n == start then return none else mkApp3Expr f lsort e (← mkNatLitExpr n)
 match isNatValue? idx with
 | some n => visit slist n n
 | none => return none

/-- Given `f := Expr.const ``List.get?Internal`, `lsort` the corresponding list sort, `slist` the list argument and
    `idx` the index argument, perform the following:
       - When `slist := []`
           - return `some $ mkOptionExpr lsort u none`
       - When `sList := [e₀, e₁, ..., eₖ]`
         - return `some $ sif 0 = idx then some e₀ else sif 1 = idx some e₁ ... else none`
       - When `sList := e₀ :: e₁ :: ... :: eₖ :: x`
         - return `some $ sif 0 = idx then some e₀ else sif 1 = idx some e₁ ... else List.get?Internal x (idx - k)`
      - Otherwise
          - return `none`
-/
@[always_inline, inline]
def isUnfoldListIdx? (f lsort slist idx : Expr) : TranslateEnvT (Option Expr) :=
 let rec visit (e : Expr) (n : Nat) (k : Expr → TranslateEnvT Expr) : TranslateEnvT (Option Expr) := do
  match e with
  | Expr.app (Expr.const ``List.nil u) lsort => k (← mkOptionExpr lsort u none)
  | Expr.app (Expr.app (Expr.app (Expr.const ``List.cons u) lsort) a) as =>
      let iteCond ← mkNatEqExpr (← mkNatLitExpr n) idx
      let notCond ← mkAppExpr (← mkPropNotOp) iteCond
      let hName ← Term.mkFreshBinderName
      let thenExpr ← mkLambdaExpr hName BinderInfo.default iteCond (← mkOptionExpr lsort u (some a))
      visit as (n + 1) fun e' => do
          let elseExpr ← mkLambdaExpr hName BinderInfo.default notCond e'
          k (← mkApp4Expr (← mkBlasterDIteOp) (← mkOptionType lsort u) iteCond thenExpr elseExpr)
  | _ => if n == 0 then return none
         else
          setRestart
          k (← mkApp3Expr f lsort e (← mkApp2Expr (← mkNatSubOp) idx (← mkNatLitExpr n)))
 visit slist 0 (λ e => return e)

/-- Apply the following simplification/normalization rules on `List.get?Internal` :
     - List.get?Internal [] i ===> none
     - List.get?Internal [e₀, e₁, ..., eₖ] n ===> some eₙ (if n := N ∧ N ≤ k)
     - List.get?Internal [e₀, e₁, ..., eₖ] n ===> none (if n := N ∧ N > k)
     - List.get?Internal (e₀ :: e₁ :: ... :: eₖ :: x) n ===> some eₙ (if n := N ∧ N ≤ k)
     - List.get?Internal (e₀ :: e₁ :: ... :: eₖ :: x) n ===> List.get?Internal x (n - k) (if n := N ∧ N > k)
     - List.get?Internal [e₀ :: e₁ :: ... :: eₙ] i ===>
          sif 0 = i then some e₀ else sif 1 = i some e₁ ... else none
     - List.get?Internal (e₀ :: e₁ :: ... :: eₙ :: x) i ===>
          sif 0 = i then some e₀ else sif 1 = i some e₁ ... else List.get?Internal x (i - n)

   Assume that f = Expr.const ``List.get?Internal.
   Optimizations are not applied when args.size ≠ 3 (e.g., List.get as HOF)
-/
def optimizeListGet (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 3 then return ← mkAppNExpr f args
 -- args[0] list sort
 -- args[1] list argument
 -- args[2] index argument
 let op1 := args[0]!
 let op2 := args[1]!
 let op3 := args[2]!
 if let some u := isNilList? op2 then return (← mkOptionExpr op1 u none)
 if let some r ← isListNCtor? f op1 op2 op3 then return r
 if let some r ← isUnfoldListIdx? f op1 op2 op3 then return r
 mkApp3Expr f op1 op2 op3

/-- Given `f := Expr.const ``List.append`, `lsort` the corresponding list sort, `list1` the first list argument, and
    and `list2` the second list argument, perform the following:
       - When `list1 := [e₁, e₂, ..., eₙ]`
              - return `some (e₁ :: ... :: eₙ :: list2)
       - When `list1 := (e₁ :: e₂ :: ... :: eₙ :: x)
              - return `some (e₁ :: e₂ :: ... :: eₙ :: List.append x list2)`
       - Otherwise
          - return `none`
-/
@[always_inline, inline]
def cstListAppend? (f lsort list1 list2 : Expr) : TranslateEnvT (Option Expr) := do
 let rec visit (e : Expr) (k : Expr → TranslateEnvT Expr) : TranslateEnvT (Option Expr) := do
  match e with
  | Expr.app (Expr.const ``List.nil _) _ => k list2
  | Expr.app (Expr.app (Expr.app (Expr.const ``List.cons u) lsort) a) as =>
      visit as fun e' => do
         k (← mkApp2Expr (← mkListCons u lsort) a e')
  | _ => if exprEq e list1 then return none
         else k (← mkApp3Expr f lsort e list2)
 visit list1 (λ e => return e)

/-- Apply the following simplification/normalization rules on `List.append` :
     - List.append [] x ===> x
     - List.append x [] ===> x
     - List.append [e₁, e₂, ..., eₙ] x ===> `(e₁ :: ... :: eₙ :: x)`
     - List.append (e₁ :: e₂ :: ... :: eₙ :: l1) l2 ===> `(e₁ :: ... :: eₙ :: List.append l1 l2)`

   Assume that f = Expr.const ``List.append.
   Optimization are not applied when args.size ≠ 3 (e.g., List.append as HOF)
-/
def optimizeListAppend (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 3 then return ← mkAppNExpr f args
 -- args[0] list sort
 -- args[1] list argument
 -- args[2] list argument
 let op1 := args[0]!
 let op2 := args[1]!
 let op3 := args[2]!
 if isNilList op2 then return op3
 if isNilList op3 then return op2
 if let some r ← cstListAppend? f op1 op2 op3 then return r
 mkApp3Expr f op1 op2 op3


/-- Given `f := Expr.const ``List.reverseAux`, `lsort` the corresponding list sort, `slist` the first list argument
    and `rlist` the second list argument, perform the following:
      - When `slist := []`
          - return `some rlist`
      - When `slist := [e₀, e₁, ..., eₖ]`
          - return `some $ eₖ :: ... :: e₁ :: e₀ :: l`
      - When `slist := (e₀ :: e₁ :: ... :: eₖ :: x)`
          - return `some $ List.reverseAux x (eₖ :: ... :: e₁ :: e₀ :: l)`
-/
@[always_inline, inline]
def cstListReverse? (f lsort slist alist : Expr): TranslateEnvT (Option Expr) := do
 let rec visit (rlist alist : Expr) : TranslateEnvT (Option Expr) := do
  match rlist with
  | Expr.app (Expr.const ``List.nil _) _ => return alist
  | Expr.app (Expr.app (Expr.app (Expr.const ``List.cons u) lsort) a) as =>
       visit as (← mkApp2Expr (← mkListCons u lsort) a alist)
  | _ => if exprEq rlist slist then return none
         else mkApp3Expr f lsort rlist alist
 visit slist alist

/-- Apply the following simplification/normalization rules on `List.reverseAux` :
     - List.reverseAux [] l ===> l
     - List.reverseAux [e₀, e₁, ..., eₖ] l ==> eₖ :: ... :: e₁ :: e₀ :: l
     - List.reverseAux (e₀ :: e₁ :: ... :: eₖ :: x) l ==> List.reverseAux x (eₖ :: ... :: e₁ :: e₀ :: l)

   Assume that f = Expr.const ``List.reverseAux.
   Optimization are not applied when args.size ≠ 3 (e.g., List.reverse as HOF)
-/
def optimizeListReverseAux (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 3 then return ← mkAppNExpr f args
 -- args[0] list sort
 -- args[1] list argument
 -- args[2] list argument
 let op1 := args[0]!
 let op2 := args[1]!
 let op3 := args[2]!
 if isNilList op2 then return op3
 if let some r ← cstListReverse? f op1 op2 op3 then return r
 mkApp3Expr f op1 op2 op3


/-- Given `f := Expr.const ``List.length`, `lsort` the corresponding list sort, `slist` the list argument,
    perform the following:
      - When `slist := []`
          - return `some 0`
      - When `slist := [e₁, e₁, ..., eₙ]`
          - return `some n`
      - When `slist := (e₁ :: e₁ :: ... :: eₙ :: x)`
          - return `some $ n + List.length x`
-/
@[always_inline, inline]
def cstListLength? (f lsort slist : Expr): TranslateEnvT (Option Expr) := do
 let rec visit (rlist : Expr) (nbElem : Nat) : TranslateEnvT (Option Expr) := do
  match rlist with
  | Expr.app (Expr.const ``List.nil _) _ => mkNatLitExpr nbElem
  | Expr.app (Expr.app (Expr.app (Expr.const ``List.cons _) _) _a) as =>
       visit as (nbElem + 1)
  | _ => if nbElem == 0 then return none
         else mkApp2Expr (← mkNatAddOp) (← mkNatLitExpr nbElem) (← mkApp2Expr f lsort rlist)
 visit slist 0

/-- Apply the following simplification/normalization rules on `List.length` :
     - List.length [] ===> 0
     - List.length [e₁, e₂, ..., eₙ] ===> n
     - List.length (e₁ :: e₂ :: ... :: eₙ :: x) ===> n + List.length x
   Assume that f = Expr.const ``List.length.
   Optimization are not applied when args.size ≠ 2 (e.g., List.length as HOF)
-/
def optimizeListLength (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then return ← mkAppNExpr f args
 -- args[0] list sort
 -- args[1] list argument
 let op1 := args[0]!
 let op2 := args[1]!
 if isNilList op2 then return ← mkNatLitExpr 0
 if let some r ← cstListLength? f op1 op2 then return r
 mkApp2Expr f op1 op2

/-- Given `f := Expr.const ``List.take`, `lsort` the corresponding list sort, `idx` the index argument
    and `slist` the list argument, perform the following:
      - When some n := isNatValue? idx
          - When `slist := [e₁, e₂, ..., eₖ]`
              - return `some [e₁, e₂, ..., eₙ] (if n ≤ k)
              - return `some [e₁, e₂, ..., eₖ] (otherwise)
          - When `slist := e₁ :: e₂ :: ... :: eₖ :: x`
              - return `some `some [e₁, e₂, ..., eₙ]                       (if n ≤ k)
              - return `some e₁ :: e₂ :: ... :: eₖ :: List.take (n - k) x` (otherwise)
          - Otherwise:
              - return `none`
      - Otherwise
          - return `none`
-/
@[always_inline, inline]
def cstListTake? (f lsort idx slist : Expr) (u : List Level) : TranslateEnvT (Option Expr) := do
 let rec visit (e : Expr) (n : Nat) (start : Nat) (k : Expr → TranslateEnvT Expr) : TranslateEnvT (Option Expr) := do
  match e with
  | Expr.app (Expr.const ``List.nil _) _ => k e
  | Expr.app (Expr.app (Expr.app (Expr.const ``List.cons u) lsort) a) as =>
      if n == 0 then k (← mkListNil u lsort)
      else visit as (n - 1) start fun e' => do
            k (← mkApp2Expr (← mkListCons u lsort) a e')
  | _ => if n == start then return none
         else if n == 0 then k (← mkListNil u lsort)
         else k (← mkApp3Expr f lsort (← mkNatLitExpr n) e)
 match isNatValue? idx with
 | some n => visit slist n n (λ e => return e)
 | none => return none

/-- Apply the following simplification/normalization rules on `List.take` :
     - List.take i [] ===> []
     - List.take 0 x ===> []
     - List.take n [e₁, e₂, ..., eₖ] ===> [e₁, e₂, ..., eₙ] (if n := N ∧ N ≤ k)
     - List.take n [e₁, e₂, ..., eₖ] ===> [e₁, e₁, ..., eₖ] (if n := N ∧ N > k)
     - List.take n (e₁ :: e₂ :: ... :: eₖ :: x) ===> [e₁, e₂, ..., eₙ] (if n := N ∧ N ≤ k)
     - List.take n (e₁ :: e₂ :: ... :: eₖ :: x) ===> e₁ :: e₂ :: ... :: eₖ :: (List.take (n - k) x) (if n := N ∧ N > k)
   Assume that f = Expr.const ``List.take.
   Optimization are not applied when args.size ≠ 3 (e.g., List.take as HOF)
-/
def optimizeListTake (f : Expr) (u : List Level) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 3 then return ← mkAppNExpr f args
 -- args[0] list sort
 -- args[1] index argument
 -- args[2] list argument
 let op1 := args[0]!
 let op2 := args[1]!
 let op3 := args[2]!
 if isNilList op3 then return op3
 if isZeroNat op2 then return ← mkListNil u op1
 if let some r ← cstListTake? f op1 op2 op3 u then return r
 mkApp3Expr f op1 op2 op3


/-- Given `f := Expr.const ``List.drop`, `lsort` the corresponding list sort, `idx` the index argument
    and `slist` the list argument, perform the following:
      - When some n := isNatValue? idx
          - When `slist := [e₁, e₂, ..., eₖ]`
              - return `some [eₙ₊₁, .. eₖ] (if n ≤ k)
              - return `some [] (otherwise)
          - When `slist := e₁ :: e₂ :: ... :: eₖ :: x`
              - return `some `some [eₙ₊₁, .. eₖ]  (if n ≤ k)
              - return `some List.drop (n - k) x`(otherwise)
          - Otherwise:
              - return `none`
      - Otherwise
          - return `none`
-/
@[always_inline, inline]
def cstListDrop? (f lsort idx slist : Expr) : TranslateEnvT (Option Expr) := do
 let rec visit (e : Expr) (n : Nat) (start : Nat) : TranslateEnvT (Option Expr) := do
  match e with
  | Expr.app (Expr.const ``List.nil _) _ => return e
  | Expr.app (Expr.app (Expr.app (Expr.const ``List.cons _) _) _a) as =>
      if n == 0 then return e
      else visit as (n - 1) start
  | _ => if n == start then return none
         else if n == 0 then return e
         else mkApp3Expr f lsort (← mkNatLitExpr n) e
 match isNatValue? idx with
 | some n => visit slist n n
 | none => return none

/-- Apply the following simplification/normalization rules on `List.drop` :
     - List.drop i [] ===> []
     - List drop 0 x ===> x
     - List.drop n [e₁, e₂, ..., eₖ] ===> [eₙ₊₁, .. eₖ] (if n := N ∧ N ≤ k)
     - List.drop n [e₁, e₂, ..., eₖ] ===> [] (if n := N ∧ N > k)
     - List.drop n (e₁ :: e₂ :: ... :: eₖ :: x) ===> [eₙ₊₁, .. eₖ] (if n := N ∧ N ≤ k)
     - List.drop n (e₁ :: e₂ :: ... :: eₖ :: x) ===> List.drop (n - k) x (if n := N ∧ N > k)
   Assume that f = Expr.const ``List.drop.
   Optimization are not applied when args.size ≠ 3 (e.g., List.drop as HOF)
-/
def optimizeListDrop (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 3 then return ← mkAppNExpr f args
 -- args[0] list sort
 -- args[1] index argument
 -- args[2] list argument
 let op1 := args[0]!
 let op2 := args[1]!
 let op3 := args[2]!
 if isNilList op3 then return op3
 if isZeroNat op2 then return op3
 if let some r ← cstListDrop? f op1 op2 op3 then return r
 mkApp3Expr f op1 op2 op3



/-- Given `f := Expr.const ``List.replicate`, `lsort` the corresponding list sort, `n` the number of copies parameter and
    `a` the element to replicate, perform the following:
      - When n := N
          - return `some [a₁,..., aₙ]`
      - When n := N + e
          - return `some $ a₁ :: ... :: aₙ :: replicate e a`
      - Otherwise
          - return `none`
-/
@[always_inline, inline]
def cstListReplicate? (f lsort n a : Expr) (u : List Level) : TranslateEnvT (Option Expr) := do
 let rec visit (nb : Nat) (alist : Expr) : TranslateEnvT Expr := do
   if nb = 0 then return alist
   else visit (nb - 1) (← mkApp2Expr (← mkListCons u lsort) a alist)
 match n with
 | Expr.lit (Literal.natVal nb) => visit nb (← mkListNil u lsort)
 | Expr.app (Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal nb))) e =>
      visit nb (← mkApp3Expr f lsort e a)
 | _ => return none

/-- Apply the following simplification/normalization rules on `List.replicate` :
     - List.replicate 0 a ===> []
     - List.replicate n a ===> [a₁,..., aₙ]` (if n := N)
     - List.replicate (n + i) a ===> a₁ :: ... :: aₙ :: replicate n a (if n := N)

   Assume that f = Expr.const ``List.replicate.
   Optimizations are not applied when args.size ≠ 3 (e.g., List.replicate as HOF)
-/
def optimizeListReplicate (f : Expr) (u : List Level) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 3 then return ← mkAppNExpr f args
 -- args[0] list sort
 -- args[1] Number of copies
 -- args[2] element
 let op1 := args[0]!
 let op2 := args[1]!
 let op3 := args[2]!
 if isZeroNat op2 then return ← mkListNil u op1
 if let some r ← cstListReplicate? f op1 op2 op3 u then return r
 mkApp3Expr f op1 op2 op3


/-- Apply simplification/normalization rules on `List` operators. -/
def optimizeList? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const n u := f | return none
  match n with
  | ``List.append => optimizeListAppend f args
  | ``List.get?Internal => optimizeListGet f args
  | ``List.reverseAux => optimizeListReverseAux f args
  | ``List.length => optimizeListLength f args
  | ``List.take => optimizeListTake f u args
  | ``List.drop => optimizeListDrop f args
  | ``List.replicate => optimizeListReplicate f u args
  | _ => return none

end Blaster.Optimize
