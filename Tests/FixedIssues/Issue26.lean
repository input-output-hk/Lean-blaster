import Lean
import Blaster

open Lean Meta
namespace Tests.Issue26

-- Issue 1: error: typeclass instance problem is stuck, it is often due to metavariables BEq ?m.1
--           when #blaster command is called
-- Diagnosis: We need to postpone instance synthesize when parsed expression has metavariables.

-- Issue 2:  Unexpected smt error: (error "line 21 column 41: Parsing function declaration.
--           Expecting sort list '(': unknown sort '@@Type'")
-- Diagnosis: We need to always check if @@Type has been declared. Indeed,
--            polymorphic type may also be declared globally.

-- Issue 3:  isGenericParam: unexpected meta variable ...
-- Diagnosis: There is a need to instantiate meta variables after type inference. Indeed, in some cases,
--            the induction tactic implicitly declares free variables with meta variables still
--            present in their types.

set_option warn.sorry false

inductive Path where
 | Here : Path
 | There : Path -> Path

def check_valid_path {α : Type}[BEq α](v : α)(p : Path)(ls : List α)
 : Bool
 := match p , ls with
    | .Here , .cons l _ls     => v == l
    | .There rs , .cons _ ls  => check_valid_path v rs ls
    | _ , _ => false

theorem validProof {α : Type}[BEq α](v : α)(p : Path)(ls : List α)
 : check_valid_path v p ls == true -> List.elem v ls := by
   induction ls generalizing p <;> blaster

-- remove solver option once induction proof is supported
#blaster (timeout: 5) (solve-result: 2) [validProof]

theorem getElem?_zipWith {f : α → β → γ} {i : Nat} :
    (List.zipWith f as bs)[i]? = match as[i]?, bs[i]? with
      | some a, some b => some (f a b) | _, _ => none := by
  induction as generalizing bs i <;> blaster

-- remove solver option once induction proof is supported
#blaster (timeout: 5) (solve-result: 2) [getElem?_zipWith]

theorem getElem?_zipWith' {f : α → β → γ} {i : Nat} :
    (List.zipWith f l₁ l₂)[i]? = (l₁[i]?.map f).bind fun g => l₂[i]?.map g := by
  induction l₁ generalizing l₂ i <;> blaster

-- remove solver option once induction proof is supported
#blaster (timeout: 5) (solve-result: 2) [getElem?_zipWith']

theorem zipWith_map_left {l₁ : List α} {l₂ : List β} {f : α → α'} {g : α' → β → γ} :
    List.zipWith g (l₁.map f) l₂ = List.zipWith (fun a b => g (f a) b) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> blaster

-- remove solver option once induction proof is supported
#blaster (timeout: 5) (solve-result: 2) [zipWith_map_left]

theorem zipWith_foldr_eq_zip_foldr {f : α → β → γ} {i : δ} {g : γ → δ → δ} :
    (List.zipWith f l₁ l₂).foldr g i = (List.zip l₁ l₂).foldr (fun p r => g (f p.1 p.2) r) i := by
  induction l₁ generalizing l₂ <;> blaster

-- remove solver option once induction proof is supported
#blaster (timeout: 5) (solve-result: 2) [zipWith_foldr_eq_zip_foldr]

end Tests.Issue26
