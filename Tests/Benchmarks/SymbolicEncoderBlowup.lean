import Lean
import Blaster.Optimize.Basic

open Lean Elab Command

namespace SymbolicEncoderBlowup

set_option maxHeartbeats 0
set_option trace.Optimize.context true

inductive Data where
  | leaf : Nat → Data
  | pair : Data → Data → Data

def encode : Option Nat → Data
  | none => .leaf 0
  | some n => .leaf (n + 1)

def pack : List (Option Nat) → Data
  | [] => .leaf 99
  | x :: xs => .pair (encode x) (pack xs)

def factored2 (a b : Option Nat) : Data :=
  .pair
    (match a with
     | none => .leaf 0
     | some n => .leaf (n + 1))
    (.pair
      (match b with
       | none => .leaf 0
       | some n => .leaf (n + 1))
      (.leaf 99))

def distributed2 (a b : Option Nat) : Data :=
  match a with
  | none =>
      match b with
      | none => .pair (.leaf 0) (.pair (.leaf 0) (.leaf 99))
      | some n => .pair (.leaf 0) (.pair (.leaf (n + 1)) (.leaf 99))
  | some n =>
      match b with
      | none => .pair (.leaf (n + 1)) (.pair (.leaf 0) (.leaf 99))
      | some m => .pair (.leaf (n + 1)) (.pair (.leaf (m + 1)) (.leaf 99))

theorem factored_eq_distributed (a b : Option Nat) :
    factored2 a b = distributed2 a b := by
  cases a <;> cases b <;> rfl

theorem pack_eq_factored (a b : Option Nat) :
    pack [a, b] = factored2 a b := by
  cases a <;> cases b <;> rfl

-- Each input is independent. Eagerly opening `encode` combines their cases.
run_cmd liftTermElabM do
  let examples := #[
    ("2", (← `(fun a b : Option Nat => pack [a, b]))),
    ("4", (← `(fun a b c d : Option Nat => pack [a, b, c, d])))
  ]
  for (n, stx) in examples do
    let expression ← Elab.Term.elabTermAndSynthesize stx none
    trace[Optimize.context] "--- {n} independent inputs ---"
    let (optimized, env) ← Blaster.Optimize.command default expression
    IO.println s!"independent inputs={n}, contexts={env.optEnv.options.nextCtxId}"
    IO.println s!"optimized expression ({n} inputs):\n{← Lean.Meta.ppExpr optimized}"

end SymbolicEncoderBlowup
