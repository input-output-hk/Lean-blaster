import Lean
import Blaster.Optimize.Basic

open Lean Elab Command

namespace ConsumerDrivenMatchBehavior

set_option maxHeartbeats 0

inductive Data where
  | leaf : Nat → Data
  | pair : Data → Data → Data

def encode : Option Nat → Data
  | none => .leaf 0
  | some n => .leaf (n + 1)

def pack : List (Option Nat) → Data
  | [] => .leaf 99
  | x :: xs => .pair (encode x) (pack xs)

def firstLeaf : Data → Nat
  | .pair (.leaf n) _ => n
  | _ => 999

def first : Data → Data
  | .pair x _ => x
  | x => x

run_cmd liftTermElabM do
  let stx ← `(fun a b c d : Option Nat => firstLeaf (pack [a, b, c, d]))
  let expression ← Elab.Term.elabTermAndSynthesize stx none
  let (optimized, env) ← Blaster.Optimize.command { preserveConstructorChoices := true } expression
  IO.println s!"firstLeaf contexts={env.optEnv.options.nextCtxId}"
  IO.println s!"firstLeaf result:\n{← Lean.Meta.ppExpr optimized}"
  let firstStx ← `(fun a b c d : Option Nat => first (pack [a, b, c, d]))
  let firstExpr ← Elab.Term.elabTermAndSynthesize firstStx none
  let (firstOpt, firstEnv) ← Blaster.Optimize.command { preserveConstructorChoices := true } firstExpr
  IO.println s!"first contexts={firstEnv.optEnv.options.nextCtxId}"
  IO.println s!"first result:\n{← Lean.Meta.ppExpr firstOpt}"

end ConsumerDrivenMatchBehavior
