import Lean
import Blaster.Optimize.Basic

open Lean Elab Command

namespace ConsumerDrivenMatchBench

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

run_cmd liftTermElabM do
  let inputs := #[
    ("2", (← `(fun a b : Option Nat => pack [a, b]))),
    ("4", (← `(fun a b c d : Option Nat => pack [a, b, c, d]))),
    ("6", (← `(fun a b c d e f : Option Nat => pack [a, b, c, d, e, f]))),
    ("8", (← `(fun a b c d e f g h : Option Nat => pack [a, b, c, d, e, f, g, h]))),
    ("10", (← `(fun a b c d e f g h i j : Option Nat => pack [a, b, c, d, e, f, g, h, i, j])))
  ]
  for (n, stx) in inputs do
    let expression ← Elab.Term.elabTermAndSynthesize stx none
    for preserve in #[false, true] do
      let start ← IO.monoNanosNow
      let (_, env) ← Blaster.Optimize.command { preserveConstructorChoices := preserve } expression
      let elapsedNs := (← IO.monoNanosNow) - start
      let mode := if preserve then "preserve-constructor-choices" else "beta-lambda"
      IO.println s!"inputs={n} mode={mode} contexts={env.optEnv.options.nextCtxId} hashcons={env.optEnv.hashConsCache.size} elapsed_ns={elapsedNs}"

end ConsumerDrivenMatchBench
