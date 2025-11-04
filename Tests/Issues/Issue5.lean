import Lean
import PlutusTx.Builtins.Tests
import Solver.Command.Syntax

namespace Tests.Issue5

open PlutusTx.Builtins.Internal
  ( appendByteString)

open PlutusTx.Builtins.Internal.BuiltinsLemmas
  (
    exampleByteString1
    exampleByteString2
    exampleByteString6
  )

-- Issue: cannot reduce to true
-- Diagnosis : need to extend  reduceApp rule to also consider higher order functions
--             and propositions passed as arguments

#solve (only-optimize: 1) [ (appendByteString exampleByteString1 exampleByteString2 == exampleByteString6) = true ]

#solve (only-optimize: 1) [List.foldr (λ x acc => x + acc) 0 [(1 : Nat), 2, 3, 4, 5] = 15]

#solve (only-optimize: 1)
 [ ∀ (a b c d e : Nat), List.foldr (λ x acc => x + acc) 0 [a, b, c, d, e] = a + (b + (c + (d + e))) ]

-- NOTE: add option (only-optimize: 1) when advanced optimizations normalizing ordering
-- on multiple add are introduced.
#solve [ ∀ (a b c d e : Nat), List.foldr (λ x acc => x + acc) 0 [a, b, c, d, e] = a + b + c + d + e ]

end Tests.Issue5
