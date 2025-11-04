import Lean
import PlutusTx.Builtins.Tests
import Solver.Command.Syntax

namespace Tests.Issue3

open PlutusTx.Builtins.Internal.BuiltinsLemmas
  ( exampleDataConstr1
    exampleDataMap1
    exampleDataMap2
  )

-- Issue: index out of bound
-- Diagnosis : paramInfo.size may not always be greater than or equal to the number of effective arguments.
--             This is so especially when a polymorphic function is applied to a function, e.g.,
--             useToOpaque .BuiltinByteString x, paramInfo.size for useToOpaque is 2 while it is being
--             applied to three arguments. One for the implicit parameter, one for  .BuiltinByteString
--             and one for `x`. Here, x is passed as effective argument to the result
--             produced by useToOpaque when applied to .BuiltinByteString.

#solve [ (exampleDataMap1 != exampleDataMap2) = true]

#solve [ true = (exampleDataMap1 != exampleDataConstr1)]

#solve [(exampleDataMap1 == exampleDataMap1) = true]

#solve [exampleDataMap1 = exampleDataMap1]

end Tests.Issue3
