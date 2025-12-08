import Lean
import Blaster

namespace Tests.Issue3

-- Issue: index out of bound
-- Diagnosis : paramInfo.size may not always be greater than or equal to the number of effective arguments.
--             This is so especially when a polymorphic function is applied to a function, e.g.,
--             useToOpaque .BuiltinByteString x, paramInfo.size for useToOpaque is 2 while it is being
--             applied to three arguments. One for the implicit parameter, one for  .BuiltinByteString
--             and one for `x`. Here, x is passed as effective argument to the result
--             produced by useToOpaque when applied to .BuiltinByteString.

def useToOpaque : α -> α
  | x => x

inductive BuiltinByteString where
  | BuiltinByteString : ByteArray → BuiltinByteString

/-- BEq instance for BuiltinByteString -/
instance BEqBuiltinByteString : BEq BuiltinByteString where
  beq
  | .BuiltinByteString bs1, .BuiltinByteString bs2 => bs1 == bs2

def toBuiltin : ByteArray → BuiltinByteString := useToOpaque .BuiltinByteString

def mkBuiltinList (xs : List ByteArray) : List BuiltinByteString :=
  xs.map (λ bs => toBuiltin bs)


def exampleDataList1 := mkBuiltinList [ "Token1".toUTF8, "Token2".toUTF8, "Token4".toUTF8 ]
def exampleDataList2 := mkBuiltinList [ "Token2".toUTF8, "Token3".toUTF8, "Token4".toUTF8 ]

#blaster [ (exampleDataList1 != exampleDataList2) = true]

#blaster [ (exampleDataList1 == exampleDataList1) = true]

#blaster [exampleDataList1 = exampleDataList1]

end Tests.Issue3
