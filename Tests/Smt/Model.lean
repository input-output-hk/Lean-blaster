import Blaster.Smt.Model

namespace Tests.Smt.Model

open Blaster.Smt.Model

#guard integerBinding "fee: (- 98765432101234567890)" == some ("fee", -98765432101234567890)
#guard (integerBinding "fee: (- nope)").isNone
#guard (integerBinding "fee: 42 trailing").isNone
#guard (bindingValue "missing separator").isNone
#guard parse "  (Pair 1 true)  " == some (.list [.atom "Pair", .atom "1", .atom "true"])
#guard parse "\"a: \"\"q\"\"\\u{0}\\u{ff}\"" == some (.text ("a: \"q\"" ++ String.singleton (Char.ofNat 0) ++ "ÿ"))
#guard (parse "(unterminated").isNone
#guard (parse "\"unterminated").isNone
#guard (parse "1 2").isNone

-- Simultaneous bindings use the outer scope; nested lets may shadow it.
#guard bindingValue "n: (let ((x 7)) (let ((x 8) (y x)) (Pair x y)))" ==
  some ("n", .list [.atom "Pair", .atom "8", .atom "7"])
#guard (bindingValue "n: (let ((x 1) (x 2)) x)").isNone
#guard (bindingValue "n: (let ((x)) x)").isNone
#guard integerBinding "n: (let ((x (- 42))) x)" == some ("n", -42)

#guard (Blaster.Smt.Model.boolBinding "flag: true") == some ("flag", true)
#guard (Blaster.Smt.Model.boolBinding "flag: false") == some ("flag", false)
#guard (Blaster.Smt.Model.boolBinding "flag: 1").isNone
#guard (Blaster.Smt.Model.boolBinding "flag: true trailing").isNone

end Tests.Smt.Model
