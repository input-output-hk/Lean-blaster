import Blaster.CEX.Decode
import Blaster.Smt.FFI.Solver
import Blaster.Smt.FFI.Terms

namespace Blaster.Smt.FFI

/-- Inspect an evaluated model AST without parsing SMT-LIB text. The raw form
    is retained when Z3 returns an array, uninterpreted value, or other form
    that cannot be reconstructed as a Lean constructor application. -/
partial def Context.readModelValue (ctx : Context) (ast : Ast)
    (fuel : Nat := 256) : IO Blaster.CEX.Value := do
  if fuel == 0 then return .raw (← ctx.astToString ast)
  if ← ctx.astIsString ast then
    let chars ← ctx.astGetStringCodepoints ast
    return .str (String.mk (chars.toList.map (Char.ofNat ∘ UInt32.toNat)))
  if ← ctx.astIsNumeral ast then
    return .numeral (← ctx.astGetNumeral ast)
  if ← ctx.astIsApp ast then
    let name ← ctx.astGetDeclName ast
    let args ← ctx.astGetArgs ast
    if name == "true" && args.isEmpty then return .bool true
    if name == "false" && args.isEmpty then return .bool false
    -- Z3 can represent a negative numeral as a unary application.
    if name == "-" && args.size == 1 then
      if let some arg := args[0]? then
        match ← ctx.readModelValue arg (fuel - 1) with
        | .numeral n => return .numeral s!"-{n}"
        | _ => pure ()
    let fields ← args.mapM (fun arg => ctx.readModelValue arg (fuel - 1))
    return .app name fields
  return .raw (← ctx.astToString ast)

end Blaster.Smt.FFI
