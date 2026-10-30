import Lean

/-! Structured counterexamples are diagnostic data, not proofs. Reconstructed
values are type checked; replay by the caller is still required. -/
namespace Blaster.Counterexample

open Lean Meta

inductive Value where
  | integer (value : Int)
  | natural (value : Nat)
  | boolean (value : Bool)
  | string (value : String)
  | bytes (hex : String)
  | unit
  /-- A domain codec supplies a lossless representation and a source type hint. -/
  | encoded (typeName encoding : String) (value : Value)
  | unavailable (reason : String)
  | list (values : List Value)
  | constructor (typeName name : String) (fields : List (String × Value))
  deriving Repr, Inhabited

/-- Export a reconstructed value without tying the solver to a source language. -/
class ToCEX (α : Type u) where
  toCEX : α → Value

export ToCEX (toCEX)

instance : ToCEX Int := ⟨Value.integer⟩
instance : ToCEX Nat := ⟨Value.natural⟩
instance : ToCEX Bool := ⟨Value.boolean⟩
instance : ToCEX String := ⟨Value.string⟩
instance : ToCEX Unit := ⟨fun _ => .unit⟩
instance [ToCEX α] : ToCEX (List α) := ⟨fun xs => .list (xs.map toCEX)⟩
instance [ToCEX α] : ToCEX (Option α) := ⟨fun
  | none => .constructor "Option" "Option.none" []
  | some x => .constructor "Option" "Option.some" [("value", toCEX x)]⟩
instance [ToCEX α] [ToCEX β] : ToCEX (α × β) := ⟨fun x =>
  .constructor "Prod" "Prod.mk" [("fst", toCEX x.1), ("snd", toCEX x.2)]⟩

partial def Value.toJson : Value → Json
  | .integer n => Json.mkObj [("kind", Lean.toJson "integer"), ("value", Lean.toJson (toString n))]
  | .natural n => Json.mkObj [("kind", Lean.toJson "natural"), ("value", Lean.toJson (toString n))]
  | .boolean b => Json.mkObj [("kind", Lean.toJson "boolean"), ("value", Lean.toJson b)]
  | .string s => Json.mkObj [("kind", Lean.toJson "string"), ("value", Lean.toJson s)]
  | .bytes h => Json.mkObj [("kind", Lean.toJson "bytes"), ("hex", Lean.toJson h)]
  | .unit => Json.mkObj [("kind", Lean.toJson "unit")]
  | .encoded t e v => Json.mkObj [("kind", Lean.toJson "encoded"),
      ("type", Lean.toJson t), ("encoding", Lean.toJson e), ("value", v.toJson)]
  | .unavailable reason => Json.mkObj [("kind", Lean.toJson "unavailable"), ("reason", Lean.toJson reason)]
  | .list xs => Json.mkObj [("kind", Lean.toJson "list"), ("values", Lean.toJson (xs.map Value.toJson))]
  | .constructor t n fs => Json.mkObj [("kind", Lean.toJson "constructor"), ("type", Lean.toJson t),
      ("constructor", Lean.toJson n), ("fields", Lean.toJson (fs.map fun (n, v) =>
        Json.mkObj [("name", Lean.toJson n), ("value", v.toJson)]))]

/-- An unsupported leaf makes the export incomplete, including inside containers. -/
partial def Value.error? : Value → Option String
  | .unavailable reason => some reason
  | .encoded _ _ v => v.error?
  | .list vs => vs.findSome? Value.error?
  | .constructor _ _ fs => fs.findSome? (fun (_, v) => v.error?)
  | _ => none

/-- Identity is independent of the display name; identical names can be shadowed.
    Expressions are internal only and are never deserialized from a report. -/
structure Binding where
  id : Name
  name : Name
  type : Expr
  raw : String
  value : Option Expr := none
  tree : Option Value := none
  error : Option String := none
  deriving Repr

structure Model where
  bindings : Array Binding := #[]
  /-- Original solver text for compatibility and unsupported models. -/
  messages : List String := []
  deriving Repr

/-- `evalExpr` is used only for diagnostic export, never to establish a theorem.
    A missing instance falls back to the structural tree built by the decoder. -/
unsafe def Binding.toJson (b : Binding) : MetaM Json := do
  let mut tree := b.tree
  let mut exportError := b.error
  if let some value := b.value then
    try
      let cls ← mkAppM ``ToCEX #[b.type]
      if let .some inst ← trySynthInstance cls then
        let exported ← mkAppOptM ``ToCEX.toCEX #[some b.type, some inst, some value]
        tree := some (← evalExpr Value (mkConst ``Value) exported)
    catch e =>
      if e.isInterrupt then throw e
      exportError := some s!"ToCEX export failed: {← e.toMessageData.toString}"
  if let some reason := tree.bind Value.error? then exportError := some reason
  if tree.isNone && exportError.isNone then
    exportError := some "No ToCEX instance or structural representation is available"
  return Json.mkObj [("id", Lean.toJson b.id.toString), ("name", Lean.toJson b.name.toString),
    ("leanType", Lean.toJson (← ppExpr b.type).pretty), ("raw", Lean.toJson b.raw.trim),
    ("value", tree.map Value.toJson |>.getD Json.null),
    ("error", Lean.toJson exportError)]

unsafe def Model.toJson (m : Model) : MetaM Json := do
  return Json.mkObj [("format", Lean.toJson "blaster-counterexample-v1"),
    ("bindings", Lean.toJson (← m.bindings.mapM Binding.toJson)), ("raw", Lean.toJson m.messages)]

end Blaster.Counterexample
