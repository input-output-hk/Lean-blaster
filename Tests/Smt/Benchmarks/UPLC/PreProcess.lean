import Lean
import Solver.Optimize.Basic
import Tests.Smt.Benchmarks.UPLC.CekMachine
open Lean Elab Command Term Meta Solver.Optimize

namespace UPLC.PreProcess
open UPLC.Uplc
open UPLC.CekMachine


/-! ## Definition of #preprocess_uplc that optimizes a uplc code according to the provided script budget.
    The #prep_uplc usage is as follows:
     #prep_uplc "<NEW-DEF>" <UPLC-PROGRAM> ([ <INPUT-TYPE₁>, ... <INPUT-TYPEₙ>])? (INPUT-CONVERTOR-FUN)? UNIT

    E.g.
     #prep_uplc "compiledProcessSCOrder" processSCOrder [ProcessSCInput] orderInputToParams 500
-/

syntax uplcInputs := ("[" ident,+ "]")?
syntax uplcMaxSteps := num
syntax (name := preprocess) "#prep_uplc" str ident uplcInputs (ident)? uplcMaxSteps : command

def parseInputs : TSyntax `uplcInputs → TermElabM (Array (Name × Expr))
  | `(uplcInputs| [ $[$ids:ident],* ]) => ids.mapIdxM validateInputType
  | `(uplcInputs| ) => return #[]
  | _ => throwUnsupportedSyntax

  where
    /- Resolve input type name and checks that it corresponds to an inductive datatype -/
    validateInputType (idx : Nat) (i : Syntax) : TermElabM (Name × Expr) := do
      let some t ← resolveId? i |
        throwErrorAt i m!"unknown constant '{.ofConstName i.getId}'"
      if !(← isInductiveTypeAux t.constName! []) then
        throwErrorAt i m!"unknown inductive datatype '{.ofConstName i.getId}'"
      return (Name.mkStr1 s!"in_{idx}", t)



def parseMaxSteps : TSyntax `uplcMaxSteps → TermElabM Nat
  | `(uplcMaxSteps | $n:num) => return n.getNat
  | _ => throwUnsupportedSyntax


@[command_elab preprocess]
def preprocessImp : CommandElab := fun stx => do
  let decl ←
      withoutModifyingEnv $ runTermElabM fun _ => do
        let app ← mkUplcApply stx
        let (e, _) ← Optimize.main app|>.run default
        let t ← inferType e
        return Declaration.defnDecl {
                 name := ← validNewDef stx[1],
                 levelParams := [],
                 type := t,
                 value := e,
                 hints := .abbrev,
                 safety := .safe }
  liftCoreM <| addAndCompile <| decl

  where
    validNewDef (f : Syntax) : TermElabM Name := do
      let some s := f.isStrLit?
        | throwErrorAt f m!"string literal expected"
      return Name.mkSimple s

    /-- Resolve prog ident and validate that it
        corresponds to a definition returning UPLC.Uplc.Program.
    -/
    validUplcProg (prog : Syntax) : TermElabM Expr := do
      let some uplcProg ← resolveId? prog |
        throwErrorAt prog m!"unknown constant '{.ofConstName prog.getId}'"
      let ConstantInfo.defnInfo info ← getConstInfo uplcProg.constName! |
        throwErrorAt prog m!"unknown definition '{.ofConstName prog.getId}'"
      let Expr.const ``UPLC.Uplc.Program _ := info.type |
        throwErrorAt prog m!"UPLC.Uplc.Program type expected for '{.ofConstName prog.getId}'"
      return uplcProg

    validFunType (t : Expr) (declInfos : Array (Name × Expr)) : TermElabM Bool := do
      Meta.forallTelescope t fun xs ret => do
        if xs.size ≠ declInfos.size then return false
        for i in [:xs.size] do
          if (← inferType xs[i]!) != declInfos[i]!.2 then return false
        match ret with
        | Expr.app (Expr.const ``List _) (Expr.const ``UPLC.Uplc.Term _) => return true
        | _ => return false

    /-- Resolve input conversion function `f` and ensures that:
       - Type(f) = α₁ → .. → αₙ → List UPLC.Uplc.Term`
       - ∀ i ∈ [1..declsInfos.size], Type(declsInfos[i]!.2) = αᵢ
       NOTE: that Type(f) can also be `List UPLC.Uplc.Term` only, i.e.,
       f produces constant uplc values.
    -/
    validConversionFun (f : Syntax) (declInfos : Array (Name × Expr)) : TermElabM (Option Expr) := do
      match f.getOptional? with
      | none =>
          if declInfos.size > 0
          then throwErrorAt f "inputs provided but no conversion function specified"
          else return none
      | some f' =>
         let some conv ← resolveId? f' |
           throwErrorAt f' m!"unknown constant '{.ofConstName f'.getId}'"
         let ConstantInfo.defnInfo info ← getConstInfo conv.constName! |
           throwErrorAt f' m!"unknown definition '{.ofConstName f'.getId}'"
         if !(← validFunType info.type declInfos) then
           throwErrorAt f' m!"inputs and conversion fun types mismatched '{declInfos}' {info.type}'"
         return conv

    mkUplcApply (stx : Syntax) : TermElabM Expr := do
      let uplcProg ← validUplcProg stx[2]
      let declInfos ← parseInputs ⟨stx[3]⟩
      let unit ← parseMaxSteps ⟨stx[5]⟩
      -- validate that Type(f) := α₁ → .. → αₙ → List Term` ∧
      --  ∀ i ∈ [1..inputs.size], Type(inputs[i]!) = αᵢ
      let cekExec := Lean.mkConst ``UPLC.CekMachine.cekExecuteProgram
      let termType := Lean.mkConst ``UPLC.Uplc.Term
      match (← validConversionFun stx[4] declInfos) with
      | none => return mkApp3 cekExec uplcProg (mkApp (Lean.mkConst ``List.nil) termType) (mkNatLit unit)
      | some f' =>
           withLocalDeclsDND declInfos fun xs =>
             mkLambdaFVars xs (mkApp3 cekExec uplcProg (mkAppN f' xs) (mkNatLit unit))


end UPLC.PreProcess
