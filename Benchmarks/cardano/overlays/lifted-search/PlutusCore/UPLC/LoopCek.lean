import PlutusCore.UPLC.RecursiveCalls

/-! Fuse CEK evaluation with certified recursive-body specializations. Worker
results are resumed at their exact remaining fuel with this same interpreter. -/
namespace PlutusCore.UPLC.LoopCek
open PlutusCore.Default CekMachine CekValue Term Builtins
open BuiltinFunctions.Evaluate

/-- Select only the needed binding; discard the rest of the environment. -/
def lookupValue (env : Environment) (x : String) : Option CekValue :=
  match env with
  | .EmptyEnvironment => none
  | .NonEmptyEnvironment rest y v =>
      if x = y then some v else lookupValue rest x

mutual
  def eval (sv : BuiltinSemanticsVariant) (fuel : Nat)
      (s : Stack) (env : Environment) (t : Term) : State :=
    match fuel with
    | 0 => .Error
    | n + 1 =>
      match t with
      | .Var x =>
          match lookupValue env x with
          | some v => ret sv n s v
          | none => .Error
      | .Const c => ret sv n s (.VCon c)
      | .Lam x body => ret sv n s (.VLam x body env)
      | .Delay body => ret sv n s (.VDelay body env)
      | .Force body => eval sv n (.ForceFrame :: s) env body
      | .Apply f a => eval sv n (.LeftApplicationToTerm a env :: s) env f
      | .Builtin b => ret sv n s (.VBuiltin b [] (expectedArgs b))
      | .Error => .Error
      | .Constr i ts =>
          match ts with
          | body :: rest => eval sv n (.ConstructorArgument i [] rest env :: s) env body
          | [] => ret sv n s (.VConstr i [])
      | .Case body branches => eval sv n (.CaseScrutinee branches env :: s) env body
  termination_by fuel
  decreasing_by all_goals omega

  def ret (sv : BuiltinSemanticsVariant) (fuel : Nat)
      (s : Stack) (v : CekValue) : State :=
    match fuel with
    | 0 => .Error
    | n + 1 =>
      match s with
      | [] => .Halt v
      | .LeftApplicationToTerm body env :: rest =>
          eval sv n (.RightApplicationOfValue v :: rest) env body
      | .RightApplicationOfValue f :: rest =>
          match f with
          | .VLam x body env =>
              match RecursiveCalls.recognize x body env v with
              | none => eval sv n rest (.NonEmptyEnvironment env x v) body
              | some plan =>
                match plan.worker sv n with
                | none => .Error
                | some (remaining,result) =>
                  if h : remaining < n then ret sv remaining rest result else .Error
          | .VBuiltin b vs expected =>
              match expected with
              | .More .ArgV tail => ret sv n rest (.VBuiltin b (v :: vs) tail)
              | .One .ArgV =>
                  match evaluateBuiltinFunction sv b (v :: vs) with
                  | some result => ret sv n rest result
                  | none => .Error
              | _ => .Error
          | _ => .Error
      | .LeftApplicationToValue arg :: rest =>
          match v with
          | .VLam x body env => eval sv n rest (.NonEmptyEnvironment env x arg) body
          | .VBuiltin b vs expected =>
              match expected with
              | .More .ArgV tail => ret sv n rest (.VBuiltin b (arg :: vs) tail)
              | .One .ArgV =>
                  match evaluateBuiltinFunction sv b (arg :: vs) with
                  | some result => ret sv n rest result
                  | none => .Error
              | _ => .Error
          | _ => .Error
      | .ForceFrame :: rest =>
          match v with
          | .VDelay body env => eval sv n rest env body
          | .VBuiltin b vs expected =>
              match expected with
              | .More .ArgQ tail => ret sv n rest (.VBuiltin b vs tail)
              | .One .ArgQ =>
                  match evaluateBuiltinFunction sv b vs with
                  | some result => ret sv n rest result
                  | none => .Error
              | _ => .Error
          | _ => .Error
      | .ConstructorArgument i vs ts env :: rest =>
          match ts with
          | body :: remaining => eval sv n (.ConstructorArgument i (v :: vs) remaining env :: rest) env body
          | [] => ret sv n rest (.VConstr i (List.reverse (v :: vs)))
      | .CaseScrutinee Ms ρ :: rest =>
          match v with
          | CekValue.VConstr i Vs =>
               match Ms[i]? with
               | some mi => eval sv n (step.folding Vs rest) ρ mi
               | none => .Error

          | CekValue.VCon (Const.Integer value) =>
               if 0 ≤ value && value.toNat < Ms.length then
                 match Ms[value.toNat]? with
                 | some mi => eval sv n rest ρ mi
                 | none => .Error
               else .Error

          | CekValue.VCon (Const.Bool false) =>
               if Ms.length == 1 || Ms.length == 2 then
                 match Ms[0]? with
                 | some mi => eval sv n rest ρ mi
                 | none => .Error
               else .Error

          | CekValue.VCon (Const.Bool true) =>
               if Ms.length == 2 then
                 match Ms[1]? with
                 | some mi => eval sv n rest ρ mi
                 | none => .Error
               else .Error

          | CekValue.VCon Const.Unit =>
                if Ms.length == 1 then
                  match Ms[0]? with
                  | some mi => eval sv n rest ρ mi
                  | none => .Error
                else .Error

          | CekValue.VCon (Const.Pair p) =>
                if Ms.length == 1 then
                  let Vs := [CekValue.VCon p.1, CekValue.VCon p.2]
                  match Ms[0]? with
                  | some mi => eval sv n (step.folding Vs rest) ρ mi
                  | none => .Error
                else .Error

          | CekValue.VCon (Const.PairData p) =>
                if Ms.length == 1 then
                  let Vs := [CekValue.VCon (Const.Data p.1), CekValue.VCon (Const.Data p.2)]
                  match Ms[0]? with
                  | some mi => eval sv n (step.folding Vs rest) ρ mi
                  | none => .Error
                else .Error

          | CekValue.VCon (Const.ConstList (c :: cs)) =>
                if Ms.length == 1 || Ms.length == 2 then
                  let Vs := [CekValue.VCon c, CekValue.VCon (Const.ConstList cs)]
                  match Ms[0]? with
                  | some mi => eval sv n (step.folding Vs rest) ρ mi
                  | none => .Error
                else .Error

          | CekValue.VCon (Const.ConstList []) =>
                if Ms.length == 2 then
                  match Ms[1]? with
                  | some mi => eval sv n rest ρ mi
                  | none => .Error
                else .Error

          | CekValue.VCon (Const.ConstDataList (c :: cs)) =>
                if Ms.length == 1 || Ms.length == 2 then
                  let Vs := [CekValue.VCon (.Data c), CekValue.VCon (Const.ConstDataList cs)]
                  match Ms[0]? with
                  | some mi => eval sv n (step.folding Vs rest) ρ mi
                  | none => .Error
                else .Error

          | CekValue.VCon (Const.ConstDataList []) =>
                if Ms.length == 2 then
                  match Ms[1]? with
                  | some mi => eval sv n rest ρ mi
                  | none => .Error
                else .Error

          | CekValue.VCon (Const.ConstPairDataList (c :: cs)) =>
                if Ms.length == 1 || Ms.length == 2 then
                  let Vs := [CekValue.VCon (.PairData c), CekValue.VCon (Const.ConstPairDataList cs)]
                  match Ms[0]? with
                  | some mi => eval sv n (step.folding Vs rest) ρ mi
                  | none => .Error
                else .Error

          | CekValue.VCon (Const.ConstPairDataList []) =>
                if Ms.length == 2 then
                  match Ms[1]? with
                  | some mi => eval sv n rest ρ mi
                  | none => .Error
                else .Error

          | _ => .Error
  termination_by fuel
  decreasing_by all_goals omega
end

/-- Entry point preserving the existing machine's terminal-state convention. -/
def run (sv : BuiltinSemanticsVariant) (state : State) (fuel : Nat) : State :=
  match state with
  | .Eval s env t => eval sv fuel s env t
  | .Return s v => ret sv fuel s v
  | .Halt _ | .Error => state

def execute (p : Program) (params : List Term) (fuel : Nat) : State :=
  match p with
  | .Program _ body => run default (initialState (applyParams body params)) fuel

end PlutusCore.UPLC.LoopCek
