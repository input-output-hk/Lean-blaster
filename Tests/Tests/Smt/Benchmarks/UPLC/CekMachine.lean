import Tests.Smt.Benchmarks.UPLC.CekValue
import Tests.Smt.Benchmarks.UPLC.Uplc
import Tests.Smt.Benchmarks.UPLC.Builtins
import Tests.Smt.Benchmarks.UPLC.BuiltinsFunctions.Evaluate

namespace UPLC.CekMachine
open UPLC.CekValue
open UPLC.Uplc
open UPLC.Builtins
open UPLC.Evaluate

set_option linter.unusedVariables false
-- setting this option to avoid warning on marco rules format and unused variables

-- Define Frame
inductive Frame where
  | ForceFrame              : Frame
  | LeftApplicationToTerm   : Term → Environment → Frame
  | LeftApplicationToValue  : CekValue → Frame
  | RightApplicationOfValue : CekValue → Frame
  | ConstructorArgument     : Nat → List CekValue → List Term → Environment → Frame
  | CaseScrutinee           : List Term → Environment → Frame
deriving Repr

-- Define Stack
abbrev Stack := List Frame

-- Define State
inductive State where
  | Eval    : Stack → Environment → Term → State
  | Return  : Stack → CekValue → State
  | Error   : State
  | Halt    : CekValue → State
deriving Repr

-- Define Helper Functions
-- Define ifBoundOtherwiseError
def ifBoundOtherwiseError (s : Stack) (p : Environment) (x : String) : State :=
  match p with
  | Environment.EmptyEnvironment => State.Error
  | Environment.NonEmptyEvironment p' x' V =>
      if x == x' then State.Return s V else ifBoundOtherwiseError s p' x

-- Define ifArgVOtherwiseError
def ifArgVOtherwiseError (Sigma : State) (l : ExpectedBuiltinArg) : State :=
  match l with
  | ExpectedBuiltinArg.ArgV => Sigma
  | ExpectedBuiltinArg.ArgQ => State.Error

def ifArgQOtherwiseError (Sigma : State) (l : ExpectedBuiltinArg) : State :=
  match l with
  | ExpectedBuiltinArg.ArgQ => Sigma
  | ExpectedBuiltinArg.ArgV => State.Error

def unfoldCase (s : Stack) (i : Nat) (Ms : List Term) (Vs : List CekValue) (p : Environment) : State :=
  match Ms[i]? with
  | some mi =>
      let sOut := Vs.foldr (fun V sAcc => Frame.LeftApplicationToValue V :: sAcc) s
      State.Eval sOut p mi
  | none => State.Error

def evalBuiltin (s : Stack) (b : BuiltinFun) (Vs : List CekValue) : State :=
  match UPLC.Evaluate.evaluateBuiltinFunction b Vs with
  | some V => State.Return s V
  | none => State.Error

-- Define the Step Function
open State

-----------------------------------------------------
-- State
-- State.Eval
syntax:49 term ";" term "▷" term : term
macro_rules
| `($s ; $ρ ▷ $M) => `(State.Eval $s $ρ $M)

-- State.Return
syntax:49 term "◁" term : term
macro_rules
| `($s ◁ $V) => `(State.Return $s $V)

-- State.Error
syntax:49 "◆" : term
macro_rules
| `(◆) => `(State.Error)

-- State.Halt
syntax:49 "▢" term : term
macro_rules
| `(▢ $V) => `(State.Halt $V)
-----------------------------------------------------

-----------------------------------------------------
-- Values
-- CekValue.VCon
syntax:49 "v" "⟨" "con" "T" ident "⟩" : term
macro_rules
| `(v ⟨con T $c⟩) => `(CekValue.VCon $c)

-- CekValue.VDelay
syntax:49 "v" "⟨" "delay" term "," term "⟩" : term
macro_rules
| `(v ⟨delay $M,$ρ⟩) => `(CekValue.VDelay $M $ρ)

-- CekValue.VLam
syntax:49 "v" "⟨" "lam" ident "," term "," term "⟩" : term
macro_rules
| `(v ⟨lam $x,$M,$ρ⟩) => `(CekValue.VLam $x $M $ρ)

-- CekValue.VConstr
syntax:49 "v" "⟨" "constr" ident "," term "⟩" : term
macro_rules
| `(v ⟨constr $i, $Vs⟩) => `(CekValue.VConstr $i $Vs)

-- CekValue.VBuiltin
syntax:49 "v" "⟨" "builtin" ident "," term "," term "⟩" : term
macro_rules
| `(v ⟨builtin $b,$Vs,$l⟩) => `(CekValue.VBuiltin $b $Vs $l)

-----------------------------------------------------
-- UPLC
-- Term.Var
syntax:49 "u" "(" "var" ident ")" : term
macro_rules
| `(u ( var $x )) => `(Term.Var $x)

-- Term.Const
syntax:49 "u" "(" "con" "T" ident ")" : term
macro_rules
| `(u ( con T $c )) => `(Term.Const $c)

-- Term.Builtin
syntax:49 "u" "(" "builtin" ident ")" : term
macro_rules
| `(u ( builtin $b )) => `(Term.Builtin $b)

-- Term.Lam
syntax:49 "u" "(" "lam" ident "," term ")" : term
macro_rules
| `(u (lam $x, $M)) => `(Term.Lam $x $M)

-- Term.Apply
syntax:49 "u[" term " ∘_ " term "]" : term
macro_rules
| `(u[$M ∘_ $N]) => `(Term.Apply $M $N)

-- Term.Delay
syntax:49 "u" "(" "delay" term ")" : term
macro_rules
| `(u (delay $M)) => `(Term.Delay $M)

-- Term.Force
syntax:49 "u" "(" "force" term ")" : term
macro_rules
| `(u (force $M)) => `(Term.Force $M)

-- Term.Constr
syntax:49 "u" "(" "constr" ident term ")" : term
macro_rules
| `(u (constr $i $Ms)) => `(Term.Constr $i $Ms)

-- Term.Case
syntax:49 "u" "(" "case" term "," term ")" : term
macro_rules
| `(u (case $N,$Ms)) => `(Term.Case $N $Ms)

-- Term.Error
syntax:49 "u" "(" "error" ")" : term
macro_rules
| `(u (error)) => `(Term.Error)
-----------------------------------------------------

-----------------------------------------------------
-- Frames
-- Frame.ForceFrame
syntax:49 "@f" "(" "force" "⎵" ")" : term
macro_rules
| `(@f(force ⎵)) => `(Frame.ForceFrame)

-- Frame.LeftApplicationToTerm
syntax:49 "@f" "[" "⎵" "(" term "," term ")" "]" : term
macro_rules
| `(@f[⎵ ($M,$ρ)]) => `(Frame.LeftApplicationToTerm $M $ρ)

-- Frame.LeftApplicationToValue
syntax:49 "@f" "[" "⎵" term "]" : term
macro_rules
| `(@f[⎵ $V]) => `(Frame.LeftApplicationToValue $V)

-- Frame.RightApplicationOfValue
syntax:49 "@f" "[" term "⎵" "]" : term
macro_rules
| `(@f[$V ⎵]) => `(Frame.RightApplicationOfValue $V)

-- Frame.ConstructorArgument
syntax:49 "@f" "(" "constr" ident "," term "⎵" "(" term "," term ")" ")" : term
macro_rules
| `(@f(constr $i, $Vs ⎵ ($Ms,$ρ))) => `(Frame.ConstructorArgument $i $Vs $Ms $ρ)

-- Frame.CaseScrutinee
syntax:49 "@f" "(" "case" "⎵" "(" term "," term ")" ")" : term
macro_rules
| `(@f(case ⎵ ($Ms,$ρ))) => `(Frame.CaseScrutinee $Ms $ρ)
-----------------------------------------------------

-----------------------------------------------------
-- Environment
-- ifBoundOtherwiseError
syntax:49 term "◁" ident "⟦" ident "⟧" "If" ident "is" "bound" "in" term : term
macro_rules
| `($s ◁ $ρ ⟦ $x ⟧ If $y is bound in $env) => `(ifBoundOtherwiseError $s $env $x)

-- Environment.NonEmptyEnvironment
syntax:49 term "⟦" ident "↦" term "⟧" : term
macro_rules
| `($ρ ⟦ $x ↦ $V ⟧) => `(Environment.NonEmptyEvironment $ρ $x $V)
-----------------------------------------------------

-----------------------------------------------------
-- Builtins
-- ifArgVOtherwiseError
syntax:49 term "If" ident "∈" "𝓤" "∪" "𝓥" : term
macro_rules
| `($s If $i ∈ 𝓤 ∪ 𝓥) => `(ifArgVOtherwiseError $s $i)

-- ifArgQOtherwiseError
syntax:49 term "If" ident "∈" "𝓠" : term
macro_rules
| `($s If $i ∈ 𝓠) => `(ifArgQOtherwiseError $s $i)

--evalbuiltin
syntax:49 "Eval_CEK" "(" term "," term "," term ")" : term
macro_rules
| `(Eval_CEK ($s,$b,$Vs)) => `(evalBuiltin $s $b $Vs)
-----------------------------------------------------

-----------------------------------------------------
-- Lists
-- ::
syntax:49 term "⋅" term : term
macro_rules
| `($M ⋅ $Ms) => `($M :: $Ms)

syntax:49 term ":⋅" term : term
macro_rules
| `($Ms :⋅ $M) => `($Ms ++ [$M])


open UPLC.Builtins
open ExpectedBuiltinArgs
open BuiltinNotations

def step (Sigma : State) : State :=
  match Sigma with
  |                                 s; ρ ▷ u(var x)               => s ◁ ρ⟦x⟧ If x is bound in ρ
  |                                 s; ρ ▷ u(con T c)             => s ◁ v⟨con T c⟩
  |                                 s; ρ ▷ u(lam x, M)            => s ◁ v⟨lam x, M, ρ⟩
  |                                 s; ρ ▷ u(delay M)             => s ◁ v⟨delay M, ρ⟩
  |                                 s; ρ ▷ u(force M)             =>  (@f(force ⎵) ⋅ s); ρ ▷ M
  |                                 s; ρ ▷ u[M ∘_ N]              => (@f[⎵ (N, ρ)] ⋅ s); ρ ▷ M
  |                                 s; ρ ▷ u(constr i (M ⋅ Ms))   => (@f(constr i, [] ⎵ (Ms, ρ)) ⋅ s); ρ ▷ M
  |                                 s; ρ ▷ u(constr i [])         => s ◁ v⟨constr i, []⟩
  |                                 s; ρ ▷ u(case N, Ms)          => (@f(case ⎵ (Ms, ρ)) ⋅ s); ρ ▷ N
  |                                 s; ρ ▷ u(builtin b)           => s ◁ v⟨builtin b, [], α(b)⟩
  |                                 s; ρ ▷ u(error)               => ◆
  |                                   [] ◁ V                      => ▢ V
  |                    (@f[⎵ (M, ρ)] ⋅ s) ◁ V                      => (@f[V ⎵] ⋅ s); ρ ▷ M
  |             (@f[v⟨lam x, M, ρ⟩ ⎵] ⋅ s) ◁ V                      => s; ρ⟦x ↦ V⟧ ▷ M
  |                         (@f[⎵ V] ⋅ s) ◁ v⟨lam x, M, ρ⟩          => s; ρ⟦x ↦ V⟧ ▷ M
  |   (@f[v⟨builtin b, Vs, ι ⊙ η⟩ ⎵] ⋅ s) ◁ V                       => (s ◁ v⟨builtin b, Vs :⋅ V, η⟩) If ι ∈ 𝓤 ∪ 𝓥
  |                         (@f[⎵ V] ⋅ s) ◁ v⟨builtin b, Vs, ι ⊙ η⟩ => (s ◁ v⟨builtin b, Vs :⋅ V, η⟩) If ι ∈ 𝓤 ∪ 𝓥
  |     (@f[v⟨builtin b, Vs, a[ι]⟩ ⎵] ⋅ s) ◁ V                      => (Eval_CEK(s, b, Vs :⋅ V)) If ι ∈ 𝓤 ∪ 𝓥
  |                         (@f[⎵ V] ⋅ s) ◁ v⟨builtin b, Vs, a[ι]⟩  => (Eval_CEK(s, b, Vs :⋅ V)) If ι ∈ 𝓤 ∪ 𝓥
  |                     (@f(force ⎵) ⋅ s) ◁ v⟨delay M, ρ⟩           => s; ρ ▷ M
  |                     (@f(force ⎵) ⋅ s) ◁ v⟨builtin b, Vs, ι ⊙ η⟩ => (s ◁ v⟨builtin b, Vs, η⟩) If ι ∈ 𝓠
  |                     (@f(force ⎵) ⋅ s) ◁ v⟨builtin b, Vs, a[ι]⟩  => (Eval_CEK(s, b, Vs)) If ι ∈ 𝓠
  |  (@f(constr i, Vs ⎵ (M ⋅ Ms, ρ)) ⋅ s) ◁ V                       => (@f(constr i, Vs :⋅ V ⎵ (Ms, ρ)) ⋅ s); ρ ▷ M
  |      (@f(constr i, Vs ⎵ ([], ρ)) ⋅ s) ◁ V                      => s ◁ v⟨constr i, Vs :⋅ V⟩
  |              (@f(case ⎵ (Ms, ρ)) ⋅ s) ◁ v⟨constr i, Vs⟩         => unfoldCase s i Ms Vs ρ
  | _ => ◆

-- Define Run Steps
def runSteps (Sigma : State) (n : Nat) : State :=
  match n, Sigma with
  | _, ▢ V => Sigma
  | _, ◆ => Sigma
  | 0, _ => Sigma -- change to error when num steps exhausted
  | Nat.succ n, _ => runSteps (step Sigma) n

-- Define Apply Params
def applyParams (body : Term) (params : List Term) : Term :=
  match params with
  | h :: t => applyParams (Term.Apply body h) t
  | [] => body

-- Define Initial State
def initialState (t : Term) : State :=
  []; Environment.EmptyEnvironment ▷ t

-- Define CEK Execution
def cekExecuteProgram (p : Program) (params : List Term) (n : Nat) : State :=
  match p with
  | Program.Program _ body =>
      -- considering all UPLC version
      -- TODO: consider version when evaluating builtins
      runSteps (initialState (applyParams body params)) n

end UPLC.CekMachine
