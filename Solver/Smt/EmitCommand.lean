import Lean
import Solver.Optimize.Env

open Solver.Optimize

namespace Solver.Smt

@[always_inline, inline]
def getProcStdIn : TranslateEnvT (IO.FS.Handle) := do
  let some p := (← get).smtEnv.smtProc |
    throwEnvError "getProcStdIn: Undefined solver instance !!!"
  return p.stdin

@[always_inline, inline]
def getProcStdOut : TranslateEnvT (IO.FS.Handle) := do
  let some p := (← get).smtEnv.smtProc |
    throwEnvError "getProcStdOut: Undefined solver instance !!!"
  return p.stdout

def updateSymbolCache (s : SmtSymbol) (rep : String) : TranslateEnvT Unit := do
  modify (fun env => { env with smtEnv.symbolStrCache :=
                                env.smtEnv.symbolStrCache.insert s rep })

@[always_inline, inline]
def withSymbolCache (s : SmtSymbol) : TranslateEnvT String := do
  match (← get).smtEnv.symbolStrCache.get? s with
  | some rep => return rep
  | none =>
     let rep := s.toString
     updateSymbolCache s rep
     return rep


def SmtSymbol.emit (s : SmtSymbol) : TranslateEnvT Unit := do
  let h ← getProcStdIn
  h.putStr (← withSymbolCache s)

partial def SortExpr.emit (e : SortExpr) : TranslateEnvT Unit := do
  let h ← getProcStdIn
  match e with
  | .SymbolSort nm => nm.emit
  | .ParamSort nm ps =>
       h.putStr "("
       nm.emit
       Array.forM
        (λ a => do
         h.putStr " "
         a.emit) ps
       h.putStr ")"

def SortedVars.emit (sv : SortedVars) : TranslateEnvT Unit := do
  let h ← getProcStdIn
  Array.forM
    (λ a => do
        h.putStr "("
        a.1.emit
        h.putStr " "
        a.2.emit
        h.putStr ")"
    ) sv

def SmtQualifiedIdent.emit (id : SmtQualifiedIdent) : TranslateEnvT Unit := do
  match id with
  | .SimpleIdent nm => nm.emit
  | .QualifiedIdent nm t =>
       let h ← getProcStdIn
       h.putStr "(as "
       nm.emit
       h.putStr " "
       t.emit
       h.putStr ")"


mutual
partial def ArraySmtTerm.emit (terms : Array SmtTerm) : TranslateEnvT Unit := do
   let h ← getProcStdIn
   Array.forM
     (λ a => do
       h.putStr " "
       a.emit
     ) terms

partial def SmtAttribute.emit (a : SmtAttribute) : TranslateEnvT Unit := do
  let h ← getProcStdIn
  match a with
  | .Named n =>
        h.putStr ":named "
        h.putStr n
  | .Pattern p =>
        h.putStr ":pattern ("
        ArraySmtTerm.emit p
        h.putStr ")"
  | .Qid n =>
         h.putStr ":qid "
         h.putStr n

partial def SmtTerm.emit (e : SmtTerm) : TranslateEnvT Unit := do
   let h ← getProcStdIn
   match e with
   | .NumTerm v => h.putStr s!"{v}"
   | .BoolTerm b => if b then h.putStr "true" else h.putStr "false"
   | .DecTerm v
   | .BinTerm v
   | .HexTerm v
   | .StrTerm v => h.putStr v
   | .SmtIdent nm => nm.emit
   | .AppTerm m args =>
       let bline := if isIteApp m then ")\n" else ")"
       h.putStr "("
       m.emit
       ArraySmtTerm.emit args
       h.putStr bline
   | .LetTerm bs body =>
       h.putStr "(let ("
       Array.forM
         (λ a => do
            h.putStr "("
            a.1.emit
            h.putStr " "
            a.2.emit
            h.putStr ")"
         ) bs
       h.putStr ") "
       body.emit
       h.putStr ")\n"
   | .ForallTerm bs body =>
        h.putStr "(forall ("
        bs.emit
        h.putStr ")\n "
        body.emit
        h.putStr ")\n"
   | .ExistsTerm bs body =>
        h.putStr "(exists ("
        bs.emit
        h.putStr ")\n "
        body.emit
        h.putStr ")\n"
   | .LambdaTerm bs body =>
        h.putStr "(lambda ("
        bs.emit
        h.putStr ")\n "
        body.emit
        h.putStr ")\n"
   | .AnnotatedTerm t annot =>
       h.putStr "(!"
       t.emit
       h.putStr " "
       Array.forM
         (λ a => do
           h.putStr " "
           a.emit
         ) annot
       h.putStr ")\n"
end


def SmtSelector.emit (s : SmtSelector) : TranslateEnvT Unit := do
  let h ← getProcStdIn
  h.putStr "("
  s.1.emit
  h.putStr " "
  s.2.emit
  h.putStr ")"


def SmtConstructorDecl.emit (decl : SmtConstructorDecl) : TranslateEnvT Unit := do
  let h ← getProcStdIn
  h.putStr "("
  decl.1.emit
  h.putStr " "
  selectorsEmit h decl.2
  h.putStr ")\n"

  where
    selectorsEmit (h : IO.FS.Handle) (sels : Option (Array SmtSelector)) : TranslateEnvT Unit := do
     match sels with
     | none => pure ()
     | some sel =>
         Array.forM
           (λ a => do
             h.putStr " "
             a.emit
           ) sel

def SmtDatatypeDecl.emit (d : SmtDatatypeDecl) : TranslateEnvT Unit := do
  let h ← getProcStdIn
  match d.params with
  | none => ctorsEmit h d.ctors
  | some args =>
      h.putStr "(par ("
      Array.forM
        (λ a => do
          h.putStr " "
          a.emit
        ) args
      h.putStr ") "
      ctorsEmit h d.ctors
      h.putStr ")"

  where
    ctorsEmit (h : IO.FS.Handle) (ctors : Array SmtConstructorDecl) : TranslateEnvT Unit := do
      h.putStr "("
      Array.forM
        (λ d => do
           h.putStr " "
           d.emit
        ) ctors
      h.putStr ")"

def SmtSortDecl.emit (d : SmtSortDecl) : TranslateEnvT Unit := do
  let h ← getProcStdIn
  h.putStr "("
  d.name.emit
  h.putStr s!" {d.arity})"


def SmtFunDecl.emit (d : SmtFunDecl) : TranslateEnvT Unit := do
  let h ← getProcStdIn
  h.putStr "("
  d.name.emit
  h.putStr " ("
  d.params.emit
  h.putStr ") "
  d.ret.emit
  h.putStr ")"


def SmtCommand.emit (c : SmtCommand) : TranslateEnvT Unit := do
  let h ← getProcStdIn
  emitAux h c
  h.flush

 where
   sortArgsEmit (h : IO.FS.Handle) (nargs : Option (Array SmtSymbol)) : TranslateEnvT Unit := do
     match nargs with
     | none => h.putStr "()"
     | some args =>
         h.putStr "("
         Array.forM
           (λ s => do
             h.putStr " "
             s.emit
           ) args
         h.putStr ")"

   emitAux (h : IO.FS.Handle) (c : SmtCommand) : TranslateEnvT Unit := do
     match c with
     | .assertTerm t =>
          h.putStr "(assert "
          t.emit
          h.putStr ")\n"
     | .checkSat => h.putStrLn "(check-sat)"
     | .checkSatAssuming args =>
          h.putStr "(check-sat-assuming ("
          ArraySmtTerm.emit args
          h.putStr "))\n"
     | .declareConst nm t =>
          h.putStr "(declare-const "
          nm.emit
          h.putStr " "
          t.emit
          h.putStr ")\n"
     | .declareDataType nm decl =>
          h.putStr "(declare-datatype "
          nm.emit
          h.putStr " "
          decl.emit
          h.putStr ")\n"
     | .declareMutualDataTypes nm decl =>
          h.putStr "(declare-datatypes ("
          Array.forM
            (λ d => do
              h.putStr " "
              d.emit
            ) nm
          h.putStr ")\n ("
          Array.forM
            (λ d => do
              h.putStr " "
              d.emit
              h.putStr "\n"
            ) decl
          h.putStr "))\n"
     | .declareFun nm args rt =>
          h.putStr "(declare-fun "
          nm.emit
          h.putStr " ("
          Array.forM
            (λ a => do
              h.putStr " "
              a.emit
            ) args
          h.putStr ") "
          rt.emit
          h.putStr ")\n"
     | .defineFun isRec nm nargs rt body =>
          let defstr := if isRec then "(define-fun-rec " else "(define-fun "
          h.putStr defstr
          nm.emit
          h.putStr " ("
          nargs.emit
          h.putStr ") "
          rt.emit
          h.putStr " "
          body.emit
          h.putStr ")\n"
     | .defineFunsRec decls bodies =>
          h.putStr "(define-funs-rec ("
          Array.forM
            (λ d => do
               h.putStr "\n"
               d.emit
            ) decls
          h.putStr ")\n ("
          Array.forM
            (λ b => do
              h.putStr "\n"
              b.emit
            ) bodies
          h.putStr ")\n)\n"
     | .declareSort nm arity =>
          h.putStr "(declare-sort "
          nm.emit
          h.putStr " "
          h.putStr s!"{arity}"
          h.putStr ")\n"
     | .defineSort nm nargs body =>
          h.putStr "(define-sort "
          nm.emit
          sortArgsEmit h nargs
          h.putStr " "
          body.emit
          h.putStr ")\n"
     | .exitSmt => h.putStr "(exit)\n"
     | .getModel => h.putStr "(get-model)\n"
     | .getProof => h.putStr "(get-proof)\n"
     | .evalTerm t =>
          h.putStr "(eval "
          t.emit
          h.putStr ")\n"
     | .setLogic l =>
          h.putStr "(set-logic "
          h.putStr l
          h.putStr ")\n"
     | .setOption opt v =>
          h.putStr "(set-option "
          h.putStr opt
          h.putStr " "
          h.putStr s!"{v}"
          h.putStr ")\n"

end Solver.Smt
