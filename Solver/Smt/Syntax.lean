import Lean


namespace Solver.Smt

abbrev SmtSymbol := String

/-- Smt-Lib V2 sort expression. -/
inductive SortExpr where
 | SymbolSort (nm : SmtSymbol)
 | ParamSort (nm : SmtSymbol) (ps : Array SortExpr)

instance : Inhabited SortExpr where
  default := .SymbolSort ""

abbrev SortedVars := Array (SmtSymbol × SortExpr)



mutual
/-- Smt term annotation attributes. -/
inductive SmtAttribute where
  | Named (n : String)
  | Pattern (p : Array SmtTerm)
  | Qid (n : String)

/-- Smt-Lib V2 term. -/
inductive SmtTerm where
 | NumTerm (v : Nat)
 | DecTerm (v : String)
 | BinTerm (v : String)
 | HexTerm (v : String)
 | StrTerm (v : String)
 | SmtIdent (nm : SmtSymbol)
 | AppTerm (nm : SmtSymbol) (args : Array SmtTerm)
 | LetTerm (bs: Array (SmtSymbol × SmtTerm)) (body : SmtTerm)
 | ForallTerm (bs : SortedVars) (body : SmtTerm)
 | ExistsTerm (bs : SortedVars) (body : SmtTerm)
 | LambdaTerm (bs : SortedVars) (body : SmtTerm)
 | AnnotatedTerm (t : SmtTerm) (annot : Array SmtAttribute)
 -- NOTE: we are not expecting to use match expression as they will be represented as ite.
end

instance : Inhabited SmtAttribute where
  default := .Qid ""

instance : Inhabited SmtTerm where
  default := .NumTerm 0

abbrev SmtSelector := SmtSymbol × SortExpr
abbrev SmtConstructorDecl := SmtSymbol × Option (Array SmtSelector)

structure SmtDatatypeDecl where
  params : Option (Array SmtSymbol)
  ctors : Array SmtConstructorDecl

structure SmtSortDecl where
  name : SmtSymbol
  arity : Nat

structure SmtFunDecl where
  name : SmtSymbol
  params : SortedVars
  ret : SortExpr

/-- Smt-Lib V2 command submitted to backend solver. -/
inductive SmtCommand where
  | assertTerm (t : SmtTerm)
  | checkSat
  | declareConst (nm : SmtSymbol) (t : SortExpr)
  | declareDataType (nm : SmtSymbol) (decl: SmtDatatypeDecl)
  | declareMutualDataTypes (nms : Array SmtSortDecl) (decls : Array SmtDatatypeDecl)
  | declareFun (nm : SmtSymbol) (args : Array SortExpr) (rt : SortExpr)
  | defineFun (isRec : Bool) (nm : SmtSymbol) (args : SortedVars) (rt: SortExpr) (body : SmtTerm)
  | defineFunsRec (decls : Array SmtFunDecl) (bodies : Array SmtTerm) -- mutually recursive functions
  | declareSort (nm : SmtSymbol) (arity : Nat)
  | defineSort (nm : SmtSymbol) (args : Option (Array SmtSymbol)) (body : SortExpr)
  | exitSmt
  | getModel
  | getProof
  | evalTerm (t : SmtTerm)
  | setLogic (l : SmtSymbol)
  | setOption (opt : String) (value : Bool)

instance : Inhabited SmtCommand where
  default := .setLogic ""


/-! ToString instances for Smt-Lib V2 syntax. -/

@[inline] private partial def SortExpr.toString (e : SortExpr) : String :=
  match e with
  | .SymbolSort nm => nm
  | .ParamSort nm ps =>
      let sps := Array.foldl (fun acc a => s!"{acc} {SortExpr.toString a}") "" ps
      s!"({nm} {sps})"


instance : ToString SortExpr where
  toString := SortExpr.toString

@[inline] private partial def SortedVars.toString (sv : SortedVars) : String :=
   Array.foldl (fun acc a => s!"{acc} ( {a.1} {a.2} ) ") "" sv

instance : ToString SortedVars where
  toString := SortedVars.toString

mutual
@[inline] private partial def SmtAttribute.toString (a : SmtAttribute) : String :=
  match a with
  | .Named n => s!":named {n}"
  | .Pattern p =>
      let sp := Array.foldl (fun acc a => s!"{acc} {a.toString}") "" p
      s!":pattern ({sp})"
  | .Qid n => s!":qid {n}"

@[inline] private partial def SmtTerm.toString (e : SmtTerm) : String :=
   match e with
   | .NumTerm v => Nat.repr v
   | .DecTerm v => v
   | .BinTerm v => v
   | .HexTerm v => v
   | .StrTerm v => v
   | .SmtIdent nm => nm
   | .AppTerm m args =>
       let sargs := Array.foldl (fun acc a => s!"{acc} {a.toString}") "" args
       s!"( {m} {sargs} )\n"
   | .LetTerm bs body =>
       let sbs := Array.foldl (fun acc a => s!"{acc} ( {a.1} {a.2.toString} ) ") "" bs
       s!"( let ({sbs}) {body.toString} )\n"
   | .ForallTerm bs body =>
       s!"( forall ({bs}) {body.toString} )\n"
   | .ExistsTerm bs body =>
       s!"( exists ({bs}) {body.toString} )\n"
   | .LambdaTerm bs body =>
       s!"( lambda ({bs}) {body.toString} )\n"
   | .AnnotatedTerm t annot =>
       let sannot := Array.foldl (fun acc a => s!"{acc} {a.toString}") "" annot
       s!"(! {t.toString} {sannot} )\n"
end

instance : ToString SmtAttribute where
  toString := SmtAttribute.toString

instance : ToString SmtTerm where
  toString := SmtTerm.toString

@[inline] private def SmtSelector.toString (s : SmtSelector) : String :=
  s!"( {s.1} {s.2} )"

instance : ToString SmtSelector where
  toString := SmtSelector.toString


@[inline] private def SmtConstructorDecl.toString (decl : SmtConstructorDecl) : String :=
  let selstr :=
    match decl.2 with
    | none => ""
    | some sel => Array.foldl (fun acc a => s!"{acc} {a}") "" sel
  s!"( {decl.1} {selstr} )\n"

instance : ToString SmtConstructorDecl where
  toString := SmtConstructorDecl.toString


@[inline] private def SmtDatatypeDecl.toString (d : SmtDatatypeDecl) : String :=
  let parstr :=
    match d.params with
    | none => ""
    | some args =>
       let sargs := Array.foldl (fun acc a => s!"{acc} {a}" ) "" args
       s!"par ( {sargs} )"
  let declstr := Array.foldl (fun acc d => s!"{acc} {d}" ) "" d.ctors
  s!"( {parstr} ( {declstr} ) )"

instance : ToString SmtDatatypeDecl where
  toString := SmtDatatypeDecl.toString

@[inline] private def SmtSortDecl.toString (d : SmtSortDecl) : String :=
  s!"( {d.name} {d.arity} )"

instance : ToString SmtSortDecl where
  toString := SmtSortDecl.toString

@[inline] private def SmtFunDecl.toString (d : SmtFunDecl) : String :=
  s!"( {d.name} ( {d.params} ) {d.ret} )"

instance : ToString SmtFunDecl where
  toString := SmtFunDecl.toString

@[inline] private def SmtCommand.toString (c : SmtCommand) : String :=
 match c with
 | .assertTerm t => s!"(assert {t})\n"
 | .checkSat => s!"(check-sat)\n"
 | .declareConst nm t => s!"(declare-const {nm} {t})\n"
 | .declareDataType nm decl => s!"(declare-datatype {nm} {decl})\n"
 | .declareMutualDataTypes nm decl =>
    let nmstr := Array.foldl (fun acc d => s!"{acc} {d}") "" nm
    let declstr := Array.foldl (fun acc d => s!"{acc} {d}\n") "" decl
    s!"(declare-datatypes ( {nmstr} )\n ( {declstr} )\n )\n"
 | .declareFun nm args rt =>
     let sargs := Array.foldl (fun acc a => s!"{acc} {a}") "" args
     s!"(declare-fun {nm} ( {sargs} ) {rt} )\n"
 | .defineFun isRec nm nargs rt body =>
    let defstr := if isRec then "define-fun-rec" else "define-fun"
    s!"({defstr} {nm} ( {nargs} ) {rt} {body})\n"
 | .defineFunsRec decls bodies =>
    let sdecls := Array.foldl (fun acc d => s!"{acc} {d}\n") "" decls
    let sbodies := Array.foldl (fun acc b => s!"{acc} {b}\n") "" bodies
    s!"(define-funs-rec ( {sdecls} )\n ( {sbodies} )\n )\n"
 | .declareSort nm arity => s!"(declare-sort {nm} {arity} )\n"
 | .defineSort nm nargs body =>
    let sargs :=
       match nargs with
       | none => ""
       | some args => Array.foldl (fun acc s => s!"{acc} {s}") "" args
    s!"(define-sort {nm} ( {sargs} ) {body} )\n"
 | .exitSmt => s!"(exit)\n"
 | .getModel => s!"(get-model)\n"
 | .getProof => s!"(get-proof)\n"
 | .evalTerm t => s!"(eval {t})\n"
 | .setLogic l => s!"(set-logic {l})\n"
 | .setOption opt v => s!"(set-option {opt} {v})\n"

 instance : ToString SmtCommand where
   toString := SmtCommand.toString

end Solver.Smt
