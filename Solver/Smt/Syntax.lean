import Lean

namespace Solver.Smt

/-- Smt-Lib V2 Smt symbol. -/
inductive SmtSymbol where
  /-- To be used for reserve word (e.g., operator symbol) -/
  | ReservedSymbol (str : String)
  /-- To be used for representing user defined symbol -/
  | NormalSymbol (str : String)

instance : Inhabited SmtSymbol where
  default := .NormalSymbol ""

instance : BEq SmtSymbol where
  beq | .ReservedSymbol s1, .ReservedSymbol s2 => s1 == s2
      | .NormalSymbol s1, .NormalSymbol s2 => s1 == s2
      | _, _ => false

private def SmtSymbol.hash : SmtSymbol → UInt64
  | .ReservedSymbol str => mixHash 11 str.hash
  | .NormalSymbol str => mixHash 13 str.hash

instance : Hashable SmtSymbol := ⟨SmtSymbol.hash⟩


/-- Smt-Lib V2 sort expression. -/
inductive SortExpr where
 | SymbolSort (nm : SmtSymbol)
 | ParamSort (nm : SmtSymbol) (ps : Array SortExpr)

instance : Inhabited SortExpr where
  default := .SymbolSort default

abbrev SortedVars := Array (SmtSymbol × SortExpr)


/-- Smt-Lib V2 qualified identifier. -/
inductive SmtQualifiedIdent where
 | SimpleIdent (nm : SmtSymbol)
 | QualifiedIdent (nm : SmtSymbol) (t : SortExpr)

instance : Inhabited SmtQualifiedIdent where
  default := .SimpleIdent default

/-- Return `true` if smt qualified ident correspond to smt `ite` symbol -/
def isIteApp (nm : SmtQualifiedIdent) : Bool :=
 match nm with
 | .SimpleIdent (.ReservedSymbol "ite") => true
 | _ => false

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
 | BoolTerm (b : Bool)
 | BinTerm (v : String)
 | HexTerm (v : String)
 | StrTerm (v : String)
 | SmtIdent (nm : SmtQualifiedIdent)
 | AppTerm (nm : SmtQualifiedIdent) (args : Array SmtTerm)
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

instance : Inhabited SmtDatatypeDecl where
  default := {params := none, ctors := #[]}


structure SmtSortDecl where
  name : SmtSymbol
  arity : Nat

instance : Inhabited SmtSortDecl where
  default := {name := default, arity := 0}


structure SmtFunDecl where
  name : SmtSymbol
  params : SortedVars
  ret : SortExpr

instance : Inhabited SmtFunDecl where
  default := {name := default, params := #[], ret := default}


/-- Smt-Lib V2 command submitted to backend solver. -/
inductive SmtCommand where
  | assertTerm (t : SmtTerm)
  | checkSat
  | checkSatAssuming (args : Array SmtTerm)
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
  | setLogic (l : String)
  | setOption (opt : String) (value : Bool)

instance : Inhabited SmtCommand where
  default := .setLogic ""


/-! Set of Smt-Lib V2 permitted characters in "simple" smt symbol. -/
opaque validSimpleChars : String :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789~!@$%^&*_-+=<>.?/"

/-! ToString instances for Smt-Lib V2 syntax. -/

@[inline] def SmtSymbol.toString (s : SmtSymbol) : String :=
  match s with
  | ReservedSymbol str => str
  | NormalSymbol str =>
      -- NOTE: A "simple" smt symbol is any non-empty sequence of
      -- characters in `validSimpleChars` that -- does not start with a digit.
      if str.isEmpty then "||"
      else
        let fstChar := str.get 0
        if (fstChar ≥ '0' && fstChar ≤ '9') || str.any (λ c => !(validSimpleChars.contains c))
        then s!"|{str}|" -- create quoted smt symbol
        else str

instance : ToString SmtSymbol where
  toString := SmtSymbol.toString

@[inline] private partial def SortExpr.toString (e : SortExpr) : String :=
  match e with
  | .SymbolSort nm => nm.toString
  | .ParamSort nm ps =>
      let sps := Array.foldl (fun acc a => s!"{acc} {SortExpr.toString a}") "" ps
      s!"({nm} {sps})"

instance : ToString SortExpr where
  toString := SortExpr.toString

@[inline] private def SortedVars.toString (sv : SortedVars) : String :=
   Array.foldl (fun acc a => s!"{acc}({a.1} {a.2})") "" sv

instance : ToString SortedVars where
  toString := SortedVars.toString

@[inline] private def SmtQualifiedIdent.toString (id : SmtQualifiedIdent) : String :=
  match id with
  | .SimpleIdent nm => nm.toString
  | .QualifiedIdent nm t => s!"(as {nm} {t})"

instance : ToString SmtQualifiedIdent where
  toString := SmtQualifiedIdent.toString

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
   | .BoolTerm b => if b then "true" else "false"
   | .BinTerm v => v
   | .HexTerm v => v
   | .StrTerm v => v
   | .SmtIdent nm => nm.toString
   | .AppTerm m args =>
       let sargs := Array.foldl (fun acc a => s!"{acc} {a.toString}") "" args
       let bline := if isIteApp m then "\n" else ""
       s!"({m}{sargs}){bline}"
   | .LetTerm bs body =>
       let sbs := Array.foldl (fun acc a => s!"{acc}({a.1} {a.2.toString})") "" bs
       s!"(let ({sbs}) {body.toString})\n"
   | .ForallTerm bs body =>
       s!"(forall ({bs})\n {body.toString})\n"
   | .ExistsTerm bs body =>
       s!"(exists ({bs})\n {body.toString})\n"
   | .LambdaTerm bs body =>
       s!"(lambda ({bs})\n {body.toString})\n"
   | .AnnotatedTerm t annot =>
       let sannot := Array.foldl (fun acc a => s!"{acc} {a.toString}") "" annot
       s!"(!{t.toString} {sannot})\n"
end

instance : ToString SmtAttribute where
  toString := SmtAttribute.toString

instance : ToString SmtTerm where
  toString := SmtTerm.toString

@[inline] private def SmtSelector.toString (s : SmtSelector) : String :=
  s!"({s.1} {s.2})"

instance : ToString SmtSelector where
  toString := SmtSelector.toString

@[inline] private def SmtConstructorDecl.toString (decl : SmtConstructorDecl) : String :=
  let selstr :=
    match decl.2 with
    | none => ""
    | some sel => Array.foldl (fun acc a => s!"{acc} {a}") "" sel
  s!"({decl.1} {selstr})\n"

instance : ToString SmtConstructorDecl where
  toString := SmtConstructorDecl.toString


@[inline] private def SmtDatatypeDecl.toString (d : SmtDatatypeDecl) : String :=
  let declstr := Array.foldl (fun acc d => s!"{acc} {d}" ) "" d.ctors
  match d.params with
  | none => s!"({declstr})"
  | some args =>
     let sargs := Array.foldl (fun acc a => s!"{acc} {a}" ) "" args
     s!"(par ({sargs}) ({declstr}))"

instance : ToString SmtDatatypeDecl where
  toString := SmtDatatypeDecl.toString

@[inline] private def SmtSortDecl.toString (d : SmtSortDecl) : String :=
  s!"({d.name} {d.arity})"

instance : ToString SmtSortDecl where
  toString := SmtSortDecl.toString

@[inline] private def SmtFunDecl.toString (d : SmtFunDecl) : String :=
  s!"({d.name} ({d.params}) {d.ret})"

instance : ToString SmtFunDecl where
  toString := SmtFunDecl.toString

@[inline] private def SmtCommand.toString (c : SmtCommand) : String :=
 match c with
 | .assertTerm t => s!"(assert {t})"
 | .checkSat => s!"(check-sat)"
 | .checkSatAssuming args =>
      let sargs := Array.foldl (fun acc a => s!"{acc} {a}") "" args
      s!"(check-sat-assuming ({sargs}))"
 | .declareConst nm t => s!"(declare-const {nm} {t})"
 | .declareDataType nm decl => s!"(declare-datatype {nm} {decl})"
 | .declareMutualDataTypes nm decl =>
    let nmstr := Array.foldl (fun acc d => s!"{acc} {d}") "" nm
    let declstr := Array.foldl (fun acc d => s!"{acc} {d}\n") "" decl
    s!"(declare-datatypes ({nmstr})\n ({declstr}))"
 | .declareFun nm args rt =>
     let sargs := Array.foldl (fun acc a => s!"{acc} {a}") "" args
     s!"(declare-fun {nm} ({sargs}) {rt})"
 | .defineFun isRec nm nargs rt body =>
    let defstr := if isRec then "define-fun-rec" else "define-fun"
    s!"({defstr} {nm} ({nargs}) {rt} {body})"
 | .defineFunsRec decls bodies =>
    let sdecls := Array.foldl (fun acc d => s!"{acc}\n{d}") "" decls
    let sbodies := Array.foldl (fun acc b => s!"{acc}\n{b}") "" bodies
    s!"(define-funs-rec ({sdecls})\n ({sbodies})\n)"
 | .declareSort nm arity => s!"(declare-sort {nm} {arity})"
 | .defineSort nm nargs body =>
    let sargs :=
       match nargs with
       | none => ""
       | some args => Array.foldl (fun acc s => s!"{acc} {s}") "" args
    s!"(define-sort {nm} ({sargs}) {body})"
 | .exitSmt => s!"(exit)"
 | .getModel => s!"(get-model)"
 | .getProof => s!"(get-proof)"
 | .evalTerm t => s!"(eval {t})"
 | .setLogic l => s!"(set-logic {l})"
 | .setOption opt v => s!"(set-option {opt} {v})"

instance : ToString SmtCommand where
  toString := SmtCommand.toString


end Solver.Smt
