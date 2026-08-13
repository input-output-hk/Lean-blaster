import Lean
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Blaster

/-! ## Const-expression accessors for the `Prop` simplification rules -/

def mkBlasterAndLeft : TranslateEnvT Expr := mkExpr (mkConst ``And.left)

def mkBlasterAndRight : TranslateEnvT Expr := mkExpr (mkConst ``And.right)

end Blaster
