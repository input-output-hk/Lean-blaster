import Blaster.Optimize.Env.GroundValue
import Blaster.Optimize.Rewriting.OptimizeList

open Lean Meta
namespace Blaster.Optimize

/-- Run the existing lookup rules before visiting list elements. Only a visible
    list spine is considered; the selected result is optimized by the caller. -/
def reduceListLookupBeforeArgs? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  unless f.isConstOf ``List.get?Internal && args.size == 3 do return none
  let list := args[1]!
  unless list.isAppOfArity ``List.cons 3 || list.isAppOfArity ``List.nil 1 do return none
  let index := (← groundConstructorValue? args[2]!).getD args[2]!
  let result ← optimizeListGet f (args.set! 2 index)
  -- This caller always revisits the rewritten expression, including finite lists.
  resetRestart
  return some result

end Blaster.Optimize
