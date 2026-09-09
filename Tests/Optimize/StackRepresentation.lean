import Blaster.Optimize.OptimizeStack

open Blaster.Optimize

namespace Tests.StackRepresentation

-- These conversions are only used to check that the fused representation
-- preserves every frame payload and the complete continuation order.
def toList : OptimizeStack → List OptimizeFrame
 | .nil => []
 | .InitOptimizeExpr e mvarDecls tail => .InitOptimizeExpr e mvarDecls :: toList tail
 | .InitOptimizeReturn e isGlobal mvarDecls tail => .InitOptimizeReturn e isGlobal mvarDecls :: toList tail
 | .RecFunDefWaitForStorage args instApp subsInts params startCtxId tail => .RecFunDefWaitForStorage args instApp subsInts params startCtxId :: toList tail
 | .RecFunDefStorage args instApp subsInts params optBody startCtxId tail => .RecFunDefStorage args instApp subsInts params optBody startCtxId :: toList tail
 | .ForallWaitForType n bi body tail => .ForallWaitForType n bi body :: toList tail
 | .ForallWaitForBody x t hctx isProp tail => .ForallWaitForBody x t hctx isProp :: toList tail
 | .AppWaitForConst args tail => .AppWaitForConst args :: toList tail
 | .OptimizeMatchInfoWaitForInst f args startArgIdx pInfo mInfo tail => .OptimizeMatchInfoWaitForInst f args startArgIdx pInfo mInfo :: toList tail
 | .AppOptimizeImplicitArgs f args idx startArgIdx stopIdx pInfo prevInApp tail => .AppOptimizeImplicitArgs f args idx startArgIdx stopIdx pInfo prevInApp :: toList tail
 | .SpecializeWaitForArg f args argIdx startIdx pInfo prevInApp tail => .SpecializeWaitForArg f args argIdx startIdx pInfo prevInApp :: toList tail
 | .SpecializeReady f args startIdx pInfo prevInApp tail => .SpecializeReady f args startIdx pInfo prevInApp :: toList tail
 | .AppOptimizeExplicitArgs f args idx stopIdx pInfo mInfo prevInApp tail => .AppOptimizeExplicitArgs f args idx stopIdx pInfo mInfo prevInApp :: toList tail
 | .InitNonFunOptimizeArgs f args idx stopIdx tail => .InitNonFunOptimizeArgs f args idx stopIdx :: toList tail
 | .NonFunOptimizeArgs f args idx stopIdx prevInCtor tail => .NonFunOptimizeArgs f args idx stopIdx prevInCtor :: toList tail
 | .DiteChoiceWaitForCond f args pInfo prevInApp tail => .DiteChoiceWaitForCond f args pInfo prevInApp :: toList tail
 | .MatchChoiceOptimizeDiscrs f args pInfo idx mInfo prevInApp tail => .MatchChoiceOptimizeDiscrs f args pInfo idx mInfo prevInApp :: toList tail
 | .LambdaWaitForType n bi body tail => .LambdaWaitForType n bi body :: toList tail
 | .LambdaWaitForBody x hctx inDite startCtxId tail => .LambdaWaitForBody x hctx inDite startCtxId :: toList tail
 | .MatchRhsLambdaWaitForType n bi body tail => .MatchRhsLambdaWaitForType n bi body :: toList tail
 | .MatchRhsLambdaNext e tail => .MatchRhsLambdaNext e :: toList tail
 | .MatchRhsLambdaWaitForBody x tail => .MatchRhsLambdaWaitForBody x :: toList tail
 | .MatchLhsSkipForallType e tail => .MatchLhsSkipForallType e :: toList tail
 | .MatchLhsForallWaitForBody e tail => .MatchLhsForallWaitForBody e :: toList tail
 | .MatchAltWaitForExpr params hctx idx matchInst tail => .MatchAltWaitForExpr params hctx idx matchInst :: toList tail
 | .LetWaitForValue body tail => .LetWaitForValue body :: toList tail
 | .MDataRecCallWaitForExpr data tail => .MDataRecCallWaitForExpr data :: toList tail
 | .ProjWaitForExpr n idx tail => .ProjWaitForExpr n idx :: toList tail

def ofList : List OptimizeFrame → OptimizeStack
 | [] => .nil
 | frame :: tail => frame ::: ofList tail

theorem toList_push (frame : OptimizeFrame) (tail : OptimizeStack) :
    toList (frame ::: tail) = frame :: toList tail := by
  cases frame <;> rfl

theorem toList_ofList (frames : List OptimizeFrame) : toList (ofList frames) = frames := by
  induction frames with
  | nil => rfl
  | cons frame tail ih => simp only [ofList, toList_push, ih]

theorem ofList_toList (stack : OptimizeStack) : ofList (toList stack) = stack := by
  induction stack <;> simp_all only [toList, ofList, OptimizeStack.push]

#print axioms toList_ofList
#print axioms ofList_toList

end Tests.StackRepresentation
