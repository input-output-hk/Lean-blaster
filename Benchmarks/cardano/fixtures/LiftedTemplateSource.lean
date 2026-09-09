import PlutusCore.UPLC
open PlutusCore.UPLC.Term
namespace LiftedTemplateSource
set_option maxHeartbeats 0
set_option maxRecDepth 10000

#import_uplc sellNFT PlutusV2 single_cbor_hex "Tests/Scripts/SellNFT/sell_nft.flat"

def child (t : Term) (i : Nat) : Option Term :=
  match t, i with
  | .Lam _ b, 0 | .Force b, 0 | .Delay b, 0 => some b
  | .Apply f _, 0 => some f
  | .Apply _ a, 1 => some a
  | _, _ => none

def atPath (path : List Nat) (t : Term) : Option Term :=
  match path with
  | [] => some t
  | i :: rest => (child t i).bind (fun next => atPath rest next)

-- These certificates check the actual decoded production script, independently
-- of the diagnostic JSON export. They use neither native_decide nor axioms.
theorem LiftedSearch_in_script :
    (match sellNFT.script with | .Program _ body => atPath [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1] body) =
      some PlutusCore.UPLC.LiftedSearch.originalSelf := by rfl
#print axioms LiftedSearch_in_script

theorem LiftedMapSearch_in_script :
    (match sellNFT.script with | .Program _ body => atPath [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1] body) =
      some PlutusCore.UPLC.LiftedMapSearch.originalSelf := by rfl
#print axioms LiftedMapSearch_in_script

end LiftedTemplateSource
