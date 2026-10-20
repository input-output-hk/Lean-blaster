import Blaster

namespace Test.FiniteFieldInterfaces

open Lean Meta Blaster.Optimize

private def smallModulus : Nat := 2 * 3 + 1
private def largeModulus : Nat := 2 ^ 381 - 19

/-! Closed modulus recognition is not a primality check or a field encoding.
    In particular, zero, one and composite bounds must remain distinct, and an
    open expression must not acquire a context-dependent cached modulus. -/
run_meta do
  let check : TranslateEnvT Unit := do
    discard <| Optimize.main (mkNatLit 0)
    let expect (e : Expr) (n : Nat) : TranslateEnvT Unit := do
      unless (← getNatModulus? e) == some n do
        throwError "incorrect closed Nat modulus for {e}; expected {n}"
    expect (mkNatLit 0) 0
    expect (mkNatLit 1) 1
    expect (mkNatLit 6) 6
    expect (mkConst ``smallModulus) 7
    expect (mkConst ``largeModulus) (2 ^ 381 - 19)
    -- Repeated lookups and a different modulus cannot alias one another.
    expect (mkConst ``smallModulus) 7
    expect (mkNatLit 11) 11
    expect (mkConst ``largeModulus) (2 ^ 381 - 19)
    let projected := mkProj ``OfNat 0 (mkApp (mkConst ``instOfNatNat) (mkNatLit 7))
    expect projected 7
    unless (← getNatModulus? (mkConst ``Bool.true)).isNone do
      throwError "non-Nat value accepted as a modulus"
    unless (← getNatModulus? (mkBVar 0)).isNone do
      throwError "loose bound variable accepted as a modulus"
    withLocalDeclD `n (mkConst ``Nat) fun n => do
      unless (← getNatModulus? n).isNone do
        throwError "symbolic modulus accepted"
      let openZero := mkApp2 (mkConst ``Nat.sub) n n
      unless (← getNatModulus? openZero).isNone do
        throwError "open expression normalized into a closed modulus"
    let unknown ← mkFreshExprMVar (mkConst ``Nat)
    unless (← getNatModulus? unknown).isNone do
      throwError "metavariable accepted as a modulus"
    unknown.mvarId!.assign (mkNatLit 13)
    expect (← instantiateMVars unknown) 13
  discard <| check.run (default : TranslateEnv)

end Test.FiniteFieldInterfaces
