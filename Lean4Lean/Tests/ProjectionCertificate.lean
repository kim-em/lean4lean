import Lean4Lean.ProjectionCertificate

namespace Lean4Lean.Tests.ProjectionCertificate

open Lean Lean4Lean TypeChecker TypeChecker.Inner

structure Wrap (alpha : Type u) where
  value : alpha
  tag : Bool

/- The native generator is untrusted but its ordinary checked certificate
accepts the canonical closed projection it produces. -/
run_meta do
  let env := (← getEnv).toKernelEnv
  let wrapNat := mkApp (mkConst ``Wrap [.zero]) (mkConst ``Nat)
  let constructor := mkAppN (mkConst ``Wrap.mk [.zero])
    #[mkConst ``Nat, mkNatLit 3, mkConst ``false]
  match TypeChecker.M.run env .safe {} [] {}
      (inferProjCertified ``Wrap 0 constructor wrapNat).run with
  | .error exception =>
      throwError "projection certification failed: {
        ← (exception.toMessageData {}).toString}"
  | .ok certificate =>
      unless certificate.projection.type == mkConst ``Nat do
        throwError "projection certificate retained the wrong legacy type"
      unless projectionFree certificate.candidate do
        throwError "projection certificate candidate retained a projection"

end Lean4Lean.Tests.ProjectionCertificate
