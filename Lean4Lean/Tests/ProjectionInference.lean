import Lean4Lean.TypeChecker

namespace Lean4Lean.Tests.ProjectionInference

open Lean Lean4Lean TypeChecker TypeChecker.Inner

structure Wrap (alpha : Type u) where
  value : alpha
  tag : Bool

run_meta do
  let env := (← getEnv).toKernelEnv
  let wrapNat := mkApp (mkConst ``Wrap [.zero]) (mkConst ``Nat)
  let constructor := mkAppN (mkConst ``Wrap.mk [.zero])
    #[mkConst ``Nat, mkNatLit 3, mkConst ``false]
  match TypeChecker.M.run env .safe {} [] {}
      (inferProj ``Wrap 0 constructor wrapNat).run with
  | .error exception =>
      throwError "projection inference failed: {
        ← (exception.toMessageData {}).toString}"
  | .ok type =>
      unless type == mkConst ``Nat do
        throwError "projection inference returned the wrong type"

end Lean4Lean.Tests.ProjectionInference
