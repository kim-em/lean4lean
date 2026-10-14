import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBinderComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRawChecking

/-! # Raw eta residuals stable under computation of the short endpoint

Fresh-argument reflection leaves a displayed eta pair or two lambdas with the
same body. Both forms have raw checking certificates, and both can follow any
computation of the short endpoint by computing the long endpoint further.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean Params

/-- The two literal outcomes of reflected fresh-argument computation. -/
inductive EtaResidual : ProofShape → ProofShape → Prop where
  | eta : EtaHead a b → EtaResidual a b
  | lam : EtaResidual (.lam A body) (.lam D body)

/-- A residual remains a raw common-mode checking certificate. -/
theorem EtaResidual.rawChecked [Params] (H : EtaResidual a b) :
    RawCheckedCompare Step true a b := by
  cases H with
  | eta H => exact .base (.etaL H)
  | lam => exact .lamCommon (.base .refl)

/-- Computing the short endpoint can be mirrored by further computation of the
long endpoint. No typed-source assumption is needed for this direction. -/
theorem EtaResidual.compute_right
    (hroot : ∀ {a b}, Step a b → ComputationalRoot a)
    (hweak : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (H : EtaResidual a b) (R : Compute Step b b') :
    ∃ a', Compute Step a a' ∧ EtaResidual a' b' := by
  cases H with
  | eta H =>
    cases H with
    | boundVar => exact ⟨_, .lam .refl (.app (R.liftN hweak) .refl), .eta .boundVar⟩
    | proof => exact ⟨_, .lam .refl (.app (R.liftN hweak) .refl), .eta .proof⟩
  | lam =>
    obtain ⟨D', body', rfl, _, RB⟩ := R.lam_inv hroot
    exact ⟨_, .lam .refl RB, .lam⟩

end Lean4Lean.VEnv.Strengthening.ProofShape
