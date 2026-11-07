import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEtaBodyResidual

/-! # Remove native eta at an actual proof argument

The typed short application already supplies the inhabitant needed to read
the erased eta body below its binder. Its body is an unused-binder lift, so
counted descent handles arbitrary body work and changing annotations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_spine_head from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Native eta immediately applied to a proof marker can be removed through
arbitrary subsequent computation. The exact exposed output is retained and
the count does not increase; no substitution closure of guards is assumed. -/
theorem pi_inert_proof_eta_spine_count_eliminate_nonlambda
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps f (.proof :: pending)))
    (H : NativeEtaExpansion Guard Δ f target)
    (RT : ScopedComputeCount (PiInertStage D n) cost Δ
      (ProofShape.mkApps target (.proof :: pending)) out)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest) :
    ∃ k, k ≤ cost ∧ ScopedComputeCount (PiInertStage D n) k Δ
      (ProofShape.mkApps f (.proof :: pending)) out := by
  have HTapp : TypedSource Δ (.app f .proof) := typed_spine_head HT
  obtain ⟨Γ, e, T, hΓ, rfl, ht, Ee⟩ := HTapp
  obtain ⟨f₀, x₀, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
  obtain ⟨A₀, B₀, hf, hx⟩ := ht.app_inv henv hΓ
  rw [← Ef] at H
  cases H with
  | intro RN SD =>
    rename_i rawA rawB u
    have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨A, B, hfA, EA, _⟩ := proofErase_scoped_recovered_pi_descend hguard hΓ hΓ W hf
      (by simpa only [ProofShape.liftN_zero] using RN)
    obtain ⟨_, hPi⟩ := hfA.isType henv hΓ
    obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
    have hA := (EA ▸ SD).descend hΓ hΓ W hA
    have hxA := argument_at_displayed_domain hΓ hf hfA hx
    obtain ⟨P, hxP, hP⟩ := proofErase_eq_proof.1 Ex
    have hA0 := ((hxA.uniqU henv hΓ hxP).of_r henv hΓ hP).hasType.1
    have hu := (hA.uniqU henv hΓ hA0).sort_inv henv hΓ
    have EB : ProofShape.app ((proofErase Γ f₀).liftN 1) (etaArgument u) =
        (proofErase Γ (.app f₀ x₀)).liftN 1 := by
      rw [Ee, ← Ef]
      simp only [etaArgument, if_pos hu, ProofShape.liftN]
    have RT' : ScopedComputeCount (PiInertStage D n) cost (proofEraseCtx Γ)
        (ProofShape.mkApps (.app (.lam (proofErase Γ A)
          ((proofErase Γ (.app f₀ x₀)).liftN 1)) .proof) pending) out := by
      simpa only [ProofShape.mkApps, ← EA, ProofShape.liftN_zero, ← EB] using RT
    obtain ⟨k, hk, R⟩ := pi_inert_constant_spine_count_eliminate heq hs hΓ hA ht
      hout RT'
    exact ⟨k, hk, by simpa only [Ee, ProofShape.mkApps] using R⟩

/-- The carrier-exposure instance of proof-argument eta elimination. The more
general result also applies to constructor values and other exposed outputs. -/
theorem pi_inert_proof_eta_spine_count_eliminate
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps f (.proof :: pending)))
    (H : NativeEtaExpansion Guard Δ f target)
    (RT : ScopedComputeCount (PiInertStage D n) cost Δ
      (ProofShape.mkApps target (.proof :: pending)) out)
    (HE : CarrierExposure out) :
    ∃ k, k ≤ cost ∧ ScopedComputeCount (PiInertStage D n) k Δ
      (ProofShape.mkApps f (.proof :: pending)) out :=
  pi_inert_proof_eta_spine_count_eliminate_nonlambda heq hs hguard HT H RT HE.not_lambda_spine

end Lean4Lean.VEnv.Strengthening
