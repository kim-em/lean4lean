import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextApplicationBase
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaClassification

/-! # Raw checking support for application at a common Pi type

Common lambda bodies substitute directly in raw syntax. Displayed eta contracts
at application after typing fixes whether the argument is a proof marker.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- At a common Pi type, inferred raw function comparison applies to a shared
argument and retains a raw checking certificate. -/
theorem proofErase_raw_apply_inferred (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (H : ProofShape.RawCheckedCompare Step false (proofErase Γ f) (proofErase Γ g)) :
    ProofShape.RawCheckedCompare Step true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  classical
  have hfx := HasType.app hf hx
  have hgx := HasType.app hg hx
  by_cases hp : IsProof Γ (.app f x)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 (isProof_of_common_type hΓ hfx hgx hp)]
    exact .base .refl
  · have hp' : ¬ IsProof Γ (.app g x) := fun h => hp (isProof_of_common_type hΓ hgx hfx h)
    rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hp,
      show proofErase Γ (.app g x) = .app _ _ from if_neg hp']
    exact .app H (.base .refl)

/-- Common lambda bodies can be applied without comparing their annotations.
The substituted certificate is raw, and both outer redexes contract by beta. -/
theorem proofErase_raw_apply_lam_shapes
    (hsubst : ∀ {a b} {τ : ProofShape.Subst}, Step a b → Step (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (Ef : proofErase Γ f = .lam D b) (Eg : proofErase Γ g = .lam D' b')
    (H : ProofShape.RawCheckedCompare Step true b b') :
    ProofShape.RawCheckedCompare Step true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  classical
  have hfx := HasType.app hf hx
  have hgx := HasType.app hg hx
  by_cases hp : IsProof Γ (.app f x)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 (isProof_of_common_type hΓ hfx hgx hp)]
    exact .base .refl
  · have hp' : ¬ IsProof Γ (.app g x) := fun h => hp (isProof_of_common_type hΓ hgx hfx h)
    rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hp,
      show proofErase Γ (.app g x) = .app _ _ from if_neg hp', Ef, Eg]
    apply ProofShape.RawCheckedCompare.compute (.beta .beta) (.beta .beta)
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
      H.subst hsubst (σ := ProofShape.Subst.one (proofErase Γ x))

/-- Substituting a typed argument into the classified fresh eta slot gives its
actual erasure, including the proof-domain case. -/
theorem proofErase_eta_argument_inst (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hx : env.HasType univs Γ x A) :
    (ProofShape.etaArgument u).inst (proofErase Γ x) = proofErase Γ x := by
  classical
  unfold ProofShape.etaArgument
  split
  · rename_i hu
    have hp : IsProof Γ x := ⟨A, hx,
      (IsDefEq.sortDF (hA.sort_r henv hΓ) (by trivial) hu).defeq hA⟩
    exact (proofErase_eq_proof.2 hp).symm
  · simp [ProofShape.inst, ProofShape.liftN_zero]

/-- Applying a displayed eta guard to a shared typed argument gives an actual
raw beta path from the long application to the short application. -/
theorem proofErase_raw_apply_eta_beta (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (H : ProofShape.EtaHead (proofErase Γ f) (proofErase Γ g)) :
    ProofShape.BetaRed (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  classical
  have hfx := HasType.app hf hx
  have hgx := HasType.app hg hx
  by_cases hp : IsProof Γ (.app f x)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 (isProof_of_common_type hΓ hfx hgx hp)]
    exact .refl
  · have hp' : ¬ IsProof Γ (.app g x) := fun h => hp (isProof_of_common_type hΓ hgx hfx h)
    obtain ⟨D, C, u, hD, hgD, _, EF⟩ := proofErase_eta_head_classified hΓ hf hg H
    have hxD := argument_at_displayed_domain hΓ hg hgD hx
    rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hp,
      show proofErase Γ (.app g x) = .app _ _ from if_neg hp', EF]
    have EL (e : ProofShape) : (e.liftN 1).inst (proofErase Γ x) = e := by
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
        ProofShape.lift_subst_cons, ProofShape.subst_id]
    simpa only [ProofShape.inst, EL, proofErase_eta_argument_inst hΓ hD hxD] using
      (ProofShape.BetaRed.beta (A := proofErase Γ D)
        (b := .app ((proofErase Γ g).liftN 1) (ProofShape.etaArgument u)) (a := proofErase Γ x))

end Lean4Lean.VEnv.Strengthening
