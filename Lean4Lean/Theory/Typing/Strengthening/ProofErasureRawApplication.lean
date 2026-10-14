import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRawApplicationSupport

/-! # Same-argument application preserves raw checking certificates

Typed replay handles computation nodes; lambda-body substitution and displayed
eta beta contraction retain raw certificates throughout. No contextual eta rule
or transitivity premise is introduced.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- The original raw comparison applies to a shared typed argument. This holds
in either mode; common lambda bodies are instantiated instead of promoted. -/
theorem proofErase_compare_raw_apply_same
    (hstep : ErasedPrimitiveDescent Step)
    (hsubst : ∀ {a b} {τ : ProofShape.Subst}, Step a b → Step (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (H : ProofShape.Compare Step mode (proofErase Γ f) (proofErase Γ g)) :
    ProofShape.RawCheckedCompare Step true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  generalize Ef : proofErase Γ f = sf at H
  generalize Eg : proofErase Γ g = sg at H
  induction H generalizing f g A B with
  | refl =>
    exact proofErase_raw_apply_inferred hΓ hf hg hx (.base (by rw [Ef, Eg]; exact .refl))
  | sort H =>
    exact proofErase_raw_apply_inferred hΓ hf hg hx (.base (by rw [Ef, Eg]; exact .sort H))
  | const H =>
    exact proofErase_raw_apply_inferred hΓ hf hg hx (.base (by rw [Ef, Eg]; exact .const H))
  | app Hf Hx =>
    exact proofErase_raw_apply_inferred hΓ hf hg hx (.base (by rw [Ef, Eg]; exact .app Hf Hx))
  | proj H =>
    exact proofErase_raw_apply_inferred hΓ hf hg hx (.base (by rw [Ef, Eg]; exact .proj H))
  | lam HD Hb =>
    exact proofErase_raw_apply_lam_shapes hsubst hΓ hf hg hx Ef Eg (.base Hb.common)
  | forallE HD HB =>
    exact proofErase_raw_apply_inferred hΓ hf hg hx (.base (by rw [Ef, Eg]; exact .forallE HD HB))
  | etaL H => exact .compute (.beta (proofErase_raw_apply_eta_beta hΓ hf hg hx (by rwa [Ef, Eg]))) .refl (.base .refl)
  | etaR H => exact .compute .refl (.beta (proofErase_raw_apply_eta_beta hΓ hg hf hx (by rwa [Ef, Eg]))) (.base .refl)
  | structL H => exact (proofErase_function_not_structure_eta hΓ hf (Ef ▸ H)).elim
  | structR H => exact (proofErase_function_not_structure_eta hΓ hg (Eg ▸ H)).elim
  | etaLams HD H =>
    exact proofErase_raw_apply_inferred hΓ hf hg hx (.base (by rw [Ef, Eg]; exact .etaLams HD H))
  | compute Rf Rg HC ih =>
    have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨f', HF, EF⟩ := proofErase_compute_typed_descend hstep hΓ hΓ W hf
      (by simpa only [ProofShape.liftN_zero, Ef] using Rf)
    obtain ⟨g', HG, EG⟩ := proofErase_compute_typed_descend hstep hΓ hΓ W hg
      (by simpa only [ProofShape.liftN_zero, Eg] using Rg)
    simp only [ProofShape.liftN_zero] at EF EG
    exact .compute
      (proofErase_compute_apply_same hΓ hf HF.hasType.2 hx (by rwa [Ef, EF]))
      (proofErase_compute_apply_same hΓ hg HG.hasType.2 hx (by rwa [Eg, EG]))
      (ih HF.hasType.2 HG.hasType.2 hx EF EG)

/-- Oracle-free common lambda checking also preserves same-argument application.
Every computation node is replayed at the actual common Pi type. -/
theorem proofErase_rawChecked_raw_apply_same
    (hstep : ErasedPrimitiveDescent Step)
    (hsubst : ∀ {a b} {τ : ProofShape.Subst}, Step a b → Step (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (H : ProofShape.RawCheckedCompare Step mode (proofErase Γ f) (proofErase Γ g)) :
    ProofShape.RawCheckedCompare Step true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  generalize Ef : proofErase Γ f = sf at H
  generalize Eg : proofErase Γ g = sg at H
  induction H generalizing f g A B with
  | base H => exact proofErase_compare_raw_apply_same hstep hsubst hΓ hf hg hx (by rwa [Ef, Eg])
  | app Hf Hx =>
    exact proofErase_raw_apply_inferred hΓ hf hg hx (by rw [Ef, Eg]; exact .app Hf Hx)
  | proj H =>
    exact proofErase_raw_apply_inferred hΓ hf hg hx (by rw [Ef, Eg]; exact .proj H)
  | lam HD Hb =>
    exact proofErase_raw_apply_lam_shapes hsubst hΓ hf hg hx Ef Eg Hb.common
  | lamCommon Hb =>
    exact proofErase_raw_apply_lam_shapes hsubst hΓ hf hg hx Ef Eg Hb
  | forallE HD HB =>
    exact proofErase_raw_apply_inferred hΓ hf hg hx (by rw [Ef, Eg]; exact .forallE HD HB)
  | compute Rf Rg HC ih =>
    have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨f', HF, EF⟩ := proofErase_compute_typed_descend hstep hΓ hΓ W hf
      (by simpa only [ProofShape.liftN_zero, Ef] using Rf)
    obtain ⟨g', HG, EG⟩ := proofErase_compute_typed_descend hstep hΓ hΓ W hg
      (by simpa only [ProofShape.liftN_zero, Eg] using Rg)
    simp only [ProofShape.liftN_zero] at EF EG
    exact .compute
      (proofErase_compute_apply_same hΓ hf HF.hasType.2 hx (by rwa [Ef, EF]))
      (proofErase_compute_apply_same hΓ hg HG.hasType.2 hx (by rwa [Eg, EG]))
      (ih HF.hasType.2 HG.hasType.2 hx EF EG)

end Lean4Lean.VEnv.Strengthening
