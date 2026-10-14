import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextApplicationBase

/-! # Application of contextual function comparisons

Common-mode certificates apply to a shared typed argument. Computation is
replayed at the common Pi type, and recursive eta bodies are instantiated.
This does not assert transitivity or substitution of distinct compared terms.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- A contextual eta-body rule with raw endpoints applies to the same argument.
The domain-sort witness identifies the fresh variable's exact erasure. -/
theorem proofErase_context_apply_eta_shape
    (hsubst : ∀ {a b} {τ : ProofShape.Subst}, Step a b → Step (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (Ef : proofErase Γ f = .lam D b)
    (SD : ProofShape.DomainSort (proofEraseCtx Γ) D u)
    (H : ProofShape.ContextCompare Step (D :: proofEraseCtx Γ) true b
      (.app ((proofErase Γ g).liftN 1) (ProofShape.etaArgument u))) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  obtain ⟨D₀, b₀, rfl, hn, ED, Eb⟩ := erase_lam_inv Ef
  obtain ⟨⟨_, hD₀⟩, C, hb⟩ := hf.lam_inv henv hΓ
  have W : Ctx.LiftN 0 0 Γ Γ := .zero []
  have hD := ProofShape.DomainSort.descend
    (by simpa only [ProofShape.liftN_zero, ED] using SD) hΓ hΓ W hD₀
  have hfPi := HasType.lam hD hb
  have hgPi := hg.defeqU_r henv hΓ (hf.uniqU henv hΓ hfPi)
  have hxD := argument_at_displayed_domain hΓ hf hfPi hx
  have hng : ¬ IsProof Γ g := fun hp => hn (isProof_of_common_type hΓ hg hf hp)
  have Eη := proofErase_eta_body hΓ hD hgPi hng
  apply proofErase_context_apply_eta_body hsubst hΓ hD hb hgPi hxD
  simpa only [proofEraseCtx, ED, Eb, Eη] using H

/-- Every contextual comparison of functions at a common Pi type applies to
one shared typed argument. The output is a contextual common-mode certificate,
including when computations occur recursively in the input certificate. -/
theorem proofErase_context_apply_same
    (hstep : ErasedPrimitiveDescent Step)
    (hsubst : ∀ {a b} {τ : ProofShape.Subst}, Step a b → Step (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (H : ProofShape.ContextCompare Step (proofEraseCtx Γ) mode (proofErase Γ f) (proofErase Γ g)) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  generalize EΔ : proofEraseCtx Γ = Δ at H
  generalize Ef : proofErase Γ f = sf at H
  generalize Eg : proofErase Γ g = sg at H
  induction H generalizing f g A B with
  | base H =>
    rw [← EΔ]
    exact proofErase_rawChecked_apply_same hstep hsubst hΓ hf hg hx (by rwa [Ef, Eg])
  | app Hf Hx =>
    rw [← EΔ]
    exact proofErase_context_apply_inferred hΓ hf hg hx (by rw [EΔ, Ef, Eg]; exact .app Hf Hx)
  | proj H =>
    rw [← EΔ]
    exact proofErase_context_apply_inferred hΓ hf hg hx (by rw [EΔ, Ef, Eg]; exact .proj H)
  | lam HD Hb =>
    rw [← EΔ]
    exact proofErase_context_apply_lam_shapes hsubst hΓ hf hg hx Ef Eg (by rw [EΔ]; exact Hb.common)
  | forallE HD HB =>
    rw [← EΔ]
    exact proofErase_context_apply_inferred hΓ hf hg hx (by rw [EΔ, Ef, Eg]; exact .forallE HD HB)
  | lamSorted SD SD' HD Hb =>
    rw [← EΔ]
    exact proofErase_context_apply_lam_shapes hsubst hΓ hf hg hx Ef Eg (by rw [EΔ]; exact Hb.common)
  | forallSorted SD SD' HD SB SB' HB =>
    rw [← EΔ]
    exact proofErase_context_apply_inferred hΓ hf hg hx
      (by rw [EΔ, Ef, Eg]; exact .forallSorted SD SD' HD SB SB' HB)
  | lamCommon Hb =>
    rw [← EΔ]
    exact proofErase_context_apply_lam_shapes hsubst hΓ hf hg hx Ef Eg (by rw [EΔ]; exact Hb)
  | etaBodyL SD Hb =>
    rw [← EΔ]
    exact proofErase_context_apply_eta_shape hsubst hΓ hf hg hx Ef
      (by rwa [EΔ]) (by rwa [EΔ, Eg])
  | etaBodyR SD Hb =>
    rw [← EΔ]
    exact .symm (proofErase_context_apply_eta_shape hsubst hΓ hg hf hx Eg
      (by rwa [EΔ]) (by rw [EΔ, Ef]; exact .symm Hb))
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
      (ih HF.hasType.2 HG.hasType.2 hx EΔ EF EG)
  | symm H ih => exact .symm (ih hg hf hx EΔ Eg Ef)

end Lean4Lean.VEnv.Strengthening
