import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedScopedPairedSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBinderComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaInstantiation

/-! # Full inferred-lambda checking survives paired head beta

The body comparison may contain arbitrary recursive eta and structure-field
checking. Both functions may compute and change their written annotations before
the structural check. Only inferred comparison of the two argument images is
needed, without a native recovery or computation-join premise on those images.
Primitive computations require typed substitution and head preservation; the
primitive-free corollary discharges both interfaces.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private lambda_common_context from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
open private empty_descent from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedScopedPairedSubstitution
variable [Params]

private theorem body_inst
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hsubst : ErasedPrimitiveSubstitutionTo Source Step)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x P) (hy : env.HasType univs Γ y P)
    (hf : env.HasType univs Γ f (.forallE P T)) (hg : env.HasType univs Γ g (.forallE P T))
    (Ef : proofErase Γ f = .lam A b) (Eg : proofErase Γ g = .lam D c)
    (HX : CarrierAlignedCompare Step (proofEraseCtx Γ) false (proofErase Γ x) (proofErase Γ y))
    (HB : ScopedCompare Source (A :: proofEraseCtx Γ) false b c) :
    CarrierAlignedCompare Step (proofEraseCtx Γ) false (b.inst (proofErase Γ x)) (c.inst (proofErase Γ y)) := by
  obtain ⟨A₀, b₀, rfl, _, EA, Eb⟩ := erase_lam_inv Ef
  obtain ⟨D₀, c₀, rfl, _, ED, Ec⟩ := erase_lam_inv Eg
  obtain ⟨u, C, hA, hD, hb, hc, Ectx⟩ := lambda_common_context hΓ hf hg
  rw [Ectx] at Ec
  have hxA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hx
  have hyA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hy
  have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have H := proofErase_carrier_aligned_scoped_paired_substitution_with_primitives
    hsource hsubst hstep hrename (CarrierAlignedSubstitution.inst hΓA hxA hyA HX) hb hc
    (by simpa only [proofEraseCtx, EA, Eb, Ec] using HB)
  simp only [← VExpr.inst_eq] at H
  rw [proofErase_instN hΓA hxA Ctx.InstN.zero hb, proofErase_instN hΓA hyA Ctx.InstN.zero hc, Eb, Ec] at H
  exact H

private theorem inferred_lambdas
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hhead : ∀ {Δ a b}, Source Δ a b → PrimitiveHead a)
    (hsubst : ErasedPrimitiveSubstitutionTo Source Step)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ))
    (H : ScopedCompare Source Δ mode sa sb) (hm : mode = false)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x P) (hy : env.HasType univs Γ y P)
    (hf : env.HasType univs Γ f (.forallE P T)) (hg : env.HasType univs Γ g (.forallE P T))
    (EΓ : proofEraseCtx Γ = Δ) (Ef : proofErase Γ f = sa) (Eg : proofErase Γ g = sb)
    (EL : sa = .lam A b) (ER : sb = .lam D c)
    (HX : CarrierAlignedCompare Step (proofEraseCtx Γ) false (proofErase Γ x) (proofErase Γ y)) :
    CarrierAlignedCompare Step (proofEraseCtx Γ) false (b.inst (proofErase Γ x)) (c.inst (proofErase Γ y)) := by
  induction H generalizing Γ x y P T f g A b D c with
  | leaf H =>
    cases hm
    cases H with
    | refl =>
      have E := (ProofShape.lam.inj (EL.symm.trans ER)).2
      apply body_inst hsource hsubst hstep hrename hΓ hx hy hf hg (Ef.trans EL) (Eg.trans ER) HX
      rw [E]
      exact .leaf .refl
    | sort | const => cases EL
  | lam HD HB ihD ihB | lamSorted SD SD' HD HB ihD ihB =>
    cases hm
    cases EL
    cases ER
    exact body_inst hsource hsubst hstep hrename hΓ hx hy hf hg Ef Eg HX (by simpa only [EΓ] using HB)
  | etaLams HD HE ihD =>
    cases hm
    cases EL
    cases ER
    obtain ⟨A₀, b₀, rfl, _, EA, Eb⟩ := erase_lam_inv Ef
    obtain ⟨D₀, c₀, rfl, _, ED, Ec⟩ := erase_lam_inv Eg
    apply body_inst hsource hsubst hstep hrename hΓ hx hy hf hg Ef Eg HX
    rcases HE with HE | HE
    · have R := proofErase_eta_lambda_bodies_beta hΓ hf hg (by simpa only [Ef, Eg] using HE)
      rw [Eb, Ec] at R
      exact .compute (.beta R) .refl (.leaf .refl)
    · have R := proofErase_eta_lambda_bodies_beta hΓ hg hf (by simpa only [Ef, Eg] using HE)
      rw [Eb, Ec] at R
      exact .compute .refl (.beta R) (.leaf .refl)
  | compute RF RG HC ih =>
    obtain ⟨A₀, b₀, rfl, hnF, EA, Eb⟩ := erase_lam_inv (Ef.trans EL)
    obtain ⟨D₀, c₀, rfl, hnG, ED, Ec⟩ := erase_lam_inv (Eg.trans ER)
    obtain ⟨⟨u, hA⟩, B, hb⟩ := hf.lam_inv henv hΓ
    obtain ⟨⟨v, hD⟩, C, hc⟩ := hg.lam_inv henv hΓ
    have hxA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hx
    have hyD := argument_at_displayed_domain hΓ hg (HasType.lam hD hc) hy
    have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hΓD : OnCtx (D₀ :: Γ) (env.IsType univs) := ⟨hΓ, v, hD⟩
    obtain ⟨A', b', ELF, RB⟩ := proofErase_scoped_lambda_inst_compute hsource hhead hsubst
      hΓ hA hb hxA hnF (by simpa only [EΓ, EA, Eb, EL] using RF)
    obtain ⟨D', c', ERG, RC⟩ := proofErase_scoped_lambda_inst_compute hsource hhead hsubst
      hΓ hD hc hyD hnG (by simpa only [EΓ, ED, Ec, ER] using RG)
    rw [proofErase_instN hΓA hxA Ctx.InstN.zero hb, Eb] at RB
    rw [proofErase_instN hΓD hyD Ctx.InstN.zero hc, Ec] at RC
    obtain ⟨f', HF, Ef'⟩ := proofErase_scoped_compute_realize hsource hΓ hf EΓ Ef RF
    obtain ⟨g', HG, Eg'⟩ := proofErase_scoped_compute_realize hsource hΓ hg EΓ Eg RG
    exact .compute RB RC (ih hm hΓ hx hy HF.hasType.2 HG.hasType.2 EΓ Ef' Eg' ELF ERG HX)
  | symm HC ih => exact (ih hm hΓ hy hx hg hf EΓ Eg Ef ER EL HX.symm).symm
  | app | proj | forallE | forallSorted => cases EL
  | lamCommon | etaBodyL | etaBodyR | structFields => cases hm

/-- Inferred comparison of two actual lambda functions survives
paired head beta at nonjoining inferred-related argument images. Every recursive
source comparison constructor is covered, including eta and structure fields. -/
theorem proofErase_carrier_aligned_scoped_head_beta_with_primitives
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hhead : ∀ {Δ a b}, Source Δ a b → PrimitiveHead a)
    (hsubst : ErasedPrimitiveSubstitutionTo Source Step)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x P) (hy : env.HasType univs Γ y P)
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam D c) (.forallE P (.sort .zero)))
    (HX : CarrierAlignedCompare Step (proofEraseCtx Γ) false (proofErase Γ x) (proofErase Γ y))
    (H : ScopedCompare Source (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam D c))) :
    CarrierAlignedCompare Step (proofEraseCtx Γ) true (proofErase Γ (b.inst x)) (proofErase Γ (c.inst y)) := by
  have Ef : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) :=
    if_neg (not_isProof_function_to_sort hΓ hf)
  have Eg : proofErase Γ (.lam D c) = .lam (proofErase Γ D) (proofErase (D :: Γ) c) :=
    if_neg (not_isProof_function_to_sort hΓ hg)
  have HC := inferred_lambdas hsource hhead hsubst hstep hrename H rfl hΓ hx hy hf hg rfl rfl rfl Ef Eg HX
  obtain ⟨⟨u, hA⟩, B, hb⟩ := hf.lam_inv henv hΓ
  obtain ⟨⟨v, hD⟩, C, hc⟩ := hg.lam_inv henv hΓ
  have hxA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hx
  have hyD := argument_at_displayed_domain hΓ hg (HasType.lam hD hc) hy
  rw [proofErase_instN (show OnCtx (A :: Γ) (env.IsType univs) from ⟨hΓ, u, hA⟩) hxA Ctx.InstN.zero hb,
    proofErase_instN (show OnCtx (D :: Γ) (env.IsType univs) from ⟨hΓ, v, hD⟩) hyD Ctx.InstN.zero hc]
  exact HC.common

/-- Primitive-free inferred comparison of two actual lambda functions survives
paired head beta at nonjoining inferred-related argument images. Every recursive
source comparison constructor is covered, including eta and structure fields. -/
theorem proofErase_carrier_aligned_scoped_head_beta
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x P) (hy : env.HasType univs Γ y P)
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam D c) (.forallE P (.sort .zero)))
    (HX : CarrierAlignedCompare Step (proofEraseCtx Γ) false (proofErase Γ x) (proofErase Γ y))
    (H : ScopedCompare (fun _ _ _ => False) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam D c))) :
    CarrierAlignedCompare Step (proofEraseCtx Γ) true (proofErase Γ (b.inst x)) (proofErase Γ (c.inst y)) :=
  proofErase_carrier_aligned_scoped_head_beta_with_primitives empty_descent (fun H => H.elim)
    (by intro Γ Γ₀ σ τ e T out hΓ₀ W E ht H; exact H.elim) hstep hrename hΓ hx hy hf hg HX H

end Lean4Lean.VEnv.Strengthening
