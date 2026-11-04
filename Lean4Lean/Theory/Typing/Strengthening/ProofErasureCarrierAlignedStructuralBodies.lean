import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedPairedBeta

/-! # Paired beta through structural variants of body annotations

Body reducts may differ by recursively comparing universe levels, rather than
having a literal common reduct. Only the left reduct is replayed as a typed
template; its actual substituted domains justify weakening the image relation
under binders. The right raw substitution need not recover those left domains.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming

namespace ProofShape
/-- Compatible universe conversion of raw shapes, including retained lambda
and Pi annotations. This contains no carrier checks, eta rules or computation. -/
inductive StructuralVariant : ProofShape → ProofShape → Prop where
  | refl : StructuralVariant a a
  | sort : u ≈ v → StructuralVariant (.sort u) (.sort v)
  | const : List.Forall₂ (· ≈ ·) ls ls' → StructuralVariant (.const c ls) (.const c ls')
  | app : StructuralVariant f g → StructuralVariant x y → StructuralVariant (.app f x) (.app g y)
  | proj : StructuralVariant a b → StructuralVariant (.proj s i a) (.proj s i b)
  | lam : StructuralVariant A E → StructuralVariant b c → StructuralVariant (.lam A b) (.lam E c)
  | forallE : StructuralVariant A E → StructuralVariant B C →
      StructuralVariant (.forallE A B) (.forallE E C)
end ProofShape

variable [Params]

/-- Structural body variants accept independently related substitution images.
Only the left original and image map supply typed interpretations. In particular,
the right images are not assumed typed at the left substituted binder domains. -/
theorem proofErase_carrier_aligned_variant_subst_images
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (V : StructuralVariant a b)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (he : env.HasType univs Γ e T) (Ee : proofErase Γ e = a)
    (E : ErasedSubstAgreement Γ Γ₀ σ ρ)
    (H : ∀ i, CarrierAlignedCompare Step (proofEraseCtx Γ₀) false (ρ i) (τ i)) :
    CarrierAlignedCompare Step (proofEraseCtx Γ₀) false (a.subst ρ) (b.subst τ) := by
  induction V generalizing Γ Γ₀ σ ρ τ e T with
  | refl =>
    simpa only [Ee] using proofErase_carrier_aligned_subst_images hrename hΓ₀ W he E H
  | sort h => exact .computed (.leaf (.sort h))
  | const h => exact .computed (.leaf (.const h))
  | app VF VX ihf ihx =>
    obtain ⟨f, x, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, hx⟩ := he.app_inv henv W.wf
    exact .app (ihf hΓ₀ W hf Ef E H) (ihx hΓ₀ W hx Ex E H).common
  | proj V ih =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv W.wf
    exact .proj (ih hΓ₀ W hm.hasType.2 Em E H)
  | lam VA VB ihA ihB | forallE VA VB ihA ihB =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := by
      first | exact erase_lam_inv Ee | exact erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := by
      first | exact he.lam_inv henv W.wf | exact he.forallE_inv henv
    have hA' := hA.subst henv.orderedStrong W hΓ₀
    have hΓA' : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) := ⟨hΓ₀, u, hA'⟩
    have HH : ∀ i, CarrierAlignedCompare Step (proofEraseCtx (A.subst σ :: Γ₀)) false
        (ρ.lift i) (τ.lift i) := by
      intro i
      cases i with
      | zero => exact .computed (.leaf .refl)
      | succ i =>
        have HR := (H i).rename hrename (ContextRenaming.of_liftN hΓ₀ hΓA' Ctx.LiftN.one)
        simpa only [subst_bvar_liftN, ProofShape.Subst.lift] using HR
    have HB := ihB hΓA' (W.lift henv.ordered hA) hb Eb (E.lift hΓ₀ W hA) HH
    rw [show proofEraseCtx (A.subst σ :: Γ₀) =
      (proofErase Γ A).subst ρ :: proofEraseCtx Γ₀ from
      congrArg (· :: proofEraseCtx Γ₀) (proofErase_subst_with hΓ₀ W hA E), EA] at HB
    first | exact .lam (ihA hΓ₀ W hA EA E H) HB | exact .forallE (ihA hΓ₀ W hA EA E H) HB

/-- Distinct body reducts related by compatible universe conversion may be
instantiated at nonjoining inferred-related images. The bodies may be typed
under different written domains; only their finite beta paths and the explicit
structural variant certificate are required. -/
theorem proofErase_carrier_aligned_variant_body_beta
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hΓE : OnCtx (E :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hc : env.HasType univs (E :: Γ) c C)
    (hx : env.HasType univs Γ x A) (hyE : env.HasType univs Γ y E)
    (RB : ProofShape.BetaRed (proofErase (A :: Γ) b) left)
    (RC : ProofShape.BetaRed (proofErase (E :: Γ) c) right)
    (V : StructuralVariant left right)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) false (proofErase Γ x) (proofErase Γ y)) :
    CarrierAlignedCompare Step (proofEraseCtx Γ) false
      (proofErase Γ (b.inst x)) (proofErase Γ (c.inst y)) := by
  obtain ⟨b', Rb', Eb'⟩ := proofErase_beta_replay hΓA hb RB
  have hb' := (Rb'.simAt henv.orderedStrong henv.betaSubjectReduction hΓA B hb).hasType.2
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have HT := proofErase_carrier_aligned_variant_subst_images hrename V hΓA.1 W hb' Eb'
    (erasedSubstAgreement_one hΓA hx)
    (τ := ProofShape.Subst.one (proofErase Γ y)) (fun i => by
      cases i with
      | zero => exact H
      | succ i => exact .computed (.leaf .refl))
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hb,
    proofErase_instN hΓE hyE Ctx.InstN.zero hc]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
    (CarrierAlignedCompare.compute (ScopedCompute.beta (RB.subst (σ := ProofShape.Subst.one (proofErase Γ x))))
      (ScopedCompute.beta (RC.subst (σ := ProofShape.Subst.one (proofErase Γ y)))) HT)

/-- Structural variants of finite body reducts suffice for paired head beta at
independently related images. Common assigned function typing supplies the
argument typings at the two written domains, which need not be identical. -/
theorem proofErase_carrier_aligned_variant_head_beta
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.lam A b) (.forallE P T))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P T))
    (hx : env.HasType univs Γ x P) (hy : env.HasType univs Γ y P)
    (RB : ProofShape.BetaRed (proofErase (A :: Γ) b) left)
    (RC : ProofShape.BetaRed (proofErase (E :: Γ) c) right)
    (V : StructuralVariant left right)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) false (proofErase Γ x) (proofErase Γ y)) :
    CarrierAlignedCompare Step (proofEraseCtx Γ) false
      (proofErase Γ (b.inst x)) (proofErase Γ (c.inst y)) := by
  obtain ⟨⟨u, hA⟩, B, hb⟩ := hf.lam_inv henv hΓ
  obtain ⟨⟨v, hE⟩, C, hc⟩ := hg.lam_inv henv hΓ
  exact proofErase_carrier_aligned_variant_body_beta hrename ⟨hΓ, u, hA⟩ ⟨hΓ, v, hE⟩ hb hc
    (argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hx)
    (argument_at_displayed_domain hΓ hg (HasType.lam hE hc) hy) RB RC V H

end Lean4Lean.VEnv.Strengthening
