import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeHeaderEta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureBetaSquares

/-! # Native header histories through scopes, wrappers and application

The original argument may provide exact recovery and subsequently compute to a
term that loses it. Instantiate the original-context codomain path first, then
compute the argument through its typed endpoint. This keeps the complete native
application history without an exact certificate for the current argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : PureObservation.Definitions}

/-- Native certificate descent and computation weakening lift an entire
header history through any well-formed unused binder block. -/
theorem NativeHeaderHistory.lift
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hf : env.HasType univs Γ f T)
    (H : NativeHeaderHistory D Γ header (proofErase Γ f)) :
    NativeHeaderHistory D Γ' (header.liftN n k) ((proofErase Γ f).liftN n k) := by
  intro out RN
  obtain ⟨A, _, RA, rfl⟩ := proofErase_scoped_recovery_certificate_descend
    (erased_static_structure_eta_expansion_union_certificate_descent heq hs)
    hΓ hΓ' W hf rfl RN
  have hrename : ∀ {Δ Δ' a b σ}, ErasedStaticStructureEtaExpansionUnion D Δ a b →
      ContextRenaming Δ Δ' σ → ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst σ) (b.subst σ) := by
    intro Δ Δ' a b σ ⟨stage, R⟩ W
    exact ⟨stage, erased_static_structure_eta_expansion_stage_rename heq hs stage R W⟩
  have R := (H RA).rename hrename (ContextRenaming.of_liftN hΓ hΓ' W)
  simpa only [subst_bvar_liftN] using R

/-- A constant wrapper inherits all original native header histories. -/
theorem NativeHeaderHistory.constant
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (hn : ¬ IsProof Γ f) (H : NativeHeaderHistory D Γ header (proofErase Γ f)) :
    NativeHeaderHistory D Γ header (constantExpansion (proofErase Γ f)) := by
  intro out RN
  exact H ((static_structure_constant_expansion_native_iff heq hs hΓ hf hn).1 RN)

/-- An identity frame stores the annotation's header ancestry. Its argument
needs ordinary typing at that annotation, not recovery of the annotation. -/
theorem NativeHeaderHistory.identity
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (hn : ¬ IsProof Γ f)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      header (proofErase Γ T)) :
    NativeHeaderHistory D Γ header (.app (.lam (proofErase Γ T) (.bvar 0)) (proofErase Γ f)) := by
  intro out RN
  rw [← proofErase_nativeIdentityExpansion hΓ hf hn] at RN
  exact RT.trans (static_structure_identity_native_origin heq hs hΓ hf RN)

/-- Applying a function with a fixed Pi-header history preserves the original
instantiated codomain's directed history. Only the original retained argument
needs exact native recovery. The current argument may have computed arbitrarily,
and native conversions at both the function and application remain unrestricted. -/
theorem NativeHeaderHistory.application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hx : env.HasType univs Γ x A)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (H : NativeHeaderHistory D Γ (proofErase Γ (.forallE A B)) f)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) a) :
    NativeHeaderHistory D Γ (proofErase Γ (B.inst x)) (.app f a) := by
  intro out RN
  obtain ⟨X, Y, RF, RC⟩ := RN.app_origin
  have RP := H RF
  rw [show proofErase Γ (.forallE A B) =
    .forallE (proofErase Γ A) (proofErase (A :: Γ) B) from
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB))] at RP
  obtain ⟨_, _, _, _, _, _, _, RB⟩ :=
    proofErase_static_structure_union_pi_components heq hs hΓ hA hB RP
  exact (static_structure_body_argument_square heq hs ⟨hΓ, u, hA⟩ hB hx HR RB RX).trans RC

end Lean4Lean.VEnv.Strengthening
