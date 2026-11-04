import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedNativeInstantiation

/-! # Full aligned instantiation over the level-extended union

Each retained image may use its own finite recovery stage. Existing computation
transport collects those bounds; the aligned induction preserves all recursive
native and eta certificates without requiring a new completeness theorem.
-/
namespace Lean4Lean.VEnv.Strengthening.LevelNativeSubstitution
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Full aligned comparison transports under interpreted union-native images.
No finite bound for the whole aligned derivation needs to be chosen here. -/
theorem aligned_union (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : CarrierAlignedCompare (ErasedLevelRecoveredUnion D) Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (W : NativeImageTransport.ImageSubstitution (ErasedLevelRecoveredUnion D) Δ Δ' τ) :
    CarrierAlignedCompare (ErasedLevelRecoveredUnion D) Δ' mode (sa.subst τ) (sb.subst τ) := by
  apply NativeImageTransport.aligned_of_compute
    (fun ⟨stage, H⟩ WR => ⟨stage, erased_level_recovered_stage_rename heq hs stage H WR⟩)
    (erased_level_recovered_union_descent heq hs) (fun H => H) ?_
    H hΓ ha hb EΓ Ea Eb W
  intro Γ Δ Δ' τ e T source out R hΓ ht EΓ Ee W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, HI⟩ := W hΓ EΓ
  have R' : ScopedCompute (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ e) out := by
    simpa only [EΓ, Ee] using R
  have HH := compute_union_subst heq hs hΓ₀ WS ES HI ht R'
  simpa only [proofErase_subst_with hΓ₀ WS ht ES, EΓ₀, Ee] using HH

/-- Actual full aligned comparison substitutes with exact endpoint erasures. -/
theorem aligned_union_subst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (HI : UnionImages D Γ Γ₀ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have HH := aligned_union heq hs H W.wf ha hb rfl rfl rfl
    (NativeImageTransport.ImageSubstitution.of_typed hΓ₀ W ES HI)
  simpa only [proofErase_subst_with hΓ₀ W ha ES, proofErase_subst_with hΓ₀ W hb ES] using HH

/-- A native argument instantiates full aligned bodies at the union. -/
theorem aligned_union_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hp : env.HasType univs Γ p A)
    (HR : ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ)
      (proofErase Γ p) (proofErase Γ A))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := A)).substEq hΓA hp
  have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one p)
      (ProofShape.Subst.one (proofErase Γ p)) := erasedSubstAgreement_one hΓA hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using
    aligned_union_subst heq hs hΓ W ES (NativeImageTransport.Images.inst HR) ha hb H

/-- Existing native evidence aligned with an assigned sort suffices to
instantiate arbitrary full aligned bodies under that sort binder. -/
theorem aligned_union_sort_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p (.sort u))
    (R : ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ p) out)
    (HT : CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) nativeMode out (.sort u))
    (ha : env.HasType univs (.sort u :: Γ) a T) (hb : env.HasType univs (.sort u :: Γ) b T)
    (H : CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx (.sort u :: Γ)) mode
      (proofErase (.sort u :: Γ) a) (proofErase (.sort u :: Γ) b)) :
    CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  have hU : env.HasType univs Γ (.sort u) (.sort (.succ u)) := .sort (hp.sort_r henv hΓ)
  have EU : proofErase Γ (.sort u) = .sort u := if_neg (not_isProof_of_sort hΓ hU)
  have HR := proofErase_carrier_aligned_level_union_recovered_sort_exact heq hs hΓ hp R HT
  exact aligned_union_inst heq hs hΓ hU hp (by simpa only [EU] using HR) ha hb H

end Lean4Lean.VEnv.Strengthening.LevelNativeSubstitution
