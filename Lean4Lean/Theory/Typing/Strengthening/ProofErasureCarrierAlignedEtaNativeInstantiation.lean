import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaNativeTransport

/-! # Typed dependent instantiation with native eta expansion

The full aligned checker, computation and native recovery retain their exact
substituted endpoints with an additive bound on source and image guard stages.
-/
namespace Lean4Lean.VEnv.Strengthening.EtaNativeSubstitution
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions} {n k : Nat}

/-- Full aligned comparison transports the common native carrier and its guard. -/
theorem aligned_subst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : Images D k Γ Γ₀ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : CarrierAlignedCompare (ErasedEtaExpansionStage D n) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    CarrierAlignedCompare (ErasedEtaExpansionStage D (n + k)) (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have HH := aligned heq hs H W.wf ha hb rfl rfl rfl
    (NativeImageTransport.ImageSubstitution.of_typed hΓ₀ W ES HI)
  simpa only [proofErase_subst_with hΓ₀ W ha ES, proofErase_subst_with hΓ₀ W hb ES] using HH

/-- A native argument instantiates the full aligned checker. -/
theorem aligned_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hp : env.HasType univs Γ p A)
    (HR : ScopedTypeRecovery (ErasedEtaExpansionStage D k) (proofEraseCtx Γ)
      (proofErase Γ p) (proofErase Γ A))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : CarrierAlignedCompare (ErasedEtaExpansionStage D n) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    CarrierAlignedCompare (ErasedEtaExpansionStage D (n + k)) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := A)).substEq hΓA hp
  have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one p)
      (ProofShape.Subst.one (proofErase Γ p)) := erasedSubstAgreement_one hΓA hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using
    aligned_subst heq hs hΓ W ES (NativeImageTransport.Images.inst HR) ha hb H

/-- Actual typed computation substitutes with an exact output and additive bound. -/
theorem compute_subst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (HI : Images D k Γ Γ₀ τ)
    (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedEtaExpansionStage D n) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedCompute (ErasedEtaExpansionStage D (n + k)) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
  rw [proofErase_subst_with hΓ₀ W ht ES]
  exact compute heq hs R W.wf ht rfl rfl (NativeImageTransport.ImageSubstitution.of_typed hΓ₀ W ES HI)

/-- Actual typed recovery substitutes while retaining its exact selected output. -/
theorem recovery_subst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (HI : Images D k Γ Γ₀ τ)
    (ht : env.HasType univs Γ e T)
    (R : ScopedTypeRecovery (ErasedEtaExpansionStage D n) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedTypeRecovery (ErasedEtaExpansionStage D (n + k)) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
  rw [proofErase_subst_with hΓ₀ W ht ES]
  exact recovery heq hs R W.wf ht rfl rfl (NativeImageTransport.ImageSubstitution.of_typed hΓ₀ W ES HI)

/-- Single instantiation preserves compute with the additive bound. -/
theorem compute_inst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p A)
    (HR : ScopedTypeRecovery (ErasedEtaExpansionStage D k) (proofEraseCtx Γ)
      (proofErase Γ p) (proofErase Γ A))
    (ht : env.HasType univs (A :: Γ) e T)
    (R : ScopedCompute (ErasedEtaExpansionStage D n) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out) :
    ScopedCompute (ErasedEtaExpansionStage D (n + k)) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) := by
  obtain ⟨u, hA⟩ := hp.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := A)).substEq hΓA hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst,
    ProofShape.Subst.liftN] using
    compute_subst heq hs hΓ W (erasedSubstAgreement_one hΓA hp) (NativeImageTransport.Images.inst HR) ht R

/-- Single instantiation preserves recovery with the additive bound. -/
theorem recovery_inst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p A)
    (HR : ScopedTypeRecovery (ErasedEtaExpansionStage D k) (proofEraseCtx Γ)
      (proofErase Γ p) (proofErase Γ A))
    (ht : env.HasType univs (A :: Γ) e T)
    (R : ScopedTypeRecovery (ErasedEtaExpansionStage D n) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out) :
    ScopedTypeRecovery (ErasedEtaExpansionStage D (n + k)) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) := by
  obtain ⟨u, hA⟩ := hp.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := A)).substEq hΓA hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst,
    ProofShape.Subst.liftN] using
    recovery_subst heq hs hΓ W (erasedSubstAgreement_one hΓA hp) (NativeImageTransport.Images.inst HR) ht R

end Lean4Lean.VEnv.Strengthening.EtaNativeSubstitution
