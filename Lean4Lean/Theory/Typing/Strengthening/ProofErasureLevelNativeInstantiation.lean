import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelNativeTransport

/-! # Typed substitution and instantiation with an explicit stage bound

The consumers keep exact term and carrier erasures. The output stage is the
sum of the source stage and the common native-image recovery stage.
-/
namespace Lean4Lean.VEnv.Strengthening.LevelNativeSubstitution
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions} {n k : Nat}

/-- Common-typed comparison transports in the finite-stage checker with exact
endpoint erasures and unchanged mode. -/
theorem compare_subst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : Images D k Γ Γ₀ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ComputedJointCompare (ErasedLevelRecoveredStage D n) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCompare (ErasedLevelRecoveredStage D (n + k)) (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have HH := check heq hs H W.wf ha hb rfl rfl rfl
    (NativeImageTransport.ImageSubstitution.of_typed hΓ₀ W ES HI)
  simpa only [proofErase_subst_with hΓ₀ W ha ES, proofErase_subst_with hΓ₀ W hb ES] using HH

/-- Carrier checking transports recursively with the exact substituted
carrier. The application subcases may convert a guard locally while the result retains this exact carrier. -/
theorem carrier_subst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : Images D k Γ Γ₀ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ComputedJointCarrierGuard (ErasedLevelRecoveredStage D n) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCarrierGuard (ErasedLevelRecoveredStage D (n + k)) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (A.subst σ)) (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have HH := check heq hs H W.wf ha hb rfl rfl rfl rfl
    (NativeImageTransport.ImageSubstitution.of_typed hΓ₀ W ES HI)
  obtain ⟨_, hA⟩ := ha.isType henv W.wf
  simpa only [proofErase_subst_with hΓ₀ W hA ES, proofErase_subst_with hΓ₀ W ha ES,
    proofErase_subst_with hΓ₀ W hb ES] using HH

/-- Actual typed computation substitutes with an exact output and additive bound. -/
theorem compute_subst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (HI : Images D k Γ Γ₀ τ)
    (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedLevelRecoveredStage D n) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedCompute (ErasedLevelRecoveredStage D (n + k)) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
  rw [proofErase_subst_with hΓ₀ W ht ES]
  exact compute heq hs R W.wf ht rfl rfl (NativeImageTransport.ImageSubstitution.of_typed hΓ₀ W ES HI)

/-- Actual typed recovery substitutes while retaining its exact selected output. -/
theorem recovery_subst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (HI : Images D k Γ Γ₀ τ)
    (ht : env.HasType univs Γ e T)
    (R : ScopedTypeRecovery (ErasedLevelRecoveredStage D n) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedTypeRecovery (ErasedLevelRecoveredStage D (n + k)) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
  rw [proofErase_subst_with hΓ₀ W ht ES]
  exact recovery heq hs R W.wf ht rfl rfl (NativeImageTransport.ImageSubstitution.of_typed hΓ₀ W ES HI)

/-- Exact image certificates compose, with the sum of their recovery bounds.
Thus repeated certified substitutions remain inside this image class. -/
theorem Images.compose (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₂ : OnCtx Γ₂ (env.IsType univs))
    (W₁ : Ctx.SubstEq env univs Γ₁ σ₁ σ₁ Γ)
    (W₂ : Ctx.SubstEq env univs Γ₂ σ₂ σ₂ Γ₁)
    (E₁ : ErasedSubstAgreement Γ Γ₁ σ₁ τ₁)
    (E₂ : ErasedSubstAgreement Γ₁ Γ₂ σ₂ τ₂)
    (H₁ : Images D n Γ Γ₁ τ₁) (H₂ : Images D k Γ₁ Γ₂ τ₂) :
    Images D (n + k) Γ Γ₂ (τ₁.comp τ₂) := by
  intro i A hl hn
  have ht := (W₁.lookup hl).hasType.1
  have R : ScopedTypeRecovery (ErasedLevelRecoveredStage D n) (proofEraseCtx Γ₁)
      (proofErase Γ₁ (σ₁ i)) ((contextOracle (proofEraseCtx Γ) i).subst τ₁) := by
    rw [E₁ hl hn]
    exact H₁ hl hn
  have R' := recovery_subst heq hs hΓ₂ W₂ E₂ H₂ ht R
  simpa only [proofErase_subst_with hΓ₂ W₂ ht E₂, E₁ hl hn,
    ProofShape.subst_subst, ProofShape.Subst.comp] using R'

/-- Single instantiation preserves compare with the additive bound. -/
theorem compare_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hp : env.HasType univs Γ p A)
    (HR : ScopedTypeRecovery (ErasedLevelRecoveredStage D k) (proofEraseCtx Γ)
      (proofErase Γ p) (proofErase Γ A))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCompare (ErasedLevelRecoveredStage D n) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCompare (ErasedLevelRecoveredStage D (n + k)) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := A)).substEq hΓA hp
  have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one p)
      (ProofShape.Subst.one (proofErase Γ p)) := erasedSubstAgreement_one hΓA hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using
    compare_subst heq hs hΓ W ES (NativeImageTransport.Images.inst HR) ha hb H

/-- Single instantiation preserves carrier with the additive bound. -/
theorem carrier_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hp : env.HasType univs Γ p A)
    (HR : ScopedTypeRecovery (ErasedLevelRecoveredStage D k) (proofEraseCtx Γ)
      (proofErase Γ p) (proofErase Γ A))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCarrierGuard (ErasedLevelRecoveredStage D n) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCarrierGuard (ErasedLevelRecoveredStage D (n + k)) (proofEraseCtx Γ)
      (proofErase Γ (T.inst p)) (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := A)).substEq hΓA hp
  have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one p)
      (ProofShape.Subst.one (proofErase Γ p)) := erasedSubstAgreement_one hΓA hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using
    carrier_subst heq hs hΓ W ES (NativeImageTransport.Images.inst HR) ha hb H

/-- Single instantiation preserves compute with the additive bound. -/
theorem compute_inst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p A)
    (HR : ScopedTypeRecovery (ErasedLevelRecoveredStage D k) (proofEraseCtx Γ)
      (proofErase Γ p) (proofErase Γ A))
    (ht : env.HasType univs (A :: Γ) e T)
    (R : ScopedCompute (ErasedLevelRecoveredStage D n) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out) :
    ScopedCompute (ErasedLevelRecoveredStage D (n + k)) (proofEraseCtx Γ)
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
    (HR : ScopedTypeRecovery (ErasedLevelRecoveredStage D k) (proofEraseCtx Γ)
      (proofErase Γ p) (proofErase Γ A))
    (ht : env.HasType univs (A :: Γ) e T)
    (R : ScopedTypeRecovery (ErasedLevelRecoveredStage D n) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out) :
    ScopedTypeRecovery (ErasedLevelRecoveredStage D (n + k)) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) := by
  obtain ⟨u, hA⟩ := hp.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := A)).substEq hΓA hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst,
    ProofShape.Subst.liftN] using
    recovery_subst heq hs hΓ W (erasedSubstAgreement_one hΓA hp) (NativeImageTransport.Images.inst HR) ht R

/-- Recovered-family comparison transports the common native carrier and its guard. -/
theorem recovered_subst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : Images D k Γ Γ₀ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : CarrierRecoveredCompare (ErasedLevelRecoveredStage D n) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    CarrierRecoveredCompare (ErasedLevelRecoveredStage D (n + k)) (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have HH := recovered heq hs H W.wf ha hb rfl rfl rfl
    (NativeImageTransport.ImageSubstitution.of_typed hΓ₀ W ES HI)
  simpa only [proofErase_subst_with hΓ₀ W ha ES, proofErase_subst_with hΓ₀ W hb ES] using HH

/-- A native argument instantiates the full recovered-family checker. -/
theorem recovered_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hp : env.HasType univs Γ p A)
    (HR : ScopedTypeRecovery (ErasedLevelRecoveredStage D k) (proofEraseCtx Γ)
      (proofErase Γ p) (proofErase Γ A))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : CarrierRecoveredCompare (ErasedLevelRecoveredStage D n) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    CarrierRecoveredCompare (ErasedLevelRecoveredStage D (n + k)) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := A)).substEq hΓA hp
  have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one p)
      (ProofShape.Subst.one (proofErase Γ p)) := erasedSubstAgreement_one hΓA hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using
    recovered_subst heq hs hΓ W ES (NativeImageTransport.Images.inst HR) ha hb H

end Lean4Lean.VEnv.Strengthening.LevelNativeSubstitution
