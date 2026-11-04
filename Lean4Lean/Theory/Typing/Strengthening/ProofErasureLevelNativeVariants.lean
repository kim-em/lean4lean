import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelNativeUnion

/-! # Transport for native types with different universe annotations

The image need not recover its assigned type in the old computation system.
A structural universe variant of that type suffices in the extended system.
-/
namespace Lean4Lean.VEnv.Strengthening.LevelNativeSubstitution
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions} {k n : Nat}

/-- A native output can convert to its assigned structural universe variant
at the same stage. Actual typing supplies well-formed target universe levels. -/
theorem recovery_variant
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p A)
    (R : ScopedTypeRecovery (ErasedLevelRecoveredStage D k) (proofEraseCtx Γ)
      (proofErase Γ p) out) (V : StructuralVariant out (proofErase Γ A)) :
    ScopedTypeRecovery (ErasedLevelRecoveredStage D k) (proofEraseCtx Γ)
      (proofErase Γ p) (proofErase Γ A) := by
  obtain ⟨_, hA⟩ := hp.isType henv hΓ
  exact R.convert ((proofErase_carrier_aligned_variant_level_compute V hΓ hA).scoped
    (fun H => .base (erased_level_primitive_into_stage H k)))

/-- Simultaneous images may initially recover a structural variant of their
assigned output. The final exact certificate is constructed using universe steps. -/
theorem images_of_variants
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (H : ∀ {i A}, Lookup Γ i A → ¬ IsProof Γ (.bvar i) →
      ∃ out, ScopedTypeRecovery (ErasedLevelRecoveredStage D k) (proofEraseCtx Γ₀) (τ i) out ∧
        StructuralVariant out ((contextOracle (proofEraseCtx Γ) i).subst τ)) :
    Images D k Γ Γ₀ τ := by
  intro i A hl hn
  obtain ⟨out, R, V⟩ := H hl hn
  obtain ⟨_, hA⟩ := (show env.HasType univs Γ (.bvar i) A from .bvar hl).isType henv W.wf
  have EA : proofErase Γ₀ (A.subst σ) = (contextOracle (proofEraseCtx Γ) i).subst τ := by
    rw [proofErase_subst_with hΓ₀ W hA ES, proofEraseCtx_oracle, erasedTypeOracle_valid W.wf hl]
  have R' := recovery_variant hΓ₀ (W.lookup hl).hasType.1
    (by simpa only [ES hl hn] using R) (by simpa only [EA] using V)
  simpa only [EA, ES hl hn] using R'

/-- Any selected native universe variant can instantiate a computation at any
finite stage, including all recursive singleton-family guards. -/
theorem compute_inst_variant (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p A)
    (HR : ScopedTypeRecovery (ErasedLevelRecoveredStage D k) (proofEraseCtx Γ)
      (proofErase Γ p) native) (V : StructuralVariant native (proofErase Γ A))
    (ht : env.HasType univs (A :: Γ) e T)
    (R : ScopedCompute (ErasedLevelRecoveredStage D n) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out) :
    ScopedCompute (ErasedLevelRecoveredStage D (n + k)) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) :=
  compute_inst heq hs hΓ hp (recovery_variant hΓ hp HR V) ht R

/-- Full comparison, with all native and computed application rules, transports
under the same structural native-output condition. -/
theorem compare_inst_variant (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hp : env.HasType univs Γ p A)
    (HR : ScopedTypeRecovery (ErasedLevelRecoveredStage D k) (proofEraseCtx Γ)
      (proofErase Γ p) native) (V : StructuralVariant native (proofErase Γ A))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCompare (ErasedLevelRecoveredStage D n) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCompare (ErasedLevelRecoveredStage D (n + k)) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) :=
  compare_inst heq hs hΓ hA hp (recovery_variant hΓ hp HR V) ha hb H

end Lean4Lean.VEnv.Strengthening.LevelNativeSubstitution
