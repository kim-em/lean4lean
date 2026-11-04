import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExactNativeContext
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentValueBoundary

/-! # Converted polymorphic binders whose results become arbitrary types

The target binder is polymorphic identity. Its source annotation expands only
the universe input, preserving the dependent codomain syntax. Exact alignment
allows recursive context transport, then resumes native recovery after applying
the identity parameter at an arbitrary Type, including a function type.
-/
namespace Lean4Lean.VEnv.Strengthening.NativeFamilyFramework.ExactNativeExample
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open DependentValueBoundary
variable [Params]

/-- A beta-expanded Type annotation. -/
def selectedUniverse : VExpr := .app (.lam (.sort (.succ .zero)) (.sort (.succ .zero))) (.sort .zero)
/-- The source keeps the same dependent X → X codomain. -/
def sourceType : VExpr := .forallE selectedUniverse (.forallE (.bvar 0) (.bvar 1))

/-- Source and native universe inputs are ordinarily equal. -/
theorem universes_equal : env.IsDefEq univs Γ selectedUniverse (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) :=
  .beta (HasType.sort (by trivial)) (HasType.sort (by trivial))

private theorem source_body_typed (hΓ : OnCtx Γ (env.IsType univs)) :
    env.HasType univs (selectedUniverse :: Γ) (.forallE (.bvar 0) (.bvar 1))
      (.sort (.imax (.succ .zero) (.succ .zero))) := by
  have HC : IsDefEqCtx env univs [] (.sort (.succ .zero) :: Γ) (selectedUniverse :: Γ) :=
    .succ (.refl hΓ) universes_equal.symm
  exact (HasType.forallE (Γ := .sort (.succ .zero) :: Γ)
    (show env.HasType univs (.sort (.succ .zero) :: Γ) (.bvar 0) (.sort (.succ .zero)) from .bvar .zero)
    (show env.HasType univs (.bvar 0 :: .sort (.succ .zero) :: Γ) (.bvar 1) (.sort (.succ .zero)) from .bvar (.succ .zero))).defeqDFC henv HC

/-- Native identity aligns to the changed source annotation with an exact
arbitrary dependent result, outside the old sort-ending native tree grammar. -/
theorem identity_alignment (hΓ : OnCtx Γ (env.IsType univs)) :
    Alignment D PolymorphicTypeFamily Γ identityType (proofErase Γ sourceType) := by
  letI := polymorphic_inputLaws (D := D)
  exact Alignment.equal_input_exact_result hΓ universes_equal (show PolymorphicTypeFamily Γ (.sort (.succ .zero)) from .sort)
    (source_body_typed hΓ)

omit [Params] in
/-- No input predicate can make this identity carrier a sort-ending native tree. -/
theorem identity_not_tree (F : List VExpr → VExpr → Prop) : ¬ Tree F Γ identityType := by
  intro H
  have HE : ∀ {Γ T}, Tree F Γ T → SortResult T := by
    intro Γ T HT
    induction HT with
    | sort => trivial
    | function _ _ ih => exact ih
  exact HE H

/-- Full recursive carrier transport crosses this converted polymorphic binder.
Applications in the transported guard may instantiate X by arbitrary types. -/
theorem identity_context
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs (sourceType :: Γ) a T)
    (hb : env.HasType univs (sourceType :: Γ) b T)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (sourceType :: Γ))
      (proofErase (sourceType :: Γ) T) (proofErase (sourceType :: Γ) a) (proofErase (sourceType :: Γ) b)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (identityType :: Γ))
      (proofErase (sourceType :: Γ) T) (proofErase (sourceType :: Γ) a) (proofErase (sourceType :: Γ) b) := by
  letI := polymorphic_inputLaws (D := D)
  exact equal_input_carrier_context hs hΓ universes_equal (show PolymorphicTypeFamily Γ (.sort (.succ .zero)) from .sort)
    (source_body_typed hΓ) ha hb H

private theorem native_app
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app f x))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f)
      (proofErase Γ (.forallE A B))) :
    ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ (.app f x))
      (proofErase Γ (B.inst x)) := by
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨u, hA⟩, _, hB⟩ := hPi.forallE_inv henv
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi)] at R
  rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hn, proofErase_instN hΓA hx .zero hB]
  exact .app R

/-- After both applications, native recovery resumes at the actual instantiated
result X. The argument x needs no recovery certificate and X need not be a sort. -/
theorem instantiated_result_recovery (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs (identityType :: Γ) X (.sort (.succ .zero)))
    (hx : env.HasType univs (identityType :: Γ) x X)
    (hn : ¬ IsProof (identityType :: Γ) (.app (.app (.bvar 0) X) x)) :
    ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx (identityType :: Γ))
      (proofErase (identityType :: Γ) (.app (.app (.bvar 0) X) x))
      (proofErase (identityType :: Γ) X) := by
  have hΔ : OnCtx (identityType :: Γ) (env.IsType univs) := ⟨hΓ, _, identityType_typed⟩
  have hf : env.HasType univs (identityType :: Γ) (.bvar 0) identityType := .bvar .zero
  have EI : ((VExpr.bvar 0).forallE (.bvar 1)).inst X = .forallE X X.lift := by
    simp [VExpr.inst, instVar, VExpr.lift]
  have hf' : env.HasType univs (identityType :: Γ) (.app (.bvar 0) X) (.forallE X X.lift) := by
    simpa only [EI] using HasType.app hf hX
  have hn' := not_isProof_fn hΔ hf' hx hn
  have hn₀ := not_isProof_fn hΔ hf hX hn'
  have R := proofErase_scoped_lookup_recovery (Step := ErasedJointStage D 0) hΔ
    (show Lookup (identityType :: Γ) 0 identityType from .zero) hn₀ .refl
  have R' := native_app hΔ hf hX hn' R
  rw [EI] at R'
  simpa only [VExpr.inst_lift] using native_app hΔ hf' hx hn R'

/-- A concrete instantiation changes the generic result into Prop → Prop,
which remains exactly recoverable after both applications. -/
theorem function_result_recovery (hΓ : OnCtx Γ (env.IsType univs)) :
    ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx (identityType :: Γ))
      (proofErase (identityType :: Γ)
        (.app (.app (.bvar 0) (.forallE (.sort .zero) (.sort .zero))) (.lam (.sort .zero) (.bvar 0))))
      (proofErase (identityType :: Γ) (.forallE (.sort .zero) (.sort .zero))) := by
  have hΔ : OnCtx (identityType :: Γ) (env.IsType univs) := ⟨hΓ, _, identityType_typed⟩
  have hX : env.HasType univs (identityType :: Γ) (.forallE (.sort .zero) (.sort .zero)) (.sort (.succ .zero)) :=
    (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq
      (HasType.forallE (HasType.sort (by trivial)) (HasType.sort (by trivial)))
  have hx : env.HasType univs (identityType :: Γ) (.lam (.sort .zero) (.bvar 0))
      (.forallE (.sort .zero) (.sort .zero)) := .lam (HasType.sort (by trivial)) (.bvar .zero)
  have hf : env.HasType univs (identityType :: Γ) (.bvar 0) identityType := .bvar .zero
  have ht := HasType.app (HasType.app hf hX) hx
  exact instantiated_result_recovery hΓ hX hx (not_isProof_function_to_sort hΔ ht)

end Lean4Lean.VEnv.Strengthening.NativeFamilyFramework.ExactNativeExample
