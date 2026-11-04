import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionNativeInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelNativeBoundary

/-! # Repairing the beta-expanded higher-order input

The full previous union cannot select this image's assigned type. A closed
constant expansion repairs that specific obstruction at stage zero, allowing
the image to instantiate every guarded layer at the unchanged source stage.
-/
namespace Lean4Lean.VEnv.Strengthening.TypeFunctionExample
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private image_erasure erase_sort written_typed body_typed core_equal
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeFunctionExample
variable [Params] {D : PureObservation.Definitions} {n : Nat}

/-- Exact native recovery at the beta-expanded assigned input. Both changes
of universe syntax and the final head expansion are explicit computations. -/
theorem expansion_recovery (hΓ : OnCtx Γ (env.IsType univs)) :
    ScopedTypeRecovery (ErasedExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ image) (proofErase Γ assigned) := by
  have hΓW : OnCtx (written :: Γ) (env.IsType univs) := ⟨hΓ, _, written_typed⟩
  have EB : proofErase (written :: Γ) body = .app (.bvar 0) (.sort .zero) := by
    rw [show proofErase (written :: Γ) body = .app _ _ from if_neg (not_isProof_of_sort hΓW body_typed)]
    have hf : env.HasType univs (written :: Γ) (.bvar 0) written := .bvar .zero
    rw [show proofErase (written :: Γ) (.bvar 0) = .bvar 0 from
      if_neg (not_isProof_function_to_sort hΓW hf), erase_sort hΓW (by trivial)]
  have EC : proofErase Γ core = .forallE (.sort inputLevel) (.sort resultLevel) := by
    rw [show proofErase Γ core = .forallE _ _ from if_neg (not_isProof_of_sort hΓ core_equal.hasType.1),
      erase_sort hΓ (by trivial), erase_sort (Γ := .sort inputLevel :: Γ) ⟨hΓ, _, HasType.sort (by trivial)⟩ (u := resultLevel) (by trivial)]
  have ES : proofErase Γ selected = constantExpansion (.forallE (.sort inputLevel) (.sort resultLevel)) := by
    change proofErase Γ (.app (.lam (.sort (.succ .zero)) core.lift) (.sort .zero)) = _
    rw [proofErase_constantExpansion hΓ core_equal.hasType.1 (not_isProof_of_sort hΓ core_equal.hasType.1), EC]
  have hAssigned := HasType.forallE (Γ := Γ) inputs_equal.hasType.1 (HasType.sort (l := .zero) (by trivial))
  have EA : proofErase Γ assigned = .forallE (proofErase Γ selected) (.sort .zero) := by
    rw [show proofErase Γ assigned = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hAssigned),
      erase_sort (Γ := selected :: Γ) ⟨hΓ, _, inputs_equal.hasType.1⟩ (u := .zero) (by trivial)]
  rw [image_erasure hΓ, EB, EA, ES]
  apply ScopedTypeRecovery.convert (T := .forallE (.forallE (.sort (.succ .zero)) (.sort .zero)) (.sort .zero))
  · apply ScopedTypeRecovery.lam
    have R : ScopedTypeRecovery (ErasedExpansionStage D 0)
        (.forallE (.sort (.succ .zero)) (.sort .zero) :: proofEraseCtx Γ)
        (.bvar 0) (.forallE (.sort (.succ .zero)) (.sort .zero)) := .bvar
    exact ScopedTypeRecovery.app R
  · apply ScopedCompute.forallE (B := .sort .zero) (B' := .sort .zero) _ .refl
    apply ScopedCompute.trans (b := .forallE (.sort inputLevel) (.sort resultLevel))
    · exact .forallE (.base (.inl (.inr (.sort VLevel.imax_self.symm (by trivial)))))
        (.base (.inl (.inr (.sort VLevel.max_self.symm (by trivial)))))
    · exact .base (.inr (.intro (by intro E; cases E)))

/-- A strict repair: failure in the old full union coexists with exact
recovery at the new base stage, in the same actual context. -/
theorem expansion_repair (hΓ : OnCtx Γ (env.IsType univs)) :
    (¬ ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ)
      (proofErase Γ image) (proofErase Γ assigned)) ∧
    ScopedTypeRecovery (ErasedExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ image) (proofErase Γ assigned) :=
  ⟨level_assigned_recovery_failure D hΓ, expansion_recovery hΓ⟩

/-- The repaired higher-order input instantiates computation at every finite
expanded stage, including its recovered-family and Eq-prefix guards. -/
theorem expansion_compute_inst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs (assigned :: Γ) e T)
    (R : ScopedCompute (ErasedExpansionStage D n) (proofEraseCtx (assigned :: Γ))
      (proofErase (assigned :: Γ) e) out) :
    ScopedCompute (ErasedExpansionStage D n) (proofEraseCtx Γ)
      (proofErase Γ (e.inst image)) (out.inst (proofErase Γ image)) := by
  simpa only [Nat.add_zero] using
    ExpansionNativeSubstitution.compute_inst heq hs hΓ image_typed (expansion_recovery hΓ) ht R

/-- Full recursive comparison also survives this previously rejected image,
with no restriction on the guarded depth of the source certificate. -/
theorem expansion_compare_inst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs (assigned :: Γ) a T) (hb : env.HasType univs (assigned :: Γ) b T)
    (H : ComputedJointCompare (ErasedExpansionStage D n) (proofEraseCtx (assigned :: Γ)) mode
      (proofErase (assigned :: Γ) a) (proofErase (assigned :: Γ) b)) :
    ComputedJointCompare (ErasedExpansionStage D n) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst image)) (proofErase Γ (b.inst image)) := by
  have hp : env.HasType univs Γ image assigned := image_typed
  obtain ⟨u, hA⟩ := hp.isType henv hΓ
  simpa only [Nat.add_zero] using
    ExpansionNativeSubstitution.compare_inst heq hs hΓ hA image_typed (expansion_recovery hΓ) ha hb H

end Lean4Lean.VEnv.Strengthening.TypeFunctionExample
