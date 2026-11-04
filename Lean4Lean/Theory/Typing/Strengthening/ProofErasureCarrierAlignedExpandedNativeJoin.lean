import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedPureNativeJoin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelNativeBoundary

/-! # A higher-order expanded carrier with stable native common reducts

The known exact-output obstruction has native common-reduct evidence already
at stage zero. Every later guarded selection computation from its assigned
carrier preserves such evidence at stage zero, although exact recovery of
the original beta-expanded assigned carrier remains impossible.
-/
namespace Lean4Lean.VEnv.Strengthening.TypeFunctionExample
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private written_typed body_typed image_erasure
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeFunctionExample
variable [Params]

private theorem erasures (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ image = .lam (.forallE (.sort (.succ .zero)) (.sort .zero))
      (.app (.bvar 0) (.sort .zero)) ∧
    proofErase Γ assigned = .forallE
      (.app (.lam (.sort (.succ .zero)) (.forallE (.sort inputLevel) (.sort resultLevel))) (.sort .zero))
      (.sort .zero) := by
  have hΓW : OnCtx (written :: Γ) (env.IsType univs) := ⟨hΓ, _, written_typed⟩
  have hf : env.HasType univs (written :: Γ) (.bvar 0) written := .bvar .zero
  have hΓU : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hSelected := (inputs_equal (Γ := Γ)).hasType.1
  have hAssigned := HasType.forallE hSelected (HasType.sort (l := .zero) (by trivial))
  have hCore : env.HasType univs (.sort (.succ .zero) :: Γ) core
      (.sort (.imax (.succ inputLevel) (.succ resultLevel))) :=
    HasType.forallE (HasType.sort (by trivial)) (HasType.sort (by trivial))
  have hLam := HasType.lam (HasType.sort (l := .succ .zero) (by trivial)) hCore
  constructor
  · rw [image_erasure hΓ]
    change ProofShape.lam _ (proofErase (written :: Γ) body) = _
    rw [show proofErase (written :: Γ) body = .app _ _ from
      if_neg (not_isProof_of_sort hΓW body_typed)]
    rw [show proofErase (written :: Γ) (.bvar 0) = .bvar 0 from
      if_neg (not_isProof_function_to_sort hΓW hf)]
    rw [show proofErase (written :: Γ) (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hΓW (HasType.sort (by trivial)))]
  · rw [show proofErase Γ assigned = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hAssigned)]
    rw [show proofErase Γ selected = .app _ _ from if_neg (not_isProof_of_sort hΓ hSelected)]
    rw [show proofErase Γ (.lam (.sort (.succ .zero)) core) = .lam _ _ from
      if_neg (not_isProof_function_to_sort hΓ hLam)]
    rw [show proofErase (.sort (.succ .zero) :: Γ) core = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓU hCore)]
    simp only [proofErase]
    repeat' rw [if_neg (not_isProof_of_sort (by first | exact hΓ | exact hΓU | exact ⟨hΓ, _, hSelected⟩ | exact ⟨hΓU, _, HasType.sort (by trivial)⟩) (HasType.sort (by trivial)))]

/-- The counterexample has a pure assigned carrier and a native common reduct
at stage zero, despite its failure of exact assigned recovery over the union. -/
theorem level_native_common_reduct (hΓ : OnCtx Γ (env.IsType univs)) :
    PureLambda (proofErase Γ assigned) ∧
    ∃ out, ScopedTypeRecovery (ErasedLevelRecoveredStage D 0) (proofEraseCtx Γ)
      (proofErase Γ image) out ∧
      ScopedCompute (ErasedLevelRecoveredStage D 0) (proofEraseCtx Γ) (proofErase Γ assigned) out := by
  obtain ⟨EI, EA⟩ := erasures hΓ
  rw [EI, EA]
  refine ⟨by trivial, .forallE (.forallE (.sort (.succ .zero)) (.sort .zero)) (.sort .zero), ?_, ?_⟩
  · exact .lam (ScopedTypeRecovery.app (A := .sort (.succ .zero)) (B := .sort .zero) (.bvar (i := 0)))
  · apply ScopedCompute.forallE ?_ .refl
    apply ScopedCompute.trans (.beta .beta)
    exact .forallE (.base (.inr (.sort VLevel.imax_self (by trivial))))
      (.base (.inr (.sort VLevel.max_self (by trivial))))

/-- Restricting recovery transport to Pi-shaped demands is still insufficient:
the fresh variable has such a native output, but substituting this actually typed
image cannot recover the exact instantiated demand. This refutes only exact
Pi-demand substitution, not common-reduct repair or strengthening. -/
theorem level_pi_demand_instantiation_failure (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ X Y, ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx (assigned :: Γ))
      (proofErase (assigned :: Γ) (.bvar 0)) (.forallE X Y) ∧
      ¬ ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ)
        (proofErase Γ image) ((ProofShape.forallE X Y).inst (proofErase Γ image)) := by
  obtain ⟨_, EA⟩ := erasures hΓ
  obtain ⟨u, hA⟩ := image_typed.isType henv hΓ
  have hΓA : OnCtx (assigned :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hx : env.HasType univs (assigned :: Γ) (.bvar 0) assigned := .bvar .zero
  have EX : proofErase (assigned :: Γ) (.bvar 0) = .bvar 0 :=
    if_neg (not_isProof_function_to_sort hΓA hx)
  refine ⟨.app (.lam (.sort (.succ .zero)) (.forallE (.sort inputLevel) (.sort resultLevel))) (.sort .zero),
    .sort .zero, ?_, ?_⟩
  · rw [EX]
    have R : ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx (assigned :: Γ))
        (.bvar 0) ((proofErase Γ assigned).liftN 1) := .bvar
    simpa only [EA, ProofShape.liftN] using R
  · simpa only [EA, ProofShape.inst] using level_assigned_recovery_failure D hΓ

/-- Every guarded selection from the expanded assigned carrier can be repaired
to a native common reduct without increasing its stage-zero native evidence. -/
theorem level_native_selection_repair (hΓ : OnCtx Γ (env.IsType univs))
    (RS : ScopedCompute (ErasedLevelRecoveredStage D stage) (proofEraseCtx Γ)
      (proofErase Γ assigned) chosen) :
    (¬ ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ)
      (proofErase Γ image) (proofErase Γ assigned)) ∧
    ∃ out, ScopedTypeRecovery (ErasedLevelRecoveredStage D 0) (proofEraseCtx Γ)
      (proofErase Γ image) out ∧
      ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) chosen out := by
  obtain ⟨HP, out, RN, RA⟩ := level_native_common_reduct (D := D) hΓ
  obtain ⟨_, hA⟩ := image_typed.isType henv hΓ
  exact ⟨level_assigned_recovery_failure D hΓ,
    proofErase_carrier_aligned_pure_native_selection hΓ hA HP RN RA RS⟩

end Lean4Lean.VEnv.Strengthening.TypeFunctionExample
