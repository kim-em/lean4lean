import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedLevelStageClosure

/-! # Structural transport for the closed level-extended recovered union

Finite bounds lift the stage laws to the union. The union is closed under its
own general singleton-family and Eq-prefix guards, and supports native recovery,
full joint checking and recovered-carrier comparison through structural context
and carrier variation. Arbitrary declarative completeness remains separate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape PureObservation
variable [Params]

/-- Finite level-extended stages increase monotonically. -/
theorem erased_level_recovered_stage_mono (hle : stage ≤ later) {Δ a b}
    (H : ErasedLevelRecoveredStage D stage Δ a b) : ErasedLevelRecoveredStage D later Δ a b := by
  induction hle with
  | refl => exact H
  | step _ ih => exact .inl ih

/-- The union contains exactly base steps and its own guarded singleton/Eq
steps. Finite certificate bounds justify closure without an infinitary rule. -/
theorem erased_level_recovered_union_iff :
    ErasedLevelRecoveredUnion D Δ a b ↔ ErasedLevelCore D a b ∨
      CarrierRecoveredSingletonPrimitive (ErasedLevelRecoveredUnion D) Δ a b ∨
      ComputedJointPrefixPrimitive (ErasedLevelRecoveredUnion D) Δ a b := by
  constructor
  · rintro ⟨stage, H⟩
    induction stage with
    | zero => exact .inl H
    | succ stage ih =>
      rcases H with H | H | H
      · exact ih H
      · exact .inr (.inl (H.mono (fun H => ⟨stage, H⟩)))
      · exact .inr (.inr (H.mono (fun H => ⟨stage, H⟩)))
  · intro H
    rcases H with H | H | H
    · exact ⟨0, H⟩
    · obtain ⟨stage, H⟩ := H.finite_stage erased_level_recovered_stage_mono
      exact ⟨stage + 1, .inr (.inl H)⟩
    · cases H with
      | intro HC =>
        obtain ⟨stage, HC⟩ := HC.finite_stage erased_level_recovered_stage_mono
        exact ⟨stage + 1, .inr (.inr (.intro HC))⟩

/-- Every union computation preserves exact endpoints through structural
context conversion, at one finite source bound. -/
theorem structuralVariantComputeContext_level_union
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    StructuralVariantComputeContext (ErasedLevelRecoveredUnion D) := by
  intro Γ Γ' e T Δ source out hΓ ht W HO EΓ Ee R
  obtain ⟨stage, R⟩ := R.finite_stage erased_level_recovered_stage_mono
  exact (structuralVariantComputeContext_level_stage heq hs stage hΓ ht W HO EΓ Ee R).mono
    (fun H => ⟨stage, H⟩)

/-- Structural computation simulation is closed for the full union. -/
theorem structuralVariantCompute_level_union
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    StructuralVariantCompute (ErasedLevelRecoveredUnion D) :=
  structuralVariantCompute_of_context_and_levels (erased_level_recovered_union_descent heq hs)
    (structuralVariantComputeContext_level_union heq hs) (fun H => .base ⟨0, .inr H⟩)

/-- All existing joint-checking constructors transport over the closed union. -/
theorem ProofShape.ComputedJointCheck.level_union_variant
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ComputedJointCheck (ErasedLevelRecoveredUnion D) Δ kind a b) :
    ComputedJointVariantResult (ErasedLevelRecoveredUnion D) Δ kind a b :=
  H.structural_variant (erased_level_recovered_union_descent heq hs)
    (structuralVariantComputeContext_level_union heq hs) (structuralVariantCompute_level_union heq hs)

/-- Native recovery follows structural variants of context and term over the
closed union. No declaration-level compatibility or native completeness premise
is required; the existing source recovery certificate is the input. -/
theorem proofErase_carrier_aligned_level_union_recovery_variant
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (ht : env.HasType univs Γ e T) (ht' : env.HasType univs Γ' e' T')
    (HO : List.Forall₂ StructuralVariant (proofEraseCtx Γ) (proofEraseCtx Γ'))
    (V : StructuralVariant (proofErase Γ e) (proofErase Γ' e'))
    (R : ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ out', ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ')
      (proofErase Γ' e') out' ∧ StructuralVariant out out' :=
  proofErase_carrier_aligned_recovery_variant (erased_level_recovered_union_descent heq hs)
    (structuralVariantCompute_level_union heq hs) R hΓ hΓ' ht ht' rfl rfl HO V

/-- Full recovered comparison transports through structurally varied contexts
in the union, preserving the original comparison language and exact carrier rule. -/
theorem proofErase_carrier_aligned_level_union_recovered_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (HO : List.Forall₂ StructuralVariant (proofEraseCtx Γ) (proofEraseCtx Γ'))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : CarrierRecoveredCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    CarrierRecoveredCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ') mode
      (proofErase Γ' a) (proofErase Γ' b) := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedLevelRecoveredUnion D) :=
    erased_level_recovered_union_descent heq hs
  have W := proofErase_carrier_aligned_context_variant_defeq (Step := ErasedLevelRecoveredUnion D) hstep hΓ hΓ' HO
  have H' := H.structural_context hstep (structuralVariantComputeContext_level_union heq hs)
    (structuralVariantCompute_level_union heq hs) (fun H => .base ⟨0, .inr H⟩)
    hΓ ha hb rfl rfl rfl W HO
  rwa [proofErase_defeqCtx hΓ W ha, proofErase_defeqCtx hΓ W hb] at H'

omit [Params] in
/-- Actual well-formed environments with canonical Eq satisfy union context
transport, with declaration soundness discharged by the registry theorem. -/
theorem proofErase_carrier_aligned_environment_union_context
    {E : VEnv} (hE : E.WF) (U : Nat) (heq : E.HasCanonicalEq)
    (hΓ : OnCtx Γ (E.IsType U)) (hΓ' : OnCtx Γ' (E.IsType U))
    (HO : List.Forall₂ StructuralVariant (@proofEraseCtx (hE.params U) Γ) (@proofEraseCtx (hE.params U) Γ'))
    (ha : E.HasType U Γ a A) (hb : E.HasType U Γ b A)
    (H : @CarrierRecoveredCompare (hE.params U)
      (@ErasedLevelRecoveredUnion (hE.params U) (Definitions.ofEnv E U hE))
      (@proofEraseCtx (hE.params U) Γ) mode (@proofErase (hE.params U) Γ a) (@proofErase (hE.params U) Γ b)) :
    @CarrierRecoveredCompare (hE.params U)
      (@ErasedLevelRecoveredUnion (hE.params U) (Definitions.ofEnv E U hE))
      (@proofEraseCtx (hE.params U) Γ') mode (@proofErase (hE.params U) Γ' a) (@proofErase (hE.params U) Γ' b) := by
  letI := hE.params U
  exact proofErase_carrier_aligned_level_union_recovered_context heq (Definitions.ofEnv_sound hE)
    hΓ hΓ' HO ha hb H

end Lean4Lean.VEnv.Strengthening
