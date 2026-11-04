import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedParameterizedFields

/-! # Actual application checking at parameterized structure domains

The native type comparison remains in the complete computed grammar. Selected
carrier parameters may change; ordinary retained projection checks rebuild the
argument guard at that selected domain. Both proof and data results are handled.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- The fieldwise selected-domain certificate checks actual application
erasures, including proof-valued applications. Actual arguments have the common
assigned domain, and only retained projections require recursive comparison. -/
theorem proofErase_carrier_aligned_typed_parameterized_application
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hpi : ∀ {Δ A B out}, ¬ Step Δ (.forallE A B) out)
    (hn : SpineRootLevels Step family)
    (hi : env.projections family info) (hindices : info.nindices = 0)
    (hp : ps.length = info.nparams)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : ComputedJointCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = ProofShape.mkApps (.const family ls) ps)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (Hfields : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      ComputedJointCompare Step (proofEraseCtx Γ) true
        (.proj family i (proofErase Γ x)) (.proj family i (proofErase Γ y)))
    (HF : ComputedJointCompare Step (proofEraseCtx Γ) false (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCompare Step (proofEraseCtx Γ) resultMode
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) := by
  have HFG := ((proofErase_computed_joint_compare_reflect hstep hΓ hf hg HF).1
    (by obtain ⟨u, hPi⟩ := hf.isType henv hΓ; exact .refl ⟨_, hPi⟩)).of_l henv hΓ hf
  have HG : ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ x) (proofErase Γ y) := by
    rw [EA]
    exact .carrierIntro hi hindices hp hadm Hfields
  have HXY := proofErase_computed_joint_carrier_reflect hstep hΓ hx hy HG
  have HE := HFG.appDF HXY
  by_cases hproof : IsProof Γ (.app f x)
  · rw [proofErase_eq_proof.2 hproof,
      proofErase_eq_proof.2 (isProof_of_common_type hΓ HE.hasType.1 HE.hasType.2 hproof)]
    exact .leaf .refl
  · have hproof' : ¬ IsProof Γ (.app g y) :=
      fun hp' => hproof (isProof_of_common_type hΓ HE.hasType.2 HE.hasType.1 hp')
    rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hproof,
      show proofErase Γ (.app g y) = .app _ _ from if_neg hproof']
    obtain ⟨_, _, _, RD, _, HG⟩ := proofErase_carrier_aligned_computed_recovered_parameterized_fields
      hstep hpi hn hi hindices hp hΓ hf R H EA hadm Hfields
    exact .appCarrier RD HF HG

/-- Parameterized fieldwise application checking is closed in the level-
extended finite stages, including arbitrary computed native type comparisons. -/
theorem proofErase_carrier_aligned_level_stage_parameterized_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info) (hindices : info.nindices = 0)
    (hp : ps.length = info.nparams)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (R : ScopedTypeRecovery (ErasedLevelRecoveredStage D stage) (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : ComputedJointCompare (ErasedLevelRecoveredStage D stage) (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = ProofShape.mkApps (.const family ls) ps)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (Hfields : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      ComputedJointCompare (ErasedLevelRecoveredStage D stage) (proofEraseCtx Γ) true
        (.proj family i (proofErase Γ x)) (.proj family i (proofErase Γ y)))
    (HF : ComputedJointCompare (ErasedLevelRecoveredStage D stage) (proofEraseCtx Γ) false (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCompare (ErasedLevelRecoveredStage D stage) (proofEraseCtx Γ) resultMode
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) :=
  proofErase_carrier_aligned_typed_parameterized_application
    (erased_level_recovered_stage_descent heq hs stage) (erased_level_recovered_stage_no_pi stage)
    (erased_level_recovered_stage_spine_levels heq (henv.projectionRigid hi) hD stage)
    hi hindices hp hΓ hf hg hx hy R H EA hadm Hfields HF

/-- Parameterized fieldwise application checking is closed in the level-
extended union, including arbitrary computed native type comparisons. -/
theorem proofErase_carrier_aligned_level_union_parameterized_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info) (hindices : info.nindices = 0)
    (hp : ps.length = info.nparams)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (R : ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : ComputedJointCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = ProofShape.mkApps (.const family ls) ps)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (Hfields : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      ComputedJointCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) true
        (.proj family i (proofErase Γ x)) (.proj family i (proofErase Γ y)))
    (HF : ComputedJointCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) false (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) resultMode
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) :=
  proofErase_carrier_aligned_typed_parameterized_application
    (erased_level_recovered_union_descent heq hs) erased_level_recovered_union_no_pi
    (erased_level_recovered_union_spine_levels heq (henv.projectionRigid hi) hD)
    hi hindices hp hΓ hf hg hx hy R H EA hadm Hfields HF

/-- The actual declaration registry and a registered structure discharge
soundness and rigid-family exclusion for parameterized application checking. -/
theorem proofErase_carrier_aligned_ofEnv_parameterized_application
    (heq : env.HasCanonicalEq)
    (hi : env.projections family info) (hindices : info.nindices = 0)
    (hp : ps.length = info.nparams)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (R : ScopedTypeRecovery (ErasedLevelRecoveredUnion (Definitions.ofEnv env univs henv)) (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : ComputedJointCompare (ErasedLevelRecoveredUnion (Definitions.ofEnv env univs henv)) (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = ProofShape.mkApps (.const family ls) ps)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (Hfields : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      ComputedJointCompare (ErasedLevelRecoveredUnion (Definitions.ofEnv env univs henv)) (proofEraseCtx Γ) true
        (.proj family i (proofErase Γ x)) (.proj family i (proofErase Γ y)))
    (HF : ComputedJointCompare (ErasedLevelRecoveredUnion (Definitions.ofEnv env univs henv)) (proofEraseCtx Γ) false (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCompare (ErasedLevelRecoveredUnion (Definitions.ofEnv env univs henv)) (proofEraseCtx Γ) resultMode
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) :=
  proofErase_carrier_aligned_level_union_parameterized_application heq (Definitions.ofEnv_sound henv)
    (fun _ _ => Definitions.ofEnv_no_rigid henv (henv.projectionRigid hi))
    hi hindices hp hΓ hf hg hx hy R H EA hadm Hfields HF

end Lean4Lean.VEnv.Strengthening
