import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedLevelExposure

/-! # Full guard transfer after native nullary-family exposure

Expose the selected type at the same family and equivalent universes, then use
the complete joint checking transport theorem. Every existing argument guard
is retained, including recursively nested computation and function guards;
there is no restriction to a separate record-only certificate grammar.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private infer_aligned
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedFullContext
variable [Params]

/-- Any full joint carrier guard transfers from a typed nullary family to an
aligned selected type. Root stability supplies an equivalent universe instance;
the full structural transport law handles every recursive guard constructor. -/
theorem proofErase_carrier_aligned_nullary_full_guard_target
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hctx : StructuralVariantComputeContext Step) (hsim : StructuralVariantCompute Step)
    (hn : ConstantRootLevels Step family)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode (proofErase Γ A) (proofErase Γ B))
    (EA : proofErase Γ A = .const family ls)
    (HC : ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ x) (proofErase Γ y)) :
    ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ B)
      (proofErase Γ x) (proofErase Γ y) := by
  obtain ⟨ls', R, HL⟩ := proofErase_carrier_aligned_nullary_levels_exposure_of_stable_root
    hstep hn hΓ hA hB H EA
  obtain ⟨B', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hB rfl rfl R
  have HI := proofErase_carrier_aligned_types_inferred hstep hΓ hA hB H
  have HAB := infer_aligned hstep HI hΓ hA hB rfl rfl rfl
    (not_isProof_of_sort hΓ hA) (not_isProof_of_sort hΓ hB)
  have HAB' := HAB.toU.trans henv hΓ HB.toU
  have V : StructuralVariant (proofErase Γ A) (proofErase Γ B') := by
    rw [EA, EB]
    exact .const HL
  have HC' := HC.structural_variant hstep hctx hsim hΓ hx hy rfl rfl rfl rfl
    (.refl hΓ) (.rfl (fun _ _ => .refl)) HAB' V
  exact .carrierCompute R (by simpa only [EB] using HC')

/-- Native Pi selection transports an arbitrary existing argument guard from
an assigned nullary family to the selected native domain. The original native
certificate and assigned-to-native type comparison remain explicit. -/
theorem proofErase_carrier_aligned_recovered_nullary_full_guard
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hctx : StructuralVariantComputeContext Step) (hsim : StructuralVariantCompute Step)
    (hpi : ∀ {Δ A B out}, ¬ Step Δ (.forallE A B) out)
    (hn : ConstantRootLevels Step family)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = .const family ls)
    (HC : ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ x) (proofErase Γ y)) :
    ∃ D C, env.HasType univs Γ f (.forallE D C) ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ D) (proofErase (D :: Γ) C)) ∧
      CarrierAlignedCompare Step (proofEraseCtx Γ) false (proofErase Γ A) (proofErase Γ D) ∧
      ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ D)
        (proofErase Γ x) (proofErase Γ y) := by
  obtain ⟨D, C, hfDC, RD, HD⟩ := proofErase_carrier_aligned_recovered_pi_domain_of_no_root hstep hpi hΓ hf R H
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨_, hPi'⟩ := hfDC.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
  obtain ⟨⟨_, hD⟩, _, _⟩ := hPi'.forallE_inv henv
  exact ⟨D, C, hfDC, RD, HD,
    proofErase_carrier_aligned_nullary_full_guard_target hstep hctx hsim hn hΓ hA hD hx hy HD EA HC⟩

/-- The closed union discharges all transport and root laws for full selected
argument guards at rigid nullary domains. No field-grammar restriction remains. -/
theorem proofErase_carrier_aligned_level_union_full_argument_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hrigid : env.Rigid family) (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (R : ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) mode T
      (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = .const family ls)
    (HC : ComputedJointCarrierGuard (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ x) (proofErase Γ y)) :
    ∃ A' B', env.HasType univs Γ f (.forallE A' B') ∧
      ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ A') (proofErase (A' :: Γ) B')) ∧
      CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) false
        (proofErase Γ A) (proofErase Γ A') ∧
      ComputedJointCarrierGuard (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ A')
        (proofErase Γ x) (proofErase Γ y) :=
  proofErase_carrier_aligned_recovered_nullary_full_guard
    (erased_level_recovered_union_descent heq hs)
    (structuralVariantComputeContext_level_union heq hs) (structuralVariantCompute_level_union heq hs)
    erased_level_recovered_union_no_pi (erased_level_recovered_union_constant_levels heq hrigid hD)
    hΓ hf hx hy R H EA HC

/-- Full selected-domain guard transport checks actual applications, including
proof-valued results. The argument premise is the entire joint carrier language. -/
theorem proofErase_carrier_aligned_typed_application_full_nullary_guard
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hctx : StructuralVariantComputeContext Step) (hsim : StructuralVariantCompute Step)
    (hpi : ∀ {Δ A B out}, ¬ Step Δ (.forallE A B) out)
    (hn : ConstantRootLevels Step family)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = .const family ls)
    (HC : ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ x) (proofErase Γ y))
    (HF : ComputedJointCompare Step (proofEraseCtx Γ) false (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCompare Step (proofEraseCtx Γ) resultMode
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) := by
  have HFG := ((proofErase_computed_joint_compare_reflect hstep hΓ hf hg HF).1
    (by obtain ⟨u, hPi⟩ := hf.isType henv hΓ; exact .refl ⟨_, hPi⟩)).of_l henv hΓ hf
  have HXY := proofErase_computed_joint_carrier_reflect hstep hΓ hx hy HC
  have HE := HFG.appDF HXY
  by_cases hproof : IsProof Γ (.app f x)
  · rw [proofErase_eq_proof.2 hproof,
      proofErase_eq_proof.2 (isProof_of_common_type hΓ HE.hasType.1 HE.hasType.2 hproof)]
    exact .leaf .refl
  · have hproof' : ¬ IsProof Γ (.app g y) :=
      fun hp' => hproof (isProof_of_common_type hΓ HE.hasType.2 HE.hasType.1 hp')
    rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hproof,
      show proofErase Γ (.app g y) = .app _ _ from if_neg hproof']
    obtain ⟨_, _, _, RD, _, HG⟩ := proofErase_carrier_aligned_recovered_nullary_full_guard
      hstep hctx hsim hpi hn hΓ hf hx hy R H EA HC
    exact .appCarrier RD HF HG

/-- Actual application checking with full assigned argument guards is closed
in the level-extended union at rigid nullary domains. -/
theorem proofErase_carrier_aligned_level_union_full_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hrigid : env.Rigid family) (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (R : ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) mode T
      (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = .const family ls)
    (HC : ComputedJointCarrierGuard (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ x) (proofErase Γ y))
    (HF : ComputedJointCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) false
      (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) resultMode
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) :=
  proofErase_carrier_aligned_typed_application_full_nullary_guard
    (erased_level_recovered_union_descent heq hs)
    (structuralVariantComputeContext_level_union heq hs) (structuralVariantCompute_level_union heq hs)
    erased_level_recovered_union_no_pi (erased_level_recovered_union_constant_levels heq hrigid hD)
    hΓ hf hg hx hy R H EA HC HF

/-- For the actual environment registry, a registered structure family supplies
rigidity and declaration exclusion. Soundness and every computational transport
interface are discharged; only the source typing/checking certificates remain. -/
theorem proofErase_carrier_aligned_ofEnv_full_argument_guard
    (heq : env.HasCanonicalEq) (hi : env.projections family info)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (R : ScopedTypeRecovery (ErasedLevelRecoveredUnion (Definitions.ofEnv env univs henv)) (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare (ErasedLevelRecoveredUnion (Definitions.ofEnv env univs henv)) (proofEraseCtx Γ) mode T
      (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = .const family ls)
    (HC : ComputedJointCarrierGuard (ErasedLevelRecoveredUnion (Definitions.ofEnv env univs henv)) (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ x) (proofErase Γ y)) :
    ∃ A' B', env.HasType univs Γ f (.forallE A' B') ∧
      ScopedTypeRecovery (ErasedLevelRecoveredUnion (Definitions.ofEnv env univs henv)) (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ A') (proofErase (A' :: Γ) B')) ∧
      CarrierAlignedCompare (ErasedLevelRecoveredUnion (Definitions.ofEnv env univs henv)) (proofEraseCtx Γ) false
        (proofErase Γ A) (proofErase Γ A') ∧
      ComputedJointCarrierGuard (ErasedLevelRecoveredUnion (Definitions.ofEnv env univs henv)) (proofEraseCtx Γ) (proofErase Γ A')
        (proofErase Γ x) (proofErase Γ y) :=
  proofErase_carrier_aligned_level_union_full_argument_guard heq (Definitions.ofEnv_sound henv)
    (henv.projectionRigid hi) (fun _ _ => Definitions.ofEnv_no_rigid henv (henv.projectionRigid hi))
    hΓ hf hx hy R H EA HC

end Lean4Lean.VEnv.Strengthening
