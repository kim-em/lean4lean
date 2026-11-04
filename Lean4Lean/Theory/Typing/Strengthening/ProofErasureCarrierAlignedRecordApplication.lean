import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedRecordTransfer

/-! # Native application with recursive record argument guards

Aligned nullary exposure supplies a structural universe variant at the selected
carrier head. Recursive record transport rebuilds its argument guard, and the
existing native application rule consumes that guard at the selected Pi domain.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A typed recursive record guard transfers to an aligned selected nullary
carrier, including a computed selected type. Field recursion can be arbitrarily
deep; the original endpoints retain their actual source typings. -/
theorem proofErase_carrier_aligned_nullary_record_target
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (hB : env.HasType univs Γ B (.sort v))
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode (proofErase Γ A) (proofErase Γ B))
    (EA : proofErase Γ A = .const family ls)
    (HG : RecordCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ x) (proofErase Γ y)) :
    ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ B) (proofErase Γ x) (proofErase Γ y) := by
  obtain ⟨_, hA⟩ := hx.isType henv hΓ
  obtain ⟨ls', R, HL⟩ := proofErase_carrier_aligned_nullary_levels_exposure hstep hn hΓ hA hB H EA
  obtain ⟨B', HB, EB'⟩ := proofErase_scoped_compute_realize hstep hΓ hB rfl rfl R
  have V : StructuralVariant (proofErase Γ A) (proofErase Γ B') := by
    rw [EA, EB']
    exact .const HL
  have HG' := proofErase_carrier_aligned_record_variant hstep hΓ hx hy HB.hasType.2 V HG
  exact .carrierCompute R (by simpa only [EB'] using HG'.computed)

/-- Native Pi selection retains an argument guard for arbitrary recursive
record certificates at a nullary assigned carrier. Exact recovery at the
assigned Pi is not required, and no recursive field guard is replaced by an
ordinary comparison premise. -/
theorem proofErase_carrier_aligned_recovered_nullary_record_guard
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = .const family ls)
    (HG : RecordCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ x) (proofErase Γ y)) :
    ∃ D C, env.HasType univs Γ f (.forallE D C) ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ D) (proofErase (D :: Γ) C)) ∧
      CarrierAlignedCompare Step (proofEraseCtx Γ) false (proofErase Γ A) (proofErase Γ D) ∧
      ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ D) (proofErase Γ x) (proofErase Γ y) := by
  obtain ⟨D, C, hfDC, RD, HD⟩ := proofErase_carrier_aligned_recovered_pi_domain hstep hhead hΓ hf R H
  obtain ⟨_, hPi⟩ := hfDC.isType henv hΓ
  obtain ⟨⟨_, hD⟩, _, _⟩ := hPi.forallE_inv henv
  exact ⟨D, C, hfDC, RD, HD,
    proofErase_carrier_aligned_nullary_record_target hstep hn hΓ hx hy hD HD EA HG⟩

/-- The existing computed application rule accepts actual argument erasures
checked by recursive records. Actual common function and argument typings also
cover the case where the application result erases to the proof marker. -/
theorem proofErase_carrier_aligned_typed_application_nullary_record
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = .const family ls)
    (HG : RecordCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ x) (proofErase Γ y))
    (HF : ComputedJointCompare Step (proofEraseCtx Γ) false (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCompare Step (proofEraseCtx Γ) resultMode
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) := by
  have HFG := ((proofErase_computed_joint_compare_reflect hstep hΓ hf hg HF).1
    (by obtain ⟨u, hPi⟩ := hf.isType henv hΓ; exact .refl ⟨_, hPi⟩)).of_l henv hΓ hf
  have HXY := proofErase_computed_joint_carrier_reflect hstep hΓ hx hy HG.computed
  have HE := HFG.appDF HXY
  by_cases hproof : IsProof Γ (.app f x)
  · rw [proofErase_eq_proof.2 hproof,
      proofErase_eq_proof.2 (isProof_of_common_type hΓ HE.hasType.1 HE.hasType.2 hproof)]
    exact .leaf .refl
  · have hproof' : ¬ IsProof Γ (.app g y) :=
      fun hp' => hproof (isProof_of_common_type hΓ HE.hasType.2 HE.hasType.1 hp')
    rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hproof,
      show proofErase Γ (.app g y) = .app _ _ from if_neg hproof']
    obtain ⟨_, _, _, RD, _, HG'⟩ := proofErase_carrier_aligned_recovered_nullary_record_guard
      hstep hhead hn hΓ hf hx hy R H EA HG
    exact .appCarrier RD HF HG'

/-- Canonical Eq and sound declarations discharge the primitive interfaces at
the full recovered-carrier union. Projection registration supplies rigidity of
the assigned family; the initial function recovery and alignment remain inputs. -/
theorem proofErase_carrier_aligned_union_application_nullary_record
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (R : ScopedTypeRecovery (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) mode T
      (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = .const family ls)
    (HG : RecordCarrierGuard (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ x) (proofErase Γ y))
    (HF : ComputedJointCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) false
      (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) resultMode
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) :=
  proofErase_carrier_aligned_typed_application_nullary_record
    (erased_carrier_recovered_union_descent heq hs) erased_carrier_recovered_union_head
    (fun H => erased_carrier_recovered_union_no_rigid heq (henv.projectionRigid hi) hD H rfl)
    hΓ hf hg hx hy R H EA HG HF

end Lean4Lean.VEnv.Strengthening
