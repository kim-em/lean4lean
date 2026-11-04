import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedComputedSpineExposure

/-! # Parameterized field guards from complete computed type checking

The computed checker exposes parameterized families at equivalent universes.
Static proof-field metadata therefore transfers to the exposed instance, while
all retained projection comparisons remain unchanged. Native Pi selection keeps
its domain comparison in this same computed language, including appComputed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private computed_domain_exposure_pair
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedDomainExposure
variable [Params]

/-- Native Pi selection retains a computed domain comparison when its supplied
type comparison belongs to the full computed checker. No old root-head premise
or arbitrary aligned-comparison exposure is used. -/
theorem proofErase_carrier_aligned_computed_recovered_pi_domain
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ A B out}, ¬ Step Δ (.forallE A B) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : ComputedJointCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B))) :
    ∃ D C, env.HasType univs Γ f (.forallE D C) ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ D) (proofErase (D :: Γ) C)) ∧
      ComputedJointCompare Step (proofEraseCtx Γ) false (proofErase Γ A) (proofErase Γ D) := by
  obtain ⟨F, hfF, EF⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf R
  obtain ⟨_, hF⟩ := hfF.isType henv hΓ
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  have EPi : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hPi)
  have HI := proofErase_computed_joint_types_inferred hstep hΓ hPi hF
    (by simpa only [EF] using H.symm)
  rw [EPi] at HI
  obtain ⟨D', C', RT, HD⟩ := (computed_domain_exposure_pair hn HI rfl).1 _ _ rfl
  rw [EF] at RT
  have R' := R.convert RT
  obtain ⟨D, C, hfDC, ED, EC⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ hΓ
    (show Ctx.LiftN 0 0 Γ Γ from .zero []) hf
    (by simpa only [ProofShape.liftN_zero] using R')
  simp only [ProofShape.liftN_zero] at ED EC
  rw [← ED, ← EC] at R'
  rw [← ED] at HD
  obtain ⟨_, hDC⟩ := hfDC.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
  obtain ⟨⟨_, hD⟩, _, _⟩ := hDC.forallE_inv henv
  exact ⟨D, C, hfDC, R', proofErase_computed_joint_types_inferred hstep hΓ hA hD HD⟩

/-- All retained field comparisons transfer to a selected parameterized carrier.
Its universe instance and parameter syntax may change. The field premises are
ordinary computed comparisons, not carrier-valued dependent field guards. -/
theorem proofErase_carrier_aligned_parameterized_fields_target
    (hstep : ErasedScopedPrimitiveDescent Step) (hn : SpineRootLevels Step family)
    (hi : env.projections family info) (hx : info.nindices = 0) (hp : ps.length = info.nparams)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (H : ComputedJointCompare Step (proofEraseCtx Γ) mode (proofErase Γ A) (proofErase Γ B))
    (EA : proofErase Γ A = ProofShape.mkApps (.const family ls) ps)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (Hfields : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      ComputedJointCompare Step (proofEraseCtx Γ) true (.proj family i x) (.proj family i y)) :
    ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ B) x y := by
  obtain ⟨ls', ps', R, HL, hlen⟩ := proofErase_carrier_aligned_computed_family_exposure hstep hn hΓ hA hB H EA
  obtain ⟨B', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hB rfl rfl R
  obtain ⟨args, rfl, _⟩ := proofErase_const_spine_inv EA
  obtain ⟨args', rfl, _⟩ := proofErase_const_spine_inv EB
  obtain ⟨_, hhead⟩ := (show VExpr.WF env univs Γ (VExpr.mkApps (.const family ls) args) from ⟨_, hA⟩).of_mkApps henv hΓ
  obtain ⟨_, hhead'⟩ := (show VExpr.WF env univs Γ (VExpr.mkApps (.const family ls') args') from ⟨_, HB.hasType.2⟩).of_mkApps henv hΓ
  have hs := StructureReplay.family_instance_levels hi hΓ hhead
  have ht := StructureReplay.family_instance_levels hi hΓ hhead'
  exact .carrierCompute R (ComputedJointCarrierGuard.fields_congr_levels hi hx (hlen.trans hp)
    hs.1 ht.1 hs.2 HL hadm Hfields)

/-- Native Pi selection and parameterized field transfer compose at the same
primitive relation, retaining the selected actual typing and domain comparison. -/
theorem proofErase_carrier_aligned_computed_recovered_parameterized_fields
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hpi : ∀ {Δ A B out}, ¬ Step Δ (.forallE A B) out) (hn : SpineRootLevels Step family)
    (hi : env.projections family info) (hx : info.nindices = 0) (hp : ps.length = info.nparams)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : ComputedJointCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = ProofShape.mkApps (.const family ls) ps)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (Hfields : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      ComputedJointCompare Step (proofEraseCtx Γ) true (.proj family i x) (.proj family i y)) :
    ∃ D C, env.HasType univs Γ f (.forallE D C) ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ D) (proofErase (D :: Γ) C)) ∧
      ComputedJointCompare Step (proofEraseCtx Γ) false (proofErase Γ A) (proofErase Γ D) ∧
      ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ D) x y := by
  obtain ⟨D, C, hfDC, RD, HD⟩ := proofErase_carrier_aligned_computed_recovered_pi_domain hstep hpi hΓ hf R H
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨_, hPi'⟩ := hfDC.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
  obtain ⟨⟨_, hD⟩, _, _⟩ := hPi'.forallE_inv henv
  exact ⟨D, C, hfDC, RD, HD,
    proofErase_carrier_aligned_parameterized_fields_target hstep hn hi hx hp hΓ hA hD HD EA hadm Hfields⟩

end Lean4Lean.VEnv.Strengthening
