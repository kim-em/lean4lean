import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedNullaryExposure
import Lean4Lean.Theory.Typing.Strengthening.StructureProofFieldUniverses

/-! # Rebuilding fieldwise guards at a selected native carrier

Nullary family exposure retains universe equivalence. That equivalence preserves
projection admissibility and the exact static proof-field predicate. Existing
recursive comparison certificates for all retained projections therefore build a
carrier guard at the exposed family and then at the selected native domain.
This handles fieldwise guards; recursive carrier-valued field guards remain separate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Fieldwise checking changes universe instances while retaining the raw
parameters, endpoints and every recursive projection comparison. Static proof
fields may be omitted at either instance, because their predicates agree. -/
theorem ProofShape.ComputedJointCarrierGuard.fields_congr_levels
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams)
    (hw : ∀ l ∈ ls, l.WF univs) (hw' : ∀ l ∈ ls', l.WF univs)
    (hl : ls.length = info.uvars) (he : List.Forall₂ (· ≈ ·) ls ls')
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (H : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      ComputedJointCompare Step Δ true (.proj family i a) (.proj family i b)) :
    ComputedJointCarrierGuard Step Δ (mkApps (.const family ls') ps) a b := by
  have hadm' : (info.resultLevel.inst ls').IsNeverZero ∨ StructureReplay.ProofFields env univs info ls' := by
    rcases hadm with hpos | hproof
    · exact .inl (hpos.of_equiv (VLevel.inst_congr rfl he))
    · exact .inr (hproof.level_congr henv hi hw hw' hl he)
  apply ComputedJointCheck.carrierIntro hi hx hp hadm'
  intro i hj hn
  exact H i hj (fun Hproof => hn (Hproof.congr_levels hi hw hw' hl he))

/-- A typed aligned comparison transfers all retained field comparisons to a
selected nullary structure carrier. Universe well-formedness and arity are
reconstructed from actual source and exposed-target typings. -/
theorem proofErase_carrier_aligned_nullary_fields_target
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (hi : env.projections family info) (hx : info.nindices = 0) (hp : info.nparams = 0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b))
    (Ea : proofErase Γ a = .const family ls)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (Hfields : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      ComputedJointCompare Step (proofEraseCtx Γ) true (.proj family i x) (.proj family i y)) :
    ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ b) x y := by
  obtain ⟨ls', R, HL⟩ := proofErase_carrier_aligned_nullary_levels_exposure hstep hn hΓ ha hb H Ea
  obtain ⟨b', HB, Eb'⟩ := proofErase_scoped_compute_realize hstep hΓ hb rfl rfl R
  obtain rfl := erase_const_inv Ea
  obtain rfl := erase_const_inv Eb'
  have hsource := StructureReplay.family_instance_levels hi hΓ ha
  have htarget := StructureReplay.family_instance_levels hi hΓ HB.hasType.2
  exact .carrierCompute R (ComputedJointCarrierGuard.fields_congr_levels hi hx (ps := []) hp.symm
    hsource.1 htarget.1 hsource.2 HL hadm Hfields)

/-- Native Pi selection supplies its domain comparison and the corresponding
fieldwise argument guard together. The domain may differ from the assigned
syntax; neither empty fields nor exact assigned-Pi recovery is required. -/
theorem proofErase_carrier_aligned_recovered_nullary_fields_guard
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (hi : env.projections family info) (hx : info.nindices = 0) (hp : info.nparams = 0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = .const family ls)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (Hfields : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      ComputedJointCompare Step (proofEraseCtx Γ) true (.proj family i x) (.proj family i y)) :
    ∃ D C, env.HasType univs Γ f (.forallE D C) ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ D) (proofErase (D :: Γ) C)) ∧
      CarrierAlignedCompare Step (proofEraseCtx Γ) false (proofErase Γ A) (proofErase Γ D) ∧
      ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ D) x y := by
  obtain ⟨D, C, hfDC, RD, HD⟩ := proofErase_carrier_aligned_recovered_pi_domain hstep hhead hΓ hf R H
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨_, hPi'⟩ := hfDC.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
  obtain ⟨⟨_, hD⟩, _, _⟩ := hPi'.forallE_inv henv
  exact ⟨D, C, hfDC, RD, HD,
    proofErase_carrier_aligned_nullary_fields_target hstep hn hi hx hp hΓ hA hD HD EA hadm Hfields⟩

/-- The reconstructed nonempty-field guard closes the computed application
rule without changing its function or argument endpoints. -/
theorem proofErase_carrier_aligned_application_nullary_fields
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (hi : env.projections family info) (hx : info.nindices = 0) (hp : info.nparams = 0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = .const family ls)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (Hfields : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      ComputedJointCompare Step (proofEraseCtx Γ) true (.proj family i x) (.proj family i y))
    (HF : ComputedJointCompare Step (proofEraseCtx Γ) false (proofErase Γ f) g) :
    ComputedJointCompare Step (proofEraseCtx Γ) resultMode (.app (proofErase Γ f) x) (.app g y) := by
  obtain ⟨_, _, _, RD, _, HG⟩ := proofErase_carrier_aligned_recovered_nullary_fields_guard
    hstep hhead hn hi hx hp hΓ hf R H EA hadm Hfields
  exact .appCarrier RD HF HG

/-- The fieldwise selected-domain certificate checks actual application
erasures, including proof-valued applications. Actual arguments have the common
assigned domain, and only retained projections require recursive comparison. -/
theorem proofErase_carrier_aligned_typed_application_nullary_fields
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (hi : env.projections family info) (hindices : info.nindices = 0)
    (hp : info.nparams = 0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = .const family ls)
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
    exact .carrierIntro hi hindices (ps := []) hp.symm hadm Hfields
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
    exact proofErase_carrier_aligned_application_nullary_fields
      hstep hhead hn hi hindices hp hΓ hf R H EA hadm Hfields HF

/-- The full recovered-carrier union discharges all primitive interfaces for
native selection with a rigid nullary fieldwise carrier. Nonempty structures and
mixed proof/data fields are allowed; the supplied projection checks remain explicit. -/
theorem proofErase_carrier_aligned_union_nullary_fields_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hrigid : env.Rigid family) (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : info.nparams = 0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) mode T
      (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = .const family ls)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (Hfields : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      ComputedJointCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) true
        (.proj family i x) (.proj family i y)) :
    ∃ A' B', env.HasType univs Γ f (.forallE A' B') ∧
      ScopedTypeRecovery (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ A') (proofErase (A' :: Γ) B')) ∧
      CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) false
        (proofErase Γ A) (proofErase Γ A') ∧
      ComputedJointCarrierGuard (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ A') x y :=
  proofErase_carrier_aligned_recovered_nullary_fields_guard
    (erased_carrier_recovered_union_descent heq hs) erased_carrier_recovered_union_head
    (fun H => erased_carrier_recovered_union_no_rigid heq hrigid hD H rfl)
    hi hx hp hΓ hf R H EA hadm Hfields

end Lean4Lean.VEnv.Strengthening
