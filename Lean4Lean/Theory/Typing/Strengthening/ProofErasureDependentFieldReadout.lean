import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureDependentRecord
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBoxFieldReadout

/-! # Symmetric field readout for a dependent pair

A pair's value-field carrier is its first projection. Symmetry may therefore
leave the value certificate at either major's type. Recording that alternative
permits exact readout without assuming transport between equal field types.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private dependent_recipes
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureDependentRecord
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

namespace ProofShape
/-- Compare the type fields and check the values at either of those types.
The disjunction records the orientation of a supplied carrier derivation;
it does not assume transport from one field type to the other. -/
def DependentPairFieldCheck (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (family : Name) (a b : ProofShape) : Prop :=
  JointCompare Step Δ true (.proj family 0 a) (.proj family 0 b) ∧
    (JointCarrierGuard Step Δ (.proj family 0 a) (.proj family 1 a) (.proj family 1 b) ∨
     JointCarrierGuard Step Δ (.proj family 0 b) (.proj family 1 a) (.proj family 1 b))

/-- Reversing the majors exchanges the two possible field carriers. -/
theorem DependentPairFieldCheck.symm (H : DependentPairFieldCheck Step Δ family a b) :
    DependentPairFieldCheck Step Δ family b a := by
  refine ⟨.symm H.1, ?_⟩
  rcases H.2 with H | H
  · exact .inr (.carrierSymm H)
  · exact .inl (.carrierSymm H)

/-- Major computation pulls back both the chosen field carrier and the values. -/
theorem DependentPairFieldCheck.compute
    (RA : ScopedCompute Step Δ a a') (RB : ScopedCompute Step Δ b b')
    (H : DependentPairFieldCheck Step Δ family a' b') :
    DependentPairFieldCheck Step Δ family a b := by
  refine ⟨.compute (.proj RA) (.proj RB) H.1, ?_⟩
  rcases H.2 with H | H
  · exact .inl (.carrierCompute (.proj RA) (.carrierReduce (.proj RA) (.proj RB) H))
  · exact .inr (.carrierCompute (.proj RB) (.carrierReduce (.proj RA) (.proj RB) H))

/-- Either orientation reconstructs the original dependent pair guard. -/
theorem DependentPairFieldCheck.pack
    (hi : env.projections family info) (hz : info.nindices = 0)
    (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hadm : (info.resultLevel.inst []).IsNeverZero)
    (H : DependentPairFieldCheck Step Δ family a b) :
    JointCarrierGuard Step Δ (.const family []) a b := by
  have pack_left {a b : ProofShape}
      (HTy : JointCompare Step Δ true (.proj family 0 a) (.proj family 0 b))
      (HV : JointCarrierGuard Step Δ (.proj family 0 a) (.proj family 1 a) (.proj family 1 b)) :
      JointCarrierGuard Step Δ (.const family []) a b := by
    obtain ⟨doms, result, HT⟩ := projection_telescope_exists (ls := []) hi (by simp)
    apply JointCheck.carrierNested hi hz (ps := []) hp.symm (.inl hadm) HT
    intro i hj hn
    obtain ⟨E₀, E₁⟩ := dependent_recipes (major := a) hp hf hshape HT
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl
    · rw [E₀]
      exact .carrierChecked HTy
    · rw [E₁]
      exact HV
  rcases H.2 with HV | HV
  · exact pack_left H.1 HV
  · exact .carrierSymm (pack_left (.symm H.1) (.carrierSymm HV))
end ProofShape

/-- The dependent pair registration determines both actual projection types. -/
theorem dependent_pair_projections_typed
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x (.const family [])) :
    env.HasType univs Γ (.proj family 0 x) (.sort (.succ .zero)) ∧
      env.HasType univs Γ (.proj family 1 x) (.proj family 0 x) := by
  have hexp := (StructureReplay.expansion_typed_iff henv hΓ hi
    (show ([] : List VExpr).length = info.nparams from hp.symm) hz hx).2 (.inl hadm)
  obtain ⟨ci, Hci, _, hls⟩ := (VExpr.WF.of_mkApps henv hΓ ⟨_, hexp⟩).const_inv henv hΓ
  rw [henv.ordered.projectionConstructor hi] at Hci
  cases Option.some.inj Hci
  have hu : info.uvars = 0 := hls.symm
  have hproj (i) (hj : i < info.numFields) : VExpr.WF env univs Γ (.proj family i x) := by
    obtain ⟨F, H⟩ := structure_expansion_projection_typed hΓ hexp hj
    exact ⟨F, H⟩
  constructor
  · apply projection_at_recovered_family (ls := []) (args := []) henv hΓ hi (hproj 0 (by omega)) hx
    simp [VProjectionInfo.fieldType, hp, hu, hshape,
      VProjectionInfo.instantiateProjectionParameters, VProjectionInfo.instantiateProjectionFields]
  · apply projection_at_recovered_family (ls := []) (args := []) henv hΓ hi (hproj 1 (by omega)) hx
    simp [VProjectionInfo.fieldType, hp, hu, hshape,
      VProjectionInfo.instantiateProjectionParameters, VProjectionInfo.instantiateProjectionFields,
      VExpr.inst, VExpr.instVar_zero]

private theorem pair_fields_raw
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ args out}, ¬ Step Δ (ProofShape.mkApps (.const family []) args) out)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (H : JointCheck Step Δ kind a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (EΓ : proofEraseCtx Γ = Δ) (Ex : proofErase Γ x = a) (Ey : proofErase Γ y = b)
    (E : JointCheckKind.carrier (.const family []) = kind) :
    DependentPairFieldCheck Step Δ family a b := by
  induction H generalizing Γ x y with
  | carrierChecked H =>
    cases E
    obtain ⟨hTx, hVx⟩ := dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hx
    obtain ⟨hTy, hVy⟩ := dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hy
    have ETx : proofErase Γ (.proj family 0 x) = .proj family 0 (proofErase Γ x) :=
      if_neg (not_isProof_of_sort hΓ hTx)
    have ETy : proofErase Γ (.proj family 0 y) = .proj family 0 (proofErase Γ y) :=
      if_neg (not_isProof_of_sort hΓ hTy)
    have EVx : proofErase Γ (.proj family 1 x) = .proj family 1 (proofErase Γ x) :=
      if_neg (not_proof_at_positive_type hΓ hTx hVx)
    have EVy : proofErase Γ (.proj family 1 y) = .proj family 1 (proofErase Γ y) :=
      if_neg (not_proof_at_positive_type hΓ hTy hVy)
    have HC : JointCompare Step (proofEraseCtx Γ) true (proofErase Γ x) (proofErase Γ y) :=
      by simpa only [EΓ, Ex, Ey] using H
    have HT := proofErase_joint_project hstep hprim hΓ hx hy hTx HC
    have HV := proofErase_joint_project hstep hprim hΓ hx hy hVx HC
    refine ⟨?_, .inl (.carrierChecked ?_)⟩
    · simpa only [EΓ, ETx, ETy, Ex, Ey] using HT
    · simpa only [EΓ, EVx, EVy, Ex, Ey] using HV
  | carrierFunction => cases E
  | carrierSubsingleton HS =>
    cases E
    have Hzero := SubsingletonCarrier.record_numFields (ps := []) hi HS
    omega
  | carrierSymm H ih => exact (ih hΓ hy hx EΓ Ey Ex E).symm
  | carrierReduce RA RB H ih =>
    obtain ⟨x', HX, EX⟩ := proofErase_scoped_compute_realize hstep hΓ hx EΓ Ex RA
    obtain ⟨y', HY, EY⟩ := proofErase_scoped_compute_realize hstep hΓ hy EΓ Ey RB
    exact (ih hΓ HX.hasType.2 HY.hasType.2 EΓ EX EY E).compute RA RB
  | carrierCompute R H ih =>
    cases E
    have RR : ScopedCompute Step _ (ProofShape.mkApps (.const family []) []) _ := R
    obtain ⟨ps', Eout, RP⟩ := RR.const_spine hinert
    cases RP
    exact ih hΓ hx hy EΓ Ex Ey (by rw [Eout]; rfl)
  | carrierIntro hi' hz' hlen hadm' HF =>
    obtain ⟨rfl, rfl, rfl⟩ := ProofShape.const_spine_inj
      (show ProofShape.mkApps (.const family []) [] = _ from JointCheckKind.carrier.inj E)
    cases henv.ordered.projections_unique hi hi'
    have hexp := (StructureReplay.expansion_typed_iff henv hΓ hi
      (show ([] : List VExpr).length = info.nparams from hp.symm) hz hx).2 (.inl hadm)
    obtain ⟨hTx, hVx⟩ := dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hx
    have hn0 : ¬ StructureReplay.ProofField env univs info [] 0 := fun H =>
      not_isProof_of_sort hΓ hTx (H.projection hΓ hi (show ([] : List VExpr).length = info.nparams from hp.symm) hexp)
    have hn1 : ¬ StructureReplay.ProofField env univs info [] 1 := fun H =>
      not_proof_at_positive_type hΓ hTx hVx (H.projection hΓ hi (show ([] : List VExpr).length = info.nparams from hp.symm) hexp)
    exact ⟨HF 0 (by omega) hn0, .inl (.carrierChecked (HF 1 (by omega) hn1))⟩
  | carrierNested hi' hz' hlen hadm' PT HF =>
    obtain ⟨rfl, rfl, rfl⟩ := ProofShape.const_spine_inj
      (show ProofShape.mkApps (.const family []) [] = _ from JointCheckKind.carrier.inj E)
    cases henv.ordered.projections_unique hi hi'
    have hexp := (StructureReplay.expansion_typed_iff henv hΓ hi
      (show ([] : List VExpr).length = info.nparams from hp.symm) hz hx).2 (.inl hadm)
    obtain ⟨hTx, hVx⟩ := dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hx
    have hn0 : ¬ StructureReplay.ProofField env univs info [] 0 := fun H =>
      not_isProof_of_sort hΓ hTx (H.projection hΓ hi (show ([] : List VExpr).length = info.nparams from hp.symm) hexp)
    have hn1 : ¬ StructureReplay.ProofField env univs info [] 1 := fun H =>
      not_proof_at_positive_type hΓ hTx hVx (H.projection hΓ hi (show ([] : List VExpr).length = info.nparams from hp.symm) hexp)
    obtain ⟨E₀, E₁⟩ := dependent_recipes hp hf hshape PT
    have HT := HF 0 (by omega) hn0
    have HV := HF 1 (by omega) hn1
    rw [E₀] at HT
    rw [E₁] at HV
    exact ⟨JointCarrierGuard.sort_checked hhead HT, .inl HV⟩
  | leaf | app | appCarrier | proj | lam | forallE | lamSorted | forallSorted | lamCommon |
      etaBodyL | etaBodyR | structFields | etaLams | compute | symm => cases E

/-- An arbitrary typed dependent-pair guard exposes its type-field comparison
and its value check at one of the two field types. No general carrier
conversion is used to choose the left field type. -/
theorem proofErase_dependent_pair_fields
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ args out}, ¬ Step Δ (ProofShape.mkApps (.const family []) args) out)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (H : JointCarrierGuard Step (proofEraseCtx Γ) (.const family [])
      (proofErase Γ x) (proofErase Γ y)) :
    DependentPairFieldCheck Step (proofEraseCtx Γ) family (proofErase Γ x) (proofErase Γ y) :=
  pair_fields_raw hstep hprim hhead hinert hi hp hf hz hadm hshape H hΓ hx hy rfl rfl rfl rfl

end Lean4Lean.VEnv.Strengthening
