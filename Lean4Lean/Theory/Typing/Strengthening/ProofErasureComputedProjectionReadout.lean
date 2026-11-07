import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCoreWorlds
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureClosedCarrierReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedCarrierTypeChecking
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentFieldReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointDescent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedProjectionSupport

/-! # Projection and dependent field readout for computed comparisons

The comparison induction includes domains recovered by computing functions. Exposed
constructors select their smaller field comparison; computation replays at the
original major type. Actual carrier equality to the closed record is retained through carrier
computation. Dependent value checks keep their chosen left/right field type;
no comparison transitivity or transport between those field types is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

private theorem project_inferred (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (ht : env.HasType univs Γ (.proj s i a) T)
    (H : ProofShape.ComputedJointCompare Step (proofEraseCtx Γ) false (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ComputedJointCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ (.proj s i a)) (proofErase Γ (.proj s i b)) := by
  have HAB := (proofErase_computed_joint_compare_reflect hstep hΓ ha hb H).1
    ⟨_, (ha.isType henv hΓ).choose_spec⟩
  have HP := SimAt.proj henv.orderedStrong hΓ (fun _ ht => HAB.of_l henv hΓ ht) T ht
  by_cases hp : IsProof Γ (.proj s i a)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HP).1 hp)]
    exact .leaf .refl
  · have hp' := mt (isProof_congr hΓ HP).2 hp
    rw [show proofErase Γ (.proj s i a) = .proj s i (proofErase Γ a) from if_neg hp,
      show proofErase Γ (.proj s i b) = .proj s i (proofErase Γ b) from if_neg hp']
    exact .proj H

private theorem structure_project
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, ProofShape.Primitive D a b → ProofShape.ScopedCompute Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (ht : env.HasType univs Γ (.proj family i a) T)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams) (hf : fields.length = info.numFields)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (Ea : proofErase Γ a = ProofShape.mkApps (.const info.ctorName ls) (ps ++ fields))
    (H : ∀ j (h : j < fields.length), fields[j] ≠ .proof →
      ProofShape.ComputedJointCompare Step (proofEraseCtx Γ) true fields[j]
        (.proj family j (proofErase Γ b)))
    (hidx : i < fields.length) :
    ProofShape.ComputedJointCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.proj family i a)) (proofErase Γ (.proj family i b)) := by
  have HM : ProofShape.ComputedJointCompare Step (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b) := by
    rw [Ea]
    exact .structFields hi hx hp hf hadm H
  have HAB := proofErase_computed_joint_carrier_reflect hstep hΓ ha hb (.carrierChecked HM)
  have HP := SimAt.proj henv.orderedStrong hΓ (fun _ ht => HAB.toU.of_l henv hΓ ht) T ht
  by_cases hproof : IsProof Γ (.proj family i a)
  · rw [proofErase_eq_proof.2 hproof, proofErase_eq_proof.2 ((isProof_congr hΓ HP).1 hproof)]
    exact .leaf .refl
  have hproof' := mt (isProof_congr hΓ HP).2 hproof
  have Eleft : proofErase Γ (.proj family i a) =
      .proj family i (ProofShape.mkApps (.const info.ctorName ls) (ps ++ fields)) := by
    rw [show proofErase Γ (.proj family i a) = .proj family i (proofErase Γ a) from if_neg hproof, Ea]
  have R : ProofShape.ScopedCompute Step (proofEraseCtx Γ)
      (proofErase Γ (.proj family i a)) fields[i] := by
    rw [Eleft]
    apply hprim
    apply ProofShape.Primitive.projIota hi (by simp [hp, hf])
    rw [← hp, List.getElem?_append_right (by omega)]
    simp [hidx]
  have hn : fields[i] ≠ .proof := by
    intro E
    have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨out, HE, EE⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ W ht rfl
      (by simpa only [ProofShape.liftN_zero] using R)
    simp only [ProofShape.liftN_zero] at EE
    exact hproof ((isProof_congr hΓ HE).2 (proofErase_eq_proof.1 (EE.trans E)))
  rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hproof']
  exact .compute R .refl (H i hidx hn)

/-- Every typed computed comparison projects at common original major and field
types, including recursive carrier comparisons inside applications. -/
theorem proofErase_computed_joint_project_typed
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, ProofShape.Primitive D a b → ProofShape.ScopedCompute Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (hta : env.HasType univs Γ (.proj s i a) T) (htb : env.HasType univs Γ (.proj s i b) T)
    (H : ProofShape.ComputedJointCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ComputedJointCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.proj s i a)) (proofErase Γ (.proj s i b)) := by
  generalize EΔ : proofEraseCtx Γ = Δ at H
  generalize Ea : proofErase Γ a = sa at H
  generalize Eb : proofErase Γ b = sb at H
  change ProofShape.ComputedJointCheck Step Δ (.compare mode) sa sb at H
  generalize EK : ProofShape.JointCheckKind.compare mode = kind at H
  induction H generalizing a b A T mode with
  | leaf H =>
    cases EK
    cases H with
    | refl =>
      rw [← EΔ]
      exact project_inferred hstep hΓ ha hb hta
        (by rw [EΔ, Ea, Eb]; exact .leaf .refl)
    | sort H =>
      rw [← EΔ]
      exact project_inferred hstep hΓ ha hb hta
        (by rw [EΔ, Ea, Eb]; exact .leaf (.sort H))
    | const H =>
      rw [← EΔ]
      exact project_inferred hstep hΓ ha hb hta
        (by rw [EΔ, Ea, Eb]; exact .leaf (.const H))
    | etaL H =>
      obtain ⟨_, _, E, _⟩ := H.shape
      exact (proofErase_projection_not_lam hΓ hta (Ea.trans E)).elim
    | etaR H =>
      obtain ⟨_, _, E, _⟩ := H.shape
      exact (proofErase_projection_not_lam hΓ htb (Eb.trans E)).elim
  | app Hf Hx =>
    rw [← EΔ]
    exact project_inferred hstep hΓ ha hb hta
      (by rw [EΔ, Ea, Eb]; exact .app Hf Hx)
  | appCarrier R Hf Hx =>
    rw [← EΔ]
    exact project_inferred hstep hΓ ha hb hta
      (by rw [EΔ, Ea, Eb]; exact .appCarrier R Hf Hx)
  | appComputed R Hf Hx =>
    rw [← EΔ]
    exact project_inferred hstep hΓ ha hb hta
      (by rw [EΔ, Ea, Eb]; exact .appComputed R Hf Hx)
  | proj H =>
    rw [← EΔ]
    exact project_inferred hstep hΓ ha hb hta
      (by rw [EΔ, Ea, Eb]; exact .proj H)
  | forallE HD HB =>
    rw [← EΔ]
    exact project_inferred hstep hΓ ha hb hta
      (by rw [EΔ, Ea, Eb]; exact .forallE HD HB)
  | forallSorted SA SA' HD SB SB' HB =>
    rw [← EΔ]
    exact project_inferred hstep hΓ ha hb hta
      (by rw [EΔ, Ea, Eb]; exact .forallSorted SA SA' HD SB SB' HB)
  | lam | lamSorted | lamCommon | etaBodyL | etaLams =>
    exact (proofErase_projection_not_lam hΓ hta Ea).elim
  | etaBodyR => exact (proofErase_projection_not_lam hΓ htb Eb).elim
  | structFields hi hx hp hf hadm HF =>
    obtain ⟨ES, hidx⟩ := proofErase_projection_constructor_family hΓ hta hi hx hp hf Ea
    subst s
    rw [← EΔ]
    exact structure_project hstep hprim hΓ ha hb hta hi hx hp hf hadm Ea
      (by simpa only [EΔ, Eb] using HF) hidx
  | compute Ra Rb _ ih =>
    have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ W ha EΔ
      (by simpa only [ProofShape.liftN_zero, Ea] using Ra)
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ W hb EΔ
      (by simpa only [ProofShape.liftN_zero, Eb] using Rb)
    simp only [ProofShape.liftN_zero] at EA EB
    have hta' := (SimAt.proj henv.orderedStrong hΓ
      (fun _ ht => (show env.IsDefEqU univs Γ a a' from ⟨_, HA⟩).of_l henv hΓ ht) T hta).hasType.2
    have htb' := (SimAt.proj henv.orderedStrong hΓ
      (fun _ ht => (show env.IsDefEqU univs Γ b b' from ⟨_, HB⟩).of_l henv hΓ ht) T htb).hasType.2
    exact .compute
      (proofErase_scoped_compute_project hΓ HA hta (by rwa [Ea, EA]))
      (proofErase_scoped_compute_project hΓ HB htb (by rwa [Eb, EB]))
      (ih HA.hasType.2 HB.hasType.2 hta' htb' EΔ EA EB EK)
  | symm _ ih => exact .symm (ih hb ha htb hta EΔ Eb Ea EK)
  | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases EK

/-- A single original projection typing suffices. Computed reflection constructs
the second projection's common field type before applying projection closure. -/
theorem proofErase_computed_joint_project
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, ProofShape.Primitive D a b → ProofShape.ScopedCompute Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (ht : env.HasType univs Γ (.proj s i a) T)
    (H : ProofShape.ComputedJointCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ComputedJointCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.proj s i a)) (proofErase Γ (.proj s i b)) := by
  have HAB := (proofErase_computed_joint_compare_reflect hstep hΓ ha hb H).1
    ⟨_, (ha.isType henv hΓ).choose_spec⟩
  have HP := SimAt.proj henv.orderedStrong hΓ (fun _ ht => HAB.of_l henv hΓ ht) T ht
  exact proofErase_computed_joint_project_typed hstep hprim hΓ ha hb ht HP.hasType.2 H

open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private dependent_recipes
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureDependentRecord
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary

open private rigid_spine_eq_closed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureClosedCarrierReadout
open private erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

namespace ProofShape
/-- Compare the type fields and check the values at either of those types.
The disjunction records the orientation of a supplied carrier derivation;
it does not assume transport from one field type to the other. -/
def ComputedDependentPairFieldCheck (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (family : Name) (a b : ProofShape) : Prop :=
  ComputedJointCompare Step Δ true (.proj family 0 a) (.proj family 0 b) ∧
    (ComputedJointCarrierGuard Step Δ (.proj family 0 a) (.proj family 1 a) (.proj family 1 b) ∨
     ComputedJointCarrierGuard Step Δ (.proj family 0 b) (.proj family 1 a) (.proj family 1 b))

/-- Reversing the majors exchanges the two possible field carriers. -/
theorem ComputedDependentPairFieldCheck.symm (H : ComputedDependentPairFieldCheck Step Δ family a b) :
    ComputedDependentPairFieldCheck Step Δ family b a := by
  refine ⟨.symm H.1, ?_⟩
  rcases H.2 with H | H
  · exact .inr (.carrierSymm H)
  · exact .inl (.carrierSymm H)

/-- Major computation pulls back both the chosen field carrier and the values. -/
theorem ComputedDependentPairFieldCheck.compute
    (RA : ScopedCompute Step Δ a a') (RB : ScopedCompute Step Δ b b')
    (H : ComputedDependentPairFieldCheck Step Δ family a' b') :
    ComputedDependentPairFieldCheck Step Δ family a b := by
  refine ⟨.compute (.proj RA) (.proj RB) H.1, ?_⟩
  rcases H.2 with H | H
  · exact .inl (.carrierCompute (.proj RA) (.carrierReduce (.proj RA) (.proj RB) H))
  · exact .inr (.carrierCompute (.proj RB) (.carrierReduce (.proj RA) (.proj RB) H))

/-- Either orientation reconstructs the original dependent pair guard. -/
theorem ComputedDependentPairFieldCheck.pack
    (hi : env.projections family info) (hz : info.nindices = 0)
    (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hadm : (info.resultLevel.inst []).IsNeverZero)
    (H : ComputedDependentPairFieldCheck Step Δ family a b) :
    ComputedJointCarrierGuard Step Δ (.const family []) a b := by
  have pack_left {a b : ProofShape}
      (HTy : ComputedJointCompare Step Δ true (.proj family 0 a) (.proj family 0 b))
      (HV : ComputedJointCarrierGuard Step Δ (.proj family 0 a) (.proj family 1 a) (.proj family 1 b)) :
      ComputedJointCarrierGuard Step Δ (.const family []) a b := by
    obtain ⟨doms, result, HT⟩ := projection_telescope_exists (ls := []) hi (by simp)
    apply ComputedJointCheck.carrierNested hi hz (ps := []) hp.symm (.inl hadm) HT
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

private theorem pair_fields_raw
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (H : ComputedJointCheck Step Δ kind a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (HE : env.IsDefEqU univs Γ A (.const family []))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (EΓ : proofEraseCtx Γ = Δ) (Ex : proofErase Γ x = a) (Ey : proofErase Γ y = b)
    (E : JointCheckKind.carrier (proofErase Γ A) = kind) :
    ComputedDependentPairFieldCheck Step Δ family a b := by
  induction H generalizing Γ A u x y with
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
    have HC : ComputedJointCompare Step (proofEraseCtx Γ) true (proofErase Γ x) (proofErase Γ y) :=
      by simpa only [EΓ, Ex, Ey] using H
    have HT := proofErase_computed_joint_project hstep hprim hΓ hx hy hTx HC
    have HV := proofErase_computed_joint_project hstep hprim hΓ hx hy hVx HC
    refine ⟨?_, .inl (.carrierChecked ?_)⟩
    · simpa only [EΓ, ETx, ETy, Ex, Ey] using HT
    · simpa only [EΓ, EVx, EVy, Ex, Ey] using HV
  | carrierFunction =>
    obtain ⟨C, B, rfl, _, _, _⟩ := erase_forallE_inv (JointCheckKind.carrier.inj E)
    exact (henv.headInversion.forallE_rigid (args := []) hΓ (henv.projectionRigid hi)
      (HE.typeChain henv hΓ hA)).elim
  | carrierSubsingleton HS =>
    cases HS with
    | unit hi' hz' hf' hp' =>
      have EC := rigid_spine_eq_closed hΓ (henv.projectionRigid hi)
        (henv.projectionRigid hi') hA HE (JointCheckKind.carrier.inj E)
      obtain ⟨rfl, rfl, rfl⟩ := ProofShape.const_spine_inj
        (show ProofShape.mkApps (.const family []) [] = _ from EC.symm)
      cases henv.ordered.projections_unique hi hi'
      omega
    | forallE HS =>
      obtain ⟨C, B, rfl, _, _, _⟩ := erase_forallE_inv (JointCheckKind.carrier.inj E)
      exact (henv.headInversion.forallE_rigid (args := []) hΓ (henv.projectionRigid hi)
        (HE.typeChain henv hΓ hA)).elim
  | carrierSymm H ih => exact (ih hΓ hA HE hy hx EΓ Ey Ex E).symm
  | carrierReduce RA RB H ih =>
    obtain ⟨x', HX, EX⟩ := proofErase_scoped_compute_realize hstep hΓ hx EΓ Ex RA
    obtain ⟨y', HY, EY⟩ := proofErase_scoped_compute_realize hstep hΓ hy EΓ Ey RB
    exact (ih hΓ hA HE HX.hasType.2 HY.hasType.2 EΓ EX EY E).compute RA RB
  | carrierCompute R H ih =>
    obtain ⟨A', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ
      (JointCheckKind.carrier.inj E) R
    exact ih hΓ HA.hasType.2 (HA.symm.toU.trans henv hΓ HE) hx hy EΓ Ex Ey
      (congrArg JointCheckKind.carrier EA)
  | carrierIntro hi' hz' hlen hadm' HF =>
    have EC := rigid_spine_eq_closed hΓ (henv.projectionRigid hi)
      (henv.projectionRigid hi') hA HE (JointCheckKind.carrier.inj E)
    obtain ⟨rfl, rfl, rfl⟩ := ProofShape.const_spine_inj
      (show ProofShape.mkApps (.const family []) [] = _ from EC.symm)
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
    have EC := rigid_spine_eq_closed hΓ (henv.projectionRigid hi)
      (henv.projectionRigid hi') hA HE (JointCheckKind.carrier.inj E)
    obtain ⟨rfl, rfl, rfl⟩ := ProofShape.const_spine_inj
      (show ProofShape.mkApps (.const family []) [] = _ from EC.symm)
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
    obtain ⟨hTy, _⟩ := dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hy
    have ETx : proofErase Γ (.proj family 0 x) = .proj family 0 (proofErase Γ x) :=
      if_neg (not_isProof_of_sort hΓ hTx)
    have ETy : proofErase Γ (.proj family 0 y) = .proj family 0 (proofErase Γ y) :=
      if_neg (not_isProof_of_sort hΓ hTy)
    have ES : proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) :=
      if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))
    have HT' := proofErase_computed_carrier_types_checked hstep hΓ hTx hTy (.inl hTx)
      (by simpa only [EΓ, ES, ETx, ETy, Ex, Ey] using HT)
    exact ⟨by simpa only [EΓ, ETx, ETy, Ex, Ey] using HT', .inl HV⟩
  | leaf | app | appCarrier | appComputed | proj | lam | forallE | lamSorted | forallSorted | lamCommon |
      etaBodyL | etaBodyR | structFields | etaLams | compute | symm => cases E

/-- An arbitrary typed dependent-pair guard exposes its type-field comparison
and its value check at one of the two field types. No general carrier
conversion is used to choose the left field type. -/
theorem proofErase_computed_dependent_pair_fields
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (H : ComputedJointCarrierGuard Step (proofEraseCtx Γ) (.const family [])
      (proofErase Γ x) (proofErase Γ y)) :
    ComputedDependentPairFieldCheck Step (proofEraseCtx Γ) family (proofErase Γ x) (proofErase Γ y) := by
  obtain ⟨u, hF⟩ := hx.isType henv hΓ
  have EF : proofErase Γ (.const family []) = .const family [] :=
    if_neg (not_isProof_of_sort hΓ hF)
  exact pair_fields_raw hstep hprim hi hp hf hz hadm hshape H hΓ hF (.refl ⟨_, hF⟩)
    hx hy rfl rfl rfl (congrArg JointCheckKind.carrier EF)

/-- An arbitrary actual alias of the registered closed pair has the same
field readout. Sound computation realizes each carrier change; rigid-head
inversion identifies exposed records even after beta or identity expansion.
No inert-family or sort-fixed primitive hypothesis is required. -/
theorem proofErase_computed_dependent_pair_alias_fields
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (HE : env.IsDefEqU univs Γ A (.const family []))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (H : ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ x) (proofErase Γ y)) :
    ComputedDependentPairFieldCheck Step (proofEraseCtx Γ) family
      (proofErase Γ x) (proofErase Γ y) :=
  pair_fields_raw hstep hprim hi hp hf hz hadm hshape H hΓ hA HE hx hy rfl rfl rfl rfl

/-- At actual pair majors, computed carrier checking is exactly type-field
comparison plus value checking at one of the two dependent field types. -/
theorem proofErase_computed_dependent_pair_fields_iff
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family [])) :
    ComputedJointCarrierGuard Step (proofEraseCtx Γ) (.const family [])
      (proofErase Γ x) (proofErase Γ y) ↔
    ComputedDependentPairFieldCheck Step (proofEraseCtx Γ) family
      (proofErase Γ x) (proofErase Γ y) :=
  ⟨proofErase_computed_dependent_pair_fields hstep hprim hi hp hf hz hadm hshape hΓ hx hy,
    fun H => H.pack hi hz hp hf hshape hadm⟩

/-- Current world histories expose the dependent fields after any allowed
future world and independent ordinary-core reductions of the majors, at the
same stage. The left/right choice is made after those operations. This does
not select a fixed value-field carrier or retain arbitrary field residuals;
those remain separate requirements for a full dependent projection action. -/
theorem PiInertWorldHistory.dependent_pair_fields
    {D : PureObservation.Definitions}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (H : PiInertWorldHistory D n (proofEraseCtx Γ) (.const family [])
      (proofErase Γ x) (proofErase Γ y))
    (W : PiInertCoreWorld D (proofEraseCtx Γ) Λ σ)
    (RA : Compute (ErasedLevelCore D) ((proofErase Γ x).subst σ) a)
    (RB : Compute (ErasedLevelCore D) ((proofErase Γ y).subst σ) b) :
    ComputedDependentPairFieldCheck (PiInertStage D n) Λ family a b := by
  obtain ⟨Γ', τ, hΓ', EΓ', WT, ES⟩ := W.typed hΓ rfl
  have hx' : env.HasType univs Γ' (x.subst τ) (.const family []) :=
    hx.subst henv.orderedStrong WT hΓ'
  have hy' : env.HasType univs Γ' (y.subst τ) (.const family []) :=
    hy.subst henv.orderedStrong WT hΓ'
  have Ex := proofErase_subst_with hΓ' WT hx ES
  have Ey := proofErase_subst_with hΓ' WT hy ES
  obtain ⟨x', HX, EX⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ' hx' EΓ' Ex (RA.scoped (fun R => .base R))
  obtain ⟨y', HY, EY⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ' hy' EΓ' Ey (RB.scoped (fun R => .base R))
  have HG := H.future W (C' := .const family []) .refl RA RB
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
    fun hΓ hΓ' V ht R => erased_static_structure_eta_expansion_stage_descent heq hs n
      hΓ hΓ' V ht (pi_inert_stage_embed R)
  have hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute (PiInertStage D n) Δ a b :=
    fun R => .base (pi_inert_stage_core (.inl (.inl (.inl R))))
  have HF := proofErase_computed_dependent_pair_fields hd hprim hi hp hf hz hadm hshape
    hΓ' HX.hasType.2 HY.hasType.2 (by simpa only [EΓ', EX, EY] using HG)
  simpa only [EΓ', EX, EY] using HF

end Lean4Lean.VEnv.Strengthening
