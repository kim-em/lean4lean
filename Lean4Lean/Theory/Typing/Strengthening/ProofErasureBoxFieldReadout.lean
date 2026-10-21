import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureBox
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointProjection

/-! # Reading the field certificate of a typed Box guard

The whole guard may use common checking, carrier checking, symmetry, carrier
computation or endpoint computation. Typed projection support and exact Box
recipes recover the field guard without a global carrier-conversion law.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private BoxCarrierAlignment.projection_recipe BoxCarrierAlignment.family_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBoxAlignment
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- The registered Box constructor determines its actual projection type.
Typed structure expansion supplies projection well-formedness and the exact
universe-argument count; field selection then returns the parameter itself. -/
theorem box_projection_typed
    (hi : env.projections family info) (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.app (.const family []) A)) :
    env.HasType univs Γ (.proj family 0 x) A := by
  have hexp := (StructureReplay.expansion_typed_iff henv hΓ hi
    (show [A].length = info.nparams by simp [hp]) hz hx).2 (.inl hadm)
  obtain ⟨F, hproj⟩ := structure_expansion_projection_typed hΓ hexp (by omega : 0 < info.numFields)
  obtain ⟨ci, Hci, _, hls⟩ := (VExpr.WF.of_mkApps henv hΓ ⟨_, hexp⟩).const_inv henv hΓ
  rw [henv.ordered.projectionConstructor hi] at Hci
  cases Option.some.inj Hci
  have hu : info.uvars = 0 := hls.symm
  apply projection_at_recovered_family (ls := []) (args := [A]) henv hΓ hi ⟨_, hproj⟩ hx
  simp [VProjectionInfo.fieldType, hp, hu, hshape,
    VProjectionInfo.instantiateProjectionParameters, VProjectionInfo.instantiateProjectionFields,
    VExpr.inst, VExpr.instVar_zero]

private theorem box_field_raw
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (hinert : ∀ {Δ args out}, ¬ Step Δ (ProofShape.mkApps (.const family []) args) out)
    (hi : env.projections family info) (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (H : JointCheck Step Δ kind a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort (.succ .zero)))
    (hx : env.HasType univs Γ x (.app (.const family []) A))
    (hy : env.HasType univs Γ y (.app (.const family []) A))
    (hpx : env.HasType univs Γ (.proj family 0 x) A)
    (hpy : env.HasType univs Γ (.proj family 0 y) A)
    (EΓ : proofEraseCtx Γ = Δ) (Ex : proofErase Γ x = a) (Ey : proofErase Γ y = b)
    (E : JointCheckKind.carrier (.app (.const family []) (proofErase Γ A)) = kind) :
    JointCarrierGuard Step Δ (proofErase Γ A) (.proj family 0 a) (.proj family 0 b) := by
  induction H generalizing Γ A x y with
  | carrierChecked H =>
    cases E
    have HC := proofErase_joint_project_typed hstep hprim hΓ hx hy hpx hpy
      (by simpa only [EΓ, Ex, Ey] using H)
    have Epx : proofErase Γ (.proj family 0 x) = .proj family 0 (proofErase Γ x) :=
      if_neg (not_proof_at_positive_type hΓ hA hpx)
    have Epy : proofErase Γ (.proj family 0 y) = .proj family 0 (proofErase Γ y) :=
      if_neg (not_proof_at_positive_type hΓ hA hpy)
    exact .carrierChecked (by simpa only [EΓ, Epx, Epy, Ex, Ey] using HC)
  | carrierFunction => cases E
  | carrierSubsingleton HS =>
    cases E
    have Hzero := SubsingletonCarrier.record_numFields (ps := [proofErase Γ A]) hi HS
    omega
  | carrierSymm H ih => exact .carrierSymm (ih hΓ hA hy hx hpy hpx EΓ Ey Ex E)
  | carrierReduce RA RB H ih =>
    obtain ⟨x', HX, EX⟩ := proofErase_scoped_compute_realize hstep hΓ hx EΓ Ex RA
    obtain ⟨y', HY, EY⟩ := proofErase_scoped_compute_realize hstep hΓ hy EΓ Ey RB
    have HPX := SimAt.proj henv.orderedStrong hΓ (fun _ ht => HX.toU.of_l henv hΓ ht) A hpx
    have HPY := SimAt.proj henv.orderedStrong hΓ (fun _ ht => HY.toU.of_l henv hΓ ht) A hpy
    exact .carrierReduce (.proj RA) (.proj RB)
      (ih hΓ hA HX.hasType.2 HY.hasType.2 HPX.hasType.2 HPY.hasType.2 EΓ EX EY E)
  | carrierCompute R H ih =>
    cases E
    have RR : ScopedCompute Step _ (ProofShape.mkApps (.const family []) [proofErase Γ A]) _ := R
    obtain ⟨ps', Eout, RP⟩ := RR.const_spine hinert
    cases RP with
    | cons RA RT =>
      cases RT
      obtain ⟨A', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ rfl RA
      have HBox := IsDefEq.appDF (BoxCarrierAlignment.family_typed (Γ := Γ) hc) HA
      exact .carrierCompute RA (by
        rw [← EA]
        exact ih hΓ HA.hasType.2 (HBox.defeq hx) (HBox.defeq hy) (HA.defeq hpx) (HA.defeq hpy)
          EΓ Ex Ey (by rw [EA, Eout]; rfl))
  | carrierIntro hi' hz hlen hadm HF =>
    obtain ⟨rfl, rfl, rfl⟩ := ProofShape.const_spine_inj
      (show ProofShape.mkApps (.const family []) [proofErase Γ A] = _ from JointCheckKind.carrier.inj E)
    cases henv.ordered.projections_unique hi hi'
    have hexp := (StructureReplay.expansion_typed_iff henv hΓ hi
      (show [A].length = info.nparams by simp [hp]) hz hx).2 hadm
    have hn : ¬ StructureReplay.ProofField env univs info [] 0 := fun H =>
      not_proof_at_positive_type hΓ hA hpx (H.projection hΓ hi (by simp [hp]) hexp)
    exact .carrierChecked (HF 0 (by omega) hn)
  | carrierNested hi' hz hlen hadm PT HF =>
    obtain ⟨rfl, rfl, rfl⟩ := ProofShape.const_spine_inj
      (show ProofShape.mkApps (.const family []) [proofErase Γ A] = _ from JointCheckKind.carrier.inj E)
    cases henv.ordered.projections_unique hi hi'
    have hexp := (StructureReplay.expansion_typed_iff henv hΓ hi
      (show [A].length = info.nparams by simp [hp]) hz hx).2 hadm
    have hn : ¬ StructureReplay.ProofField env univs info [] 0 := fun H =>
      not_proof_at_positive_type hΓ hA hpx (H.projection hΓ hi (by simp [hp]) hexp)
    have HG := HF 0 (by omega) hn
    rw [BoxCarrierAlignment.projection_recipe hp hf hshape PT] at HG
    exact HG
  | leaf | app | appCarrier | proj | lam | forallE | lamSorted | forallSorted | lamCommon |
      etaBodyL | etaBodyR | structFields | etaLams | compute | symm => cases E

/-- Every Box guard on actual typed majors yields its field carrier guard,
including guards built by common checking and arbitrary computation prefixes.
The supplied projection typings identify the field with the actual parameter;
no normalization or common field comparison is required. -/
theorem proofErase_box_field_guard
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (hinert : ∀ {Δ args out}, ¬ Step Δ (ProofShape.mkApps (.const family []) args) out)
    (hi : env.projections family info) (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort (.succ .zero)))
    (hx : env.HasType univs Γ x (.app (.const family []) A))
    (hy : env.HasType univs Γ y (.app (.const family []) A))
    (hpx : env.HasType univs Γ (.proj family 0 x) A)
    (hpy : env.HasType univs Γ (.proj family 0 y) A)
    (H : JointCarrierGuard Step (proofEraseCtx Γ) (.app (.const family []) (proofErase Γ A))
      (proofErase Γ x) (proofErase Γ y)) :
    JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A)
      (.proj family 0 (proofErase Γ x)) (.proj family 0 (proofErase Γ y)) :=
  box_field_raw hstep hprim hinert hi hp hf hshape hc H hΓ hA hx hy hpx hpy rfl rfl rfl rfl

end Lean4Lean.VEnv.Strengthening
