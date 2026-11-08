import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCompetitorReplay
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProjectionSupplyRelay

/-! # The structure-root case of projected-field readout induction

Readout at smaller primitive cost first bypasses the structure expansion,
using its exact projected first field. Typed replay recovers an actual run
of the original pair at that smaller cost. A second use of the induction
hypothesis then reads its incoming field ancestry. All scopes, continuation
predicates and frame counts remain those of the actual execution.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private identity_interpretation
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertHoleContinuation
variable [Params] {D : Definitions}

/-- Projected-field ancestry readout for arbitrary actual pair executions at
a specified total primitive cost. The source pair may be in any temporary
scope, with arbitrary fields. Its continuation may have arbitrarily nested
retained frames. Competitors remain raw and use the same predicate K.

The intended induction is below a least failed projection budget, with an
exposed final output. Establishing it throughout that range is still open: the function-root and
arbitrary frame-progress cases need a compatible induction. This definition
is an induction target, not an assertion of its truth or global sufficiency. -/
def PiInertPairAncestryReadout (D : Definitions) (Ω : List ProofShape)
    (family : Name) (info : VProjectionInfo) (out : ProofShape) (cost : Nat) : Prop :=
  ∀ {Δ field value stage cb endpoint K ck frames},
    TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]) →
    ScopedComputeCount (PiInertStage D stage) cb Δ
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) endpoint →
    PiInertProjectionRunFrames D Ω family 0 out Δ K endpoint ck frames →
    cb+ck = cost →
    ∀ {source u lower fieldStage fieldCost},
      ControlTyping Δ (.proj family 0 source) (.sort u) →
      AdministrativeHeadDeletion field lower →
      ScopedComputeCount (PiInertStage D fieldStage) fieldCost Δ (.proj family 0 source) lower →
      ∃ later j major k, j+k ≤ fieldCost+cost ∧
        ScopedComputeCount (PiInertStage D later) j Δ source major ∧ K major k

/-- At the final observer's own scope, the least failed projection budget
supplies ancestry readout for an arbitrary actual source computation and
continuation. A temporary identity frame absorbs the source computation;
after the existing observer relay, that raw frame is composed back into the
returned source path. No smaller-cost readout hypothesis is needed here. -/
theorem pi_inert_observer_ancestry_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0)
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (HT : TypedSource Ω (ProofShape.mkApps (.const info.ctorName []) [field, value]))
    (R : ScopedComputeCount (PiInertStage D stage) cb Ω
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) endpoint)
    (HK : PiInertProjectionRunFrames D Ω family 0 out Ω K endpoint ck frames)
    (hbudget : cb+ck < budget)
    (HSort : ControlTyping Ω (.proj family 0 source) (.sort u))
    (HD : AdministrativeHeadDeletion field lower)
    (RF : ScopedComputeCount (PiInertStage D fieldStage) fieldCost Ω (.proj family 0 source) lower) :
    ∃ later j major k, j+k ≤ fieldCost+cb+ck ∧
      ScopedComputeCount (PiInertStage D later) j Ω source major ∧ K major k := by
  have HApp : PiInertProjectionRunFrames D Ω family 0 out Ω
      (PiInertApplicationContinuation D Ω ProofShape.Subst.id [] K)
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) (cb+ck) (frames+1) := by
    apply PiInertProjectionRunFrames.application (n := stage) HT (.identity identity_interpretation) _ _ HK
    · simpa only [ProofShape.subst_id, ProofShape.mkApps] using HT
    · simpa only [ProofShape.subst_id, ProofShape.mkApps] using R
  have HC : PiInertPairComponentSupplyRun D Ω family info out Ω
      (PiInertApplicationContinuation D Ω ProofShape.Subst.id [] K) field value (cb+ck) (frames+1) :=
    .observer HApp
  obtain ⟨later, j, major, k, hcost, RJ, next, a, final, b, hsum, RA, HB⟩ :=
    HC.projected_field_competitor HLeast heq hs hi hp hf hz hout hbudget HSort HD RF
  have RA' : ScopedComputeCount (PiInertStage D next) a Ω major final := by
    simpa only [ProofShape.subst_id, ProofShape.mkApps] using RA
  exact ⟨max later next, j+a, final, b, by omega,
    (RJ.mono (pi_inert_stage_mono (Nat.le_max_left later next))).trans
      (RA'.mono (pi_inert_stage_mono (Nat.le_max_right later next))), HB⟩

/-- A native structure root is bypassed at its original source, at no greater
cost than its target suffix. This uses ONLY readout at the strictly smaller
target cost, starting from the reflexive projected-field ancestry supplied by
the actual native expansion. The returned execution is typed, has the exact
original continuation and frame count, and omits the root's unit charge. -/
theorem pi_inert_structure_smaller_execution
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]))
    (HE : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D guardStage) Δ
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) target)
    (HR : PiInertStage D stage Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]) target)
    (RT : ScopedComputeCount (PiInertStage D stage) ct Δ target endpoint)
    (HK : PiInertProjectionRunFrames D Ω family 0 out Δ K endpoint ck frames)
    (IH : PiInertPairAncestryReadout D Ω family info out (ct+ck)) :
    ∃ later j major k, j+k ≤ ct+ck ∧
      ScopedComputeCount (PiInertStage D later) j Δ
        (ProofShape.mkApps (.const info.ctorName []) [field, value]) major ∧
      PiInertProjectionRunFrames D Ω family 0 out Δ K major k frames := by
  obtain ⟨Γ, m, hΓ, EΓ, hm, Em⟩ :=
    TypedSource.closed_constructor_realize hi hp hz (by simp [hf]) HT
  have HNative : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D guardStage)
      (proofEraseCtx Γ) (proofErase Γ m) target := by simpa only [EΓ, Em] using HE
  obtain ⟨HSort, HTtarget, nextValue, ET⟩ := proofErase_native_pair_structure_field D
    (erased_static_structure_eta_expansion_stage_descent heq hs guardStage)
    hi hp hf hz hadm hshape hΓ hm HNative
  simp only [EΓ, Em] at HSort HTtarget ET
  rw [ET] at HTtarget RT
  have RF : ScopedComputeCount (PiInertStage D stage) 0 Δ
      (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value]))
      (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value])) :=
    .beta .refl
  obtain ⟨later, j, major, k, hcost, RJ, RK⟩ := IH HTtarget RT HK rfl HSort .refl RF
  have RAll := (ScopedComputeCount.base HR).trans (ET ▸ RT)
  exact ⟨later, j, major, k, by omega, RJ, HK.replay_from_source heq hs HT RAll RJ RK⟩

/-- The structure-root case closes under strong induction on primitive cost,
even with arbitrary fields in an arbitrary temporary scope. The first smaller
call bypasses the root; replay gives actual typing, and the second smaller
call transports the ORIGINAL incoming projected-field ancestry. No field is
assumed to descend independently to the final observer. -/
theorem pi_inert_structure_ancestry_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (IH : ∀ smaller, smaller < bound → PiInertPairAncestryReadout D Ω family info out smaller)
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]))
    (HE : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D guardStage) Δ
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) target)
    (HR : PiInertStage D stage Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]) target)
    (RT : ScopedComputeCount (PiInertStage D stage) ct Δ target endpoint)
    (HK : PiInertProjectionRunFrames D Ω family 0 out Δ K endpoint ck frames)
    (hbound : ct+ck < bound)
    (HSort : ControlTyping Δ (.proj family 0 source) (.sort u))
    (HD : AdministrativeHeadDeletion field lower)
    (RF : ScopedComputeCount (PiInertStage D fieldStage) fieldCost Δ (.proj family 0 source) lower) :
    ∃ later j major k, j+k ≤ fieldCost+ct+ck ∧
      ScopedComputeCount (PiInertStage D later) j Δ source major ∧ K major k := by
  obtain ⟨later, j, major, k, hcost, RJ, HJ⟩ := pi_inert_structure_smaller_execution
    heq hs hi hp hf hz hadm hshape HT HE HR RT HK (IH (ct+ck) hbound)
  obtain ⟨last, a, final, b, hlast, RA, HB⟩ :=
    IH (j+k) (by omega) HT RJ HJ rfl HSort HD RF
  exact ⟨last, a, final, b, by omega, RA, HB⟩

/-- Component computation before the structure root also preserves the
incoming ancestry and its count. The smaller-cost induction bypasses the
root after that prefix, saving its unit charge in the final bound. This is
the structure case of an arbitrary constructor-spine cut, with no restriction
on the actual target suffix or continuation frames. -/
theorem pi_inert_components_structure_ancestry_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (IH : ∀ smaller, smaller < bound → PiInertPairAncestryReadout D Ω family info out smaller)
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]))
    (RA : ScopedArgumentsCount (PiInertStage D stage) Δ ca [field, value] [nextField, nextValue])
    (HE : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D guardStage) Δ
      (ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue]) target)
    (HR : PiInertStage D stage Δ (ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue]) target)
    (RT : ScopedComputeCount (PiInertStage D stage) ct Δ target endpoint)
    (HK : PiInertProjectionRunFrames D Ω family 0 out Δ K endpoint ck frames)
    (hbound : ca+1+ct+ck ≤ bound)
    (HSort : ControlTyping Δ (.proj family 0 source) (.sort u))
    (HD : AdministrativeHeadDeletion field lower)
    (RF : ScopedComputeCount (PiInertStage D fieldStage) fieldCost Δ (.proj family 0 source) lower) :
    ∃ later j major k, j+k ≤ fieldCost+ca+ct+ck ∧
      ScopedComputeCount (PiInertStage D later) j Δ source major ∧ K major k := by
  have RPair : ScopedComputeCount (PiInertStage D stage) ca Δ
      (ProofShape.mkApps (.const info.ctorName []) [field, value])
      (ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue]) := by
    simpa only [Nat.zero_add] using
      (ScopedComputeCount.beta (Step := PiInertStage D stage) (Δ := Δ)
        (BetaRed.refl (e := .const info.ctorName []))).mkApps RA
  have HTnext := HT.pi_inert_compute heq hs RPair.forget
  have HTfield : TypedSource Δ field :=
    (ScopedHole.appFn (.appArg (.const info.ctorName []) .hole) value).typed HT
  cases RA with
  | cons RField rest =>
    cases rest with
    | cons RValue last =>
      cases last
      obtain ⟨nextLower, cNext, hcNext, RNext, HDNext⟩ := HD.compute heq hs HTfield RField
      have RAncestry := (RF.mono (pi_inert_stage_mono (Nat.le_max_left fieldStage stage))).trans
        (RNext.mono (pi_inert_stage_mono (Nat.le_max_right fieldStage stage)))
      obtain ⟨later, j, major, k, hcost, RJ, RK⟩ := pi_inert_structure_ancestry_readout
        heq hs hi hp hf hz hadm hshape IH HTnext HE HR RT HK (by omega) HSort HDNext RAncestry
      exact ⟨later, j, major, k, by omega, RJ, RK⟩

/-- A selected structure root cannot occur in an unrestricted minimum once
projected-field readout is available at its strictly smaller target cost.
An arbitrary actual prefix is retained, so this applies at a root discovered
inside a larger constructor path as well as at the original source. -/
theorem pi_inert_minimum_no_structure_of_ancestry_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (HT : TypedSource Δ original)
    (RP : ScopedComputeCount (PiInertStage D stage) cp Δ original
      (ProofShape.mkApps (.const info.ctorName []) [field, value]))
    (HE : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D guardStage) Δ
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) target)
    (HR : PiInertStage D stage Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]) target)
    (RT : ScopedComputeCount (PiInertStage D stage) ct Δ target endpoint)
    (HK : PiInertProjectionRunFrames D Ω family 0 out Δ K endpoint ck frames)
    (IH : PiInertPairAncestryReadout D Ω family info out (ct+ck))
    (hcost : cp+1+ct+ck ≤ cost)
    (HM : ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j Δ original endpoint' →
      K endpoint' k → cost ≤ j+k) : False := by
  obtain ⟨later, j, major, k, hsmall, RJ, HJ⟩ := pi_inert_structure_smaller_execution
    heq hs hi hp hf hz hadm hshape (HT.pi_inert_compute heq hs RP.forget) HE HR RT HK IH
  have RAlt := (RP.mono (pi_inert_stage_mono (Nat.le_max_left stage later))).trans
    (RJ.mono (pi_inert_stage_mono (Nat.le_max_right stage later)))
  have HB := HM _ _ major k RAlt HJ.forget.holds
  omega

/-- The actual activated structure boundary left by function-eta elimination
is excluded by smaller-cost ancestry readout. There is no restriction to
component-supply continuations, to the observer's scope, or to one retained
terminal; the selected arbitrary continuation is used directly. -/
theorem PiInertActivatedPairStructureMinimum.not_of_ancestry_readout
    (H : PiInertActivatedPairStructureMinimum D Ω family info out field controls value cost frames application)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (IH : ∀ smaller, smaller < cost → PiInertPairAncestryReadout D Ω family info out smaller) : False := by
  obtain ⟨stage, pre, pending, target, endpoint, ct, ck, K, EArgs, HT, HR,
    ⟨EP, guardStage, _, HE⟩, RT, HK, hc, HM, _⟩ := H
  subst pending
  simp only [List.append_nil] at EArgs
  subst pre
  exact pi_inert_minimum_no_structure_of_ancestry_readout heq hs hi hp hf hz hadm hshape
    HT (ScopedComputeCount.beta (Step := PiInertStage D stage) .refl) HE HR RT HK
    (IH (ct+ck) (by omega)) (by omega) HM

/-- The marked fresh-field structure boundary is excluded by the same
smaller-cost hypothesis. Only the mark is forgotten; its actual execution,
context, raw continuation and unrestricted minimum supply the contradiction. -/
theorem PiInertFreshPairStructureMinimum.not_of_ancestry_readout
    (H : PiInertFreshPairStructureMinimum D Ω Δ family info out A x controls value cost frames)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (IH : ∀ smaller, smaller < cost → PiInertPairAncestryReadout D Ω family info out smaller) : False := by
  obtain ⟨stage, guardStage, target, endpoint, ct, ck, K, _, HT, HR, HE, RT, HK, hc, HM⟩ := H
  exact pi_inert_minimum_no_structure_of_ancestry_readout heq hs hi hp hf hz hadm hshape
    HT (ScopedComputeCount.beta (Step := PiInertStage D stage) .refl) HE HR RT HK.forget
    (IH (ct+ck) (by omega)) (by omega) HM

end Lean4Lean.VEnv.Strengthening
