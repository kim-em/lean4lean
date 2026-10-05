import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalCodeSite
import Lean4Lean.Theory.Typing.AnchoredOriginalConstantCoherence

/-! A constant query at an actual closed canonical site. Its named charge
belongs to the enclosing canonical owner, which need not be this constant.
The caller keeps its own original constant endpoint. Shared declaration lookup
and the actual primitive universe seeds align assigned types without an
original comparison between the canonical site and the caller. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

structure CanonicalConstSitePacket (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (strata : EquationStratification env)
    (name : Name) (levels : List VLevel) (profile : Profile n) where
  ownerName : Name
  owner : CanonicalCodeOwner env registry strata ownerName
  info : VConstant
  lookup : owner.selected.origin.source.constants name = some info
  assignedLevels : List VLevel
  assignedWF : ∀ level ∈ assignedLevels, level.WF U
  levelsWF : ∀ level ∈ levels, level.WF U
  equivalent : List.Forall₂ (· ≈ ·) assignedLevels levels
  typeClosed : info.type.Closed
  site : EndpointRef owner.selected.origin.source U [] (.const name levels)
    (info.type.instL assignedLevels)
  realization : Subst
  footprint : Footprint
  query : RichObs owner.selected.origin.source env U registry target (.ref site)
    [] realization profile footprint
  resources : footprint.Available (fun _ => [])

namespace CanonicalConstSitePacket
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {strata : EquationStratification env} {name : Name} {levels : List VLevel} {profile : Profile n}

noncomputable def chargeDepth
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile) : Nat → Nat :=
  headDepth packet.owner.selected.ordinal
    (fun control => packet.query.stratifiedDepth (strata.headOrdinal registry) control)

noncomputable def siteSchedule
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile) : Nat :=
  richSchedule .fundamental
    (Closure.close ((EndpointState.ref packet.site).dependencyOrigin packet.owner.selected.origin.ordered) []).cost

noncomputable def returnRaw
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (answer : RichComputationalValue packet.owner.selected.origin.source env U registry target
      (.ref packet.site) [] packet.realization packet.realization (fun _ => []) profile) :
    CanonicalConstSitePacket env U registry target strata name levels answer.rightQuery.raw :=
  { packet with footprint := answer.rightQuery.footprint
                query := answer.rightQuery.observation
                resources := answer.rightQuery.resources }

theorem returnRaw_depth
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (answer : RichComputationalValue packet.owner.selected.origin.source env U registry target
      (.ref packet.site) [] packet.realization packet.realization (fun _ => []) profile) :
    (packet.returnRaw answer).chargeDepth = headDepth packet.owner.selected.ordinal
      (fun control => answer.rightQuery.observation.stratifiedDepth (strata.headOrdinal registry) control) := rfl

/-- This is only metadata inversion at the actual primitive constDF. The
two environments agree on the declared constant through their common target. -/
theorem primitiveAssigned
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (below : sourceEnv ≤ env)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expressionEq : expression = .const name levels) (primitive : reference.Primitive) :
    ∃ callerLevels : List VLevel,
      (∀ level ∈ callerLevels, level.WF U) ∧
      List.Forall₂ (· ≈ ·) packet.assignedLevels callerLevels ∧
      assigned = packet.info.type.instL callerLevels := by
  have registered : env.constants name = some packet.info :=
    packet.owner.selected.origin.sourceBelow.constants packet.lookup
  cases reference with
  | left original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl otherWF levelWF lookup wf count equiv closed ambient =>
      have same := Option.some.inj (registered.symm.trans (below.constants lookup))
      cases same
      exact ⟨_, wf, packet.equivalent, rfl⟩
  | right original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl wf count levelWF lookup otherWF equiv closed ambient =>
      have same := Option.some.inj (registered.symm.trans (below.constants lookup))
      cases same
      have reverse := Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm)
        (Lean4Lean.List.Forall₂.flip equiv)
      exact ⟨_, wf, Lean4Lean.List.Forall₂.trans (T := (· ≈ ·))
        (fun _ _ _ first second => first.trans second) packet.equivalent reverse, rfl⟩

noncomputable def returnType
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (answer : RichSupportedValue packet.owner.selected.origin.source env U registry target
      (.ref packet.site) [] packet.realization packet.realization (fun _ => []) profile)
    (callerWF : ∀ level ∈ callerLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) packet.assignedLevels callerLevels) :
    CanonicalCodeSitePacket env U registry target strata (packet.info.type.instL callerLevels) true answer.support where
  name := packet.ownerName
  owner := packet.owner
  canonicalExpression := packet.info.type.instL packet.assignedLevels
  level := (EndpointState.ref packet.site).typeFormation.level
  node := (EndpointState.ref packet.site).typeFormation.node
  canonicalClosed := packet.typeClosed.instL
  expressionEq := EqUpToLevels.instL_expr packet.info.type packet.assignedWF callerWF equivalent
  realization := packet.realization
  footprint := answer.footprint
  certificate := answer.certificate
  resources := answer.resources

theorem returnType_related
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (henv : env.Ordered)
    (answer : RichSupportedValue packet.owner.selected.origin.source env U registry target
      (.ref packet.site) [] packet.realization packet.realization (fun _ => []) profile)
    (callerWF : ∀ level ∈ callerLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) packet.assignedLevels callerLevels) (σ : Subst) :
    TypeRelated env U registry target ((packet.info.type.instL callerLevels).subst σ)
      ((packet.info.type.instL callerLevels).subst σ) answer.support := by
  have code : TypeRelated env U registry target
      (packet.info.type.instL packet.assignedLevels) (packet.info.type.instL packet.assignedLevels)
      answer.support := by
    simpa only [packet.typeClosed.instL.subst_eq (σ := packet.realization) .zero] using answer.typeCode
  have comparison := EqUpToLevels.instL_expr packet.info.type packet.assignedWF callerWF equivalent
  simpa only [packet.typeClosed.instL.subst_eq (σ := σ) .zero] using code.levels henv comparison comparison

theorem returnRelated
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (henv : env.Ordered)
    (answer : RichSupportedValue packet.owner.selected.origin.source env U registry target
      (.ref packet.site) [] packet.realization packet.realization (fun _ => []) profile)
    (callerWF : ∀ level ∈ callerLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) packet.assignedLevels callerLevels) (σ τ : Subst) :
    Related env U registry target ((VExpr.const name levels).subst σ) ((VExpr.const name levels).subst τ)
      ((packet.info.type.instL callerLevels).subst σ) profile answer.support := by
  have code : TypeRelated env U registry target
      (packet.info.type.instL packet.assignedLevels) (packet.info.type.instL packet.assignedLevels)
      answer.support := by
    simpa only [packet.typeClosed.instL.subst_eq (σ := packet.realization) .zero] using answer.typeCode
  have self : List.Forall₂ (· ≈ ·) packet.assignedLevels packet.assignedLevels := by
    induction packet.assignedLevels with
    | nil => exact .nil
    | cons level rest ih => exact .cons rfl ih
  have first := EqUpToLevels.instL_expr packet.info.type packet.assignedWF packet.assignedWF self
  have second := EqUpToLevels.instL_expr packet.info.type packet.assignedWF callerWF equivalent
  have original : Related env U registry target (.const name levels) (.const name levels)
      (packet.info.type.instL packet.assignedLevels) profile answer.support := by
    simpa only [subst, packet.typeClosed.instL.subst_eq (σ := packet.realization) .zero] using answer.related
  simpa only [subst, packet.typeClosed.instL.subst_eq (σ := σ) .zero] using
    original.convert henv answer.typed (code.levels henv first second)

end CanonicalConstSitePacket

structure CanonicalConstSiteAt (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (strata : EquationStratification env)
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst) (profile : Profile n) where
  packet : CanonicalConstSitePacket env U registry target strata name levels profile

structure CanonicalConstSiteReturnResult
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ τ : Subst)
    (answer : RichComputationalValue packet.owner.selected.origin.source env U registry target
      (.ref packet.site) [] packet.realization packet.realization (fun _ => []) profile) where
  typeQuery : CanonicalCodeSiteAt sourceEnv env U registry target strata caller.typeFormation.node
    locals σ true answer.support
  typeCode : TypeRelated env U registry target (assigned.subst σ) (assigned.subst σ) answer.support
  typed : profile.HasType answer.support
  related : Related env U registry target ((VExpr.const name levels).subst σ) ((VExpr.const name levels).subst τ)
    (assigned.subst σ) profile answer.support
  rightQuery : CanonicalConstSiteAt sourceEnv env U registry target strata caller locals τ answer.rightQuery.raw
  adapter : GeneralNormalProfileAdapter env U registry target answer.rightQuery.raw
    (raiseProfile answer.rightQuery.rank answer.rightQuery.bound profile)

noncomputable def CanonicalConstSitePacket.assembleReturn
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (henv : env.Ordered)
    (callerWF : ∀ level ∈ callerLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) packet.assignedLevels callerLevels)
    (caller : EndpointState sourceEnv U source (.const name levels) (packet.info.type.instL callerLevels))
    (locals : List Nat) (σ τ : Subst)
    (answer : RichComputationalValue packet.owner.selected.origin.source env U registry target
      (.ref packet.site) [] packet.realization packet.realization (fun _ => []) profile) :
    CanonicalConstSiteReturnResult packet caller locals σ τ answer where
  typeQuery := ⟨packet.returnType answer.toRichSupportedValue callerWF equivalent⟩
  typeCode := packet.returnType_related henv answer.toRichSupportedValue callerWF equivalent σ
  typed := answer.typed
  related := packet.returnRelated henv answer.toRichSupportedValue callerWF equivalent σ τ
  rightQuery := ⟨packet.returnRaw answer⟩
  adapter := answer.rightQuery.adapter

end Lean4Lean.AnchoredSource.Adapted
