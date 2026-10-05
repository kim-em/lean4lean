import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalCodeOwner
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaDomain
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalNativeOpening
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeHeadDepth
import Lean4Lean.Theory.Typing.ProjectionLevelCongruence

/-! A closed canonical code site need not be the defining value's declared
type. It retains an actual formation node in the named owner's selected
pre-equation source. Its charge opens that exact node and a returned code
certificate can be attached to an independent caller formation without an
original-proof comparison. This is an isolated packet, not shared grammar. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace CanonicalCodeOwner

def ofNative (opening : CanonicalNativeOpening env registry strata name) :
    CanonicalCodeOwner env registry strata name :=
  ⟨opening.program.equation, opening.registered.singletonEquation opening.singleton, by
    simp only [EquationStratification.headEquation, opening.notDefinition,
      opening.lookup, Option.bind_some, opening.singleton]⟩

end CanonicalCodeOwner

structure CanonicalCodeSitePacket (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (strata : EquationStratification env)
    (expression : VExpr) (relevant : Bool) (profile : Profile n) where
  name : Name
  owner : CanonicalCodeOwner env registry strata name
  canonicalExpression : VExpr
  level : VLevel
  node : EndpointState owner.selected.origin.source U [] canonicalExpression (.sort level)
  canonicalClosed : canonicalExpression.Closed
  expressionEq : EqUpToLevels U canonicalExpression expression
  realization : Subst
  footprint : Footprint
  certificate : RichCert owner.selected.origin.source env U registry target node
    [] realization relevant profile footprint
  resources : footprint.Available (fun _ => [])

namespace CanonicalCodeSitePacket
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {strata : EquationStratification env} {expression : VExpr} {relevant : Bool} {profile : Profile n}

theorem closed (packet : CanonicalCodeSitePacket env U registry target strata expression relevant profile) :
    expression.Closed := packet.expressionEq.closedN_iff.mp packet.canonicalClosed

theorem formed (packet : CanonicalCodeSitePacket env U registry target strata expression relevant profile) :
    profile.HasType (.sort relevant) := packet.certificate.formed

noncomputable def chargeDepth
    (packet : CanonicalCodeSitePacket env U registry target strata expression relevant profile) : Nat → Nat :=
  headDepth packet.owner.selected.ordinal
    (fun control => packet.certificate.stratifiedDepth (strata.headOrdinal registry) control)

noncomputable def codeSchedule
    (packet : CanonicalCodeSitePacket env U registry target strata expression relevant profile) : Nat :=
  richSchedule .fundamental
    (Closure.close (packet.node.dependencyOrigin packet.owner.selected.origin.ordered) []).cost

theorem related
    (packet : CanonicalCodeSitePacket env U registry target strata expression relevant profile)
    (henv : env.Ordered)
    (child : TypeRelated env U registry target
      (packet.canonicalExpression.subst packet.realization)
      (packet.canonicalExpression.subst packet.realization) profile)
    (σ τ : Subst) :
    TypeRelated env U registry target (expression.subst σ) (expression.subst τ) profile := by
  have base : TypeRelated env U registry target packet.canonicalExpression packet.canonicalExpression profile := by
    simpa only [packet.canonicalClosed.subst_eq (σ := packet.realization) .zero] using child
  simpa only [packet.closed.subst_eq (σ := σ) .zero, packet.closed.subst_eq (σ := τ) .zero] using
    base.levels henv packet.expressionEq packet.expressionEq

/-- Conditional induction only at the exact stored original node, with
its computed empty-frame cost and exact canonical source cutoff. -/
def CodeBelow
    (packet : CanonicalCodeSitePacket env U registry target strata expression relevant profile)
    (parentKey : EquationControlMeasure.Key strata.rules.length) : Prop :=
  ∀ {footprint : Footprint}
    (query : RichObs packet.owner.selected.origin.source env U registry target
      packet.node [] packet.realization profile footprint),
    footprint.Available (fun _ => []) → ∀ fuel : Nat → Nat,
    WithinAbove (packet.owner.selected.ordinal - 1) fuel
      (fun control => query.stratifiedDepth (strata.headOrdinal registry) control) →
    strata.SourceCutoff packet.owner.selected.origin.source (packet.owner.selected.ordinal - 1) →
    EquationControlMeasure.Less
      (EquationControlMeasure.key strata.rules.length (packet.owner.selected.ordinal - 1) fuel
        packet.owner.selected.origin.ordered.constantCount packet.codeSchedule) parentKey →
    ∃ answer : RichComputationalValue packet.owner.selected.origin.source env U registry target
      packet.node [] packet.realization packet.realization (fun _ => []) profile,
      WithinAbove (packet.owner.selected.ordinal - 1) fuel
        (fun control => answer.rightQuery.observation.stratifiedDepth (strata.headOrdinal registry) control)

theorem openingDecrease
    (packet : CanonicalCodeSitePacket env U registry target strata expression relevant profile)
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat) (bounded : WithinAbove cutoff fuel packet.chargeDepth) :
    EquationControlMeasure.Less
      (EquationControlMeasure.key strata.rules.length (packet.owner.selected.ordinal - 1)
        (fun control => packet.certificate.stratifiedDepth (strata.headOrdinal registry) control)
        packet.owner.selected.origin.ordered.constantCount packet.codeSchedule)
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule) :=
  EquationStratifiedFuel.openingDecrease packet.owner.selected.ordinal_pos
    packet.owner.selected.ordinal_le cutoffBound bounded constants callerSchedule
    packet.owner.selected.origin.ordered.constantCount packet.codeSchedule

/-- Rebuild from the actual lower answer's right query. Every output control
is bounded on this same packet, including controls masked by its owner. -/
theorem interpret
    (packet : CanonicalCodeSitePacket env U registry target strata expression relevant profile)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat) (bounded : WithinAbove cutoff fuel packet.chargeDepth)
    (lower : packet.CodeBelow
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule))
    (σ τ : Subst) :
    ∃ output : CanonicalCodeSitePacket env U registry target strata expression relevant profile,
      output.name = packet.name ∧ HEq output.owner packet.owner ∧
      TypeRelated env U registry target (expression.subst σ) (expression.subst τ) profile ∧
      WithinAbove cutoff fuel output.chargeDepth := by
  let children := fun control => packet.certificate.stratifiedDepth (strata.headOrdinal registry) control
  obtain ⟨answer, answerBound⟩ := lower (.code packet.certificate) packet.resources children (by
    intro control _
    simp only [RichObs.stratifiedDepth, RichObs.headDepth]
    exact Nat.le_refl _) packet.owner.sourceCutoff
      (packet.openingDecrease cutoff cutoffBound fuel constants callerSchedule bounded)
  obtain ⟨required, certificate, resources, depth⟩ := answer.rightQuery.code_headDepth henv packet.formed
  let output : CanonicalCodeSitePacket env U registry target strata expression relevant profile :=
    { packet with footprint := required, certificate := certificate, resources := resources }
  refine ⟨output, rfl, HEq.rfl,
    packet.related henv (answer.related.code_of_sortable henv hscoped formed packet.formed) σ τ, ?_⟩
  apply EquationStratifiedFuel.rebuild packet.owner.selected.ordinal_pos bounded
  intro control above
  exact Nat.le_trans (depth (fun name value => headDepth (strata.headOrdinal registry name) (fun _ => value) control))
    (answerBound control above)

end CanonicalCodeSitePacket

/-- The caller retains its own original formation, independently of the
closed canonical node supplying this finite code query. -/
structure CanonicalCodeSiteAt (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (strata : EquationStratification env)
    (node : EndpointState sourceEnv U source expression (.sort level))
    (locals : List Nat) (σ : Subst) (relevant : Bool) (profile : Profile n) where
  packet : CanonicalCodeSitePacket env U registry target strata expression relevant profile

def CanonicalCodeSiteAt.reindex
    {node : EndpointState sourceEnv U source expression (.sort level)}
    (query : CanonicalCodeSiteAt sourceEnv env U registry target strata node locals σ relevant profile)
    (destination : EndpointState destinationEnv U destinationSource expression (.sort destinationLevel))
    (destinationLocals : List Nat) (destinationSubst : Subst) :
    CanonicalCodeSiteAt destinationEnv env U registry target strata destination
      destinationLocals destinationSubst relevant profile := ⟨query.packet⟩

@[simp] theorem CanonicalCodeSiteAt.reindex_chargeDepth
    {node : EndpointState sourceEnv U source expression (.sort level)}
    (query : CanonicalCodeSiteAt sourceEnv env U registry target strata node locals σ relevant profile)
    (destination : EndpointState destinationEnv U destinationSource expression (.sort destinationLevel))
    (destinationLocals : List Nat) (destinationSubst : Subst) :
    (query.reindex destination destinationLocals destinationSubst).packet.chargeDepth = query.packet.chargeDepth := rfl

end Lean4Lean.AnchoredSource.Adapted
