import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstStep
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstOrigin

/-! The closed constant carrier's assigned return is already shared syntax.
The same actual lower answer supplies its root certificate and semantic code;
no caller-local resources or cross-source comparison are introduced. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CanonicalConstSitePacket

/-- Extract exactly the query-independent payload used by the shared leaf. -/
noncomputable def origin
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile) :
    CanonicalConstOrigin env U registry strata name levels where
  ownerName := packet.ownerName
  owner := packet.owner
  info := packet.info
  lookup := packet.lookup
  assignedLevels := packet.assignedLevels
  assignedWF := packet.assignedWF
  levelsWF := packet.levelsWF
  equivalent := packet.equivalent
  typeClosed := packet.typeClosed
  site := packet.site

/-- The prospective shared constructor feeds the existing checked interpreter
without changing its original, query, or nil resource proof. -/
noncomputable def ofOrigin {footprint : Footprint}
    (origin : CanonicalConstOrigin env U registry strata name levels)
    (realization : Subst)
    (query : RichObs origin.owner.selected.origin.source env U registry target
      (.ref origin.site) [] realization profile footprint)
    (resources : footprint.Available (fun _ => [])) :
    CanonicalConstSitePacket env U registry target strata name levels profile where
  ownerName := origin.ownerName
  owner := origin.owner
  info := origin.info
  lookup := origin.lookup
  assignedLevels := origin.assignedLevels
  assignedWF := origin.assignedWF
  levelsWF := origin.levelsWF
  equivalent := origin.equivalent
  typeClosed := origin.typeClosed
  site := origin.site
  realization := realization
  footprint := footprint
  query := query
  resources := resources


/-- The actual shared function-side observation. Its recursive original is
closed, while the caller retains its own original constant node. -/
noncomputable def observation
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst) :
    RichObs sourceEnv env U registry target caller locals σ profile [] :=
  .canonicalConst packet.origin packet.realization packet.query packet.resources

@[simp] theorem observation_headDepth
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst) (policy : Name → Nat → Nat) :
    (packet.observation caller locals σ).headDepth policy =
      policy packet.ownerName (packet.query.headDepth policy) := by
  simp only [observation, RichObs.headDepth, origin]

/-- Primitive constant dispatch returns an actual shared assigned certificate,
with the enclosing canonical owner's mask. The observation carrier remains the
exact returned closed packet, ready for the shared constant-leaf constructor. -/
theorem primitiveSharedReturn
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (reference : EndpointRef sourceEnv U source (.const name levels) assigned)
    (primitive : reference.Primitive)
    (locals : List Nat) (σ τ : Subst)
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length)
    (fuel : Nat → Nat) (constants schedule : Nat)
    (bounded : WithinAbove cutoff fuel packet.chargeDepth)
    (lower : packet.ComputationalBelow
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants schedule)) :
    ∃ answer : RichComputationalValue packet.owner.selected.origin.source env U registry target
        (.ref packet.site) [] packet.realization packet.realization (fun _ => []) profile,
      ∃ result : CanonicalConstSiteReturnResult packet (.ref reference) locals σ τ answer,
      ∃ certificate : RichCert sourceEnv env U registry target
          (EndpointState.ref reference).typeFormation.node locals σ true answer.support [],
        Footprint.Available [] available ∧
        TypeRelated env U registry target (assigned.subst σ) (assigned.subst σ) answer.support ∧
        WithinAbove cutoff fuel (fun control => certificate.stratifiedDepth
          (strata.headOrdinal registry) control) ∧
        WithinAbove cutoff fuel result.rightQuery.packet.chargeDepth := by
  obtain ⟨answer, result, queryBound, typeBound⟩ := packet.primitiveStep henv below reference
    primitive locals σ τ cutoff cutoffBound fuel constants schedule bounded lower
  let code := result.typeQuery.packet
  refine ⟨answer, result, .recipe (.root _ locals σ code.owner code.node code.canonicalClosed
    code.expressionEq code.realization code.certificate code.resources), ?_, result.typeCode, ?_, queryBound⟩
  · intro position need member
    cases member
  · intro control above
    simp only [RichCert.stratifiedDepth, RichCert.headDepth, RichCodeRecipe.headDepth,
      stratifiedHeadPolicy]
    change EquationStratifiedFuel.headDepth (strata.headOrdinal registry code.name)
      (fun _ => code.certificate.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control))
      control ≤ fuel control
    rw [code.owner.headOrdinal_eq]
    simpa only [code, CanonicalCodeSitePacket.chargeDepth, RichCert.stratifiedDepth,
      EquationStratifiedFuel.headDepth] using typeBound control above

/-- Actual primitive F returns both ordinary shared syntax channels from the
one computed smaller canonical call. Neither output is a packet-only witness. -/
theorem primitiveComputational
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (reference : EndpointRef sourceEnv U source (.const name levels) assigned)
    (primitive : reference.Primitive) (locals : List Nat) (σ τ : Subst)
    (available : Valuation)
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length)
    (fuel : Nat → Nat) (constants schedule : Nat)
    (bounded : WithinAbove cutoff fuel packet.chargeDepth)
    (lower : packet.ComputationalBelow
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants schedule)) :
    ∃ output : RichComputationalValue sourceEnv env U registry target
        (.ref reference) locals σ τ available profile,
      WithinAbove cutoff fuel (fun control =>
        output.certificate.stratifiedDepth (strata.headOrdinal registry) control) ∧
      WithinAbove cutoff fuel (fun control =>
        output.rightQuery.observation.stratifiedDepth (strata.headOrdinal registry) control) := by
  obtain ⟨answer, result, certificate, resources, code, codeBound, queryBound⟩ :=
    packet.primitiveSharedReturn (available := available) henv below reference primitive
      locals σ τ cutoff cutoffBound fuel constants schedule bounded lower
  let returned : RichComputationalValue sourceEnv env U registry target
      (.ref reference) locals σ τ available profile := {
    support := answer.support
    footprint := []
    certificate := certificate
    resources := resources
    typed := result.typed
    related := result.related
    typeCode := code
    rightQuery := {
      rank := answer.rightQuery.rank
      bound := answer.rightQuery.bound
      raw := answer.rightQuery.raw
      footprint := []
      observation := result.rightQuery.packet.observation (.ref reference) locals τ
      adapter := result.adapter
      resources := fun _ _ member => nomatch member
      live := answer.rightQuery.live } }
  refine ⟨returned, codeBound, ?_⟩
  intro control above
  simp only [returned, RichObs.stratifiedDepth, observation_headDepth,
    stratifiedHeadPolicy]
  rw [result.rightQuery.packet.owner.headOrdinal_eq]
  simpa only [CanonicalConstSitePacket.chargeDepth, RichObs.stratifiedDepth,
    EquationStratifiedFuel.headDepth] using queryBound control above

end CanonicalConstSitePacket
end Lean4Lean.AnchoredSource.Adapted
