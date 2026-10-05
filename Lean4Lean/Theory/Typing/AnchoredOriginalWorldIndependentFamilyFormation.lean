import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFundedFamilyRebuild
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyFormationQuery

/-! The paired enriched header returns through its retained canonical
carrier, applies to the SAME packed caller argument, and restores the
actual major's formation. Header and caller controls remain independent. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private headerEmptyGraph from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPackedFamilyDescriptor
open private oneDomain_eq from Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyTerminalEnrichment
open private applicationWorld from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedFamilyApplication
set_option quotPrecheck false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

section Application
variable
  {strata : EquationStratification env}
  {sourceControls : OriginalWorldControls strata sourceEnv}
  {frontier : List (World strata.rules.length)} {parent : World strata.rules.length}
  {common : List VExpr}
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  (selected : WorldFundedFamilyHeaderAt sourceControls U registry target name levels frontier parent)
  (initial : ContextDerivation sourceEnv U source)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source (.const name levels) (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located major (.app hu hv (.ref domain) body function argument result))
  (sourceGraph : OriginalCaptureMap (common := common) (location.contextDerivation initial) sourceRaw)
  (headerDomain : EndpointRef selected.header.origin.source U [] C (.sort cu))
  (headerBody : EndpointState selected.header.origin.source U [C] selected.header.signature.result (.sort dv))
  (hcu : cu.WF U) (hdv : dv.WF U)
  (headerLocation : Located (selected.header.origin.familyHeader selected.header.seedWF).reference
    (.pi hcu hdv (.ref headerDomain) headerBody))

local notation "headerGraph" => headerEmptyGraph (headerLocation.contextDerivation .nil) common
local notation "sourceSide" => originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph
local notation "headerSide" => originalNativePiRouteSide .nil headerDomain headerBody hcu hdv headerLocation headerGraph

/-- All output queries are computed from the operative replay packet and
its jointly selected carrier. The argument annotation is retained by the
actual packing producer, and is not supplied as a reconstruction premise. -/
theorem WorldApplyPiReplayResult.oneParameterIndependentDescriptor
    {P : VEnv → Prop} {base : OriginalCaptureBase env U registry target}
    {history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide}
    {initialProvenance : WorldEnvironmentProvenance strata U ownerInitial}
    {sourceWorld : WorldEnvironmentProvenance strata U
      (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)}
    {priorWorld : WorldEnvironmentProvenance strata U history.final}
    {wholeInputs : history.whole.WorldInputs strata}
    (answer : WorldApplyPiReplayResult history field major ownerInitial base caps profile P
      sourceControls selected.controls frontier initialProvenance sourceWorld priorWorld wholeInputs)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (domains : selected.header.signature.domains = [C])
    (resultSort : selected.header.signature.result = .sort level) (relevance : Relevant level relevant)
    (domainLocation : Located (selected.header.origin.familyHeader selected.header.seedWF).reference (.ref headerDomain))
    (domainLineage : domainLocation.contextDerivation .nil = .nil)
    (headerRoute : PrefixRoute selected.header.origin.source U [] (.forallE C selected.header.signature.result)
      ((EndpointState.ref (selected.header.origin.familyHeader selected.header.seedWF).reference).cast
        (oneDomain_eq selected.header.signature domains) rfl)
      (.pi hcu hdv (.ref headerDomain) headerBody))
    (flagPresent : flag ∈ answer.packed.request.support.sortFlags)
    (paid : Sponsored frontier [parent]) :
    ∃ request : DataRequest (Profile answer.packed.request.rank),
      request.input = answer.packed.request.key.input ∧
      request.anchor = a.subst (sourceRaw.comp commonLeft) ∧
      flag ∈ request.support.sortFlags ∧
      RankedData.RequestAdmission env U (relations env U registry answer.packed.request.rank) target request
        (a.subst (sourceRaw.comp commonLeft)) (a.subst (sourceRaw.comp commonRight)) ∧
      ∃ query : RichGradedResult sourceEnv env U registry target
        (.app hu hv (.ref domain) body function argument result) answer.selected.locals
        (sourceRaw.comp commonLeft) answer.selected.available
        (.singleton (n := answer.packed.request.rank+1)
          (.family ⟨name, selected.header.seed, relevant, [request]⟩)),
        Nonempty (ControlledStoredQuery sourceControls frontier (.observation query.observation)) := by
  obtain ⟨request, inputEq, anchorEq, flagMember, pairedAdmission, plan, ⟨planReady⟩⟩ :=
    answer.oneParameterIndependentPairedPlan selected.header initial domain body function argument result hu hv
      location sourceGraph headerDomain headerBody hcu hdv headerLocation
      henv below formed domains resultSort relevance domainLocation domainLineage flagPresent
  obtain ⟨restored, ⟨restoredReady⟩⟩ := plan.restoreSingleHeaderControlled domains headerRoute planReady
  obtain ⟨observation, observationReady, _, _⟩ := selected.rebuildPlanControlled
    function answer.selected.locals (sourceRaw.comp commonLeft) restored restoredReady paid
  have paired : Admitted env U registry target request.toKeyData
      (a.subst (sourceRaw.comp commonLeft)) (a.subst (sourceRaw.comp commonRight)) :=
    ⟨pairedAdmission.1, pairedAdmission.2.1, request.support, pairedAdmission.2.2.1,
      pairedAdmission.2.2.2.1, pairedAdmission.2.2.2.2.1,
      pairedAdmission.2.2.2.2.2.1, pairedAdmission.2.2.2.2.2.2⟩
  have admitted := paired.left_diagonal
  have padded := Admitted.pad henv admitted
  have anchorAdmitted : Admitted env U registry target (Key.pad request.toKeyData)
      (Key.pad request.toKeyData).anchor (Key.pad request.toKeyData).anchor := by
    simpa only [Key.pad, anchorEq] using padded
  let functionQuery : RichGradedResult sourceEnv env U registry target function
      answer.selected.locals (sourceRaw.comp commonLeft) answer.selected.available
      (Profile.fn (Key.pad request.toKeyData) (.family ⟨name, selected.header.seed, relevant, [request]⟩)) := {
    rank := answer.packed.request.rank+2
    bound := Nat.le_refl _
    raw := Profile.fn (Key.pad request.toKeyData) (.family ⟨name, selected.header.seed, relevant, [request]⟩)
    footprint := []
    observation := observation
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := fun _ _ impossible => nomatch impossible
    live := Profile.Live.singleton_iff.mpr ⟨anchorAdmitted, trivial⟩ }
  obtain ⟨argumentPadReady⟩ := answer.packedControlled.argument.raise
    (Nat.le_max_left answer.packed.argumentQuery.rank (answer.packed.request.rank+1))
  obtain ⟨query, queryReady⟩ := applicationWorld sourceControls frontier henv hscoped formed
    (.ref domain) body result hu hv functionQuery (answer.packed.argumentQuery.pad henv hscoped formed)
    observationReady argumentPadReady
    (by change GeneralNormalProfileAdapter env U registry target
          answer.packed.request.key.input.pad request.input.pad
        rw [inputEq]; exact .refl _)
    padded
  exact ⟨request, inputEq, anchorEq, flagMember, pairedAdmission, query, queryReady⟩

end Application

section Formation
variable
  {strata : EquationStratification env}
  {sourceControls : OriginalWorldControls strata sourceEnv}
  {frontier : List (World strata.rules.length)} {parent : World strata.rules.length}
  {common : List VExpr}
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  (major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) [a]))
  (selected : WorldFundedFamilyHeaderAt sourceControls U registry target name levels frontier parent)
  (initial : ContextDerivation sourceEnv U source)


variable
  (domain : EndpointRef sourceEnv U source (assignedFamilyApplication major 0 rfl).view.domainExpression (.sort (assignedFamilyApplication major 0 rfl).view.domainLevel))
  (domainEq : (assignedFamilyApplication major 0 rfl).view.domain = .ref domain)


variable
  (sourceGraph : OriginalCaptureMap (common := common) ((domainEq ▸ (assignedFamilyApplication major 0 rfl).view.location).contextDerivation initial) sourceRaw)
  (headerDomain : EndpointRef selected.header.origin.source U [] C (.sort cu))
  (headerBody : EndpointState selected.header.origin.source U [C] selected.header.signature.result (.sort dv))
  (hcu : cu.WF U) (hdv : dv.WF U)
  (headerLocation : Located (selected.header.origin.familyHeader selected.header.seedWF).reference
    (.pi hcu hdv (.ref headerDomain) headerBody))

local notation "headerGraph" => headerEmptyGraph (headerLocation.contextDerivation .nil) common
local notation "sourceSide" => originalApplicationTypeRouteSide initial domain (assignedFamilyApplication major 0 rfl).view.codomain
  (assignedFamilyApplication major 0 rfl).view.function (assignedFamilyApplication major 0 rfl).view.argument (assignedFamilyApplication major 0 rfl).view.result (assignedFamilyApplication major 0 rfl).view.domainWF
  (assignedFamilyApplication major 0 rfl).view.bodyWF (domainEq ▸ (assignedFamilyApplication major 0 rfl).view.location) sourceGraph
local notation "headerSide" => originalNativePiRouteSide .nil headerDomain headerBody hcu hdv headerLocation headerGraph

/-- Complete the independent-header carrier path at the actual major's
assigned formation, retaining the paired request and the selected caller
resources. The original prefix is computed from this SAME major. -/
theorem WorldApplyPiReplayResult.oneParameterIndependentAssignedCertificate
    {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide}
    {initialProvenance : WorldEnvironmentProvenance strata U ownerInitial}
    {sourceWorld : WorldEnvironmentProvenance strata U
      (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)}
    {priorWorld : WorldEnvironmentProvenance strata U history.final}
    {wholeInputs : history.whole.WorldInputs strata}
    (answer : WorldApplyPiReplayResult history field major ownerInitial base caps profile P
      sourceControls selected.controls frontier initialProvenance sourceWorld priorWorld wholeInputs)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (domains : selected.header.signature.domains = [C])
    (resultSort : selected.header.signature.result = .sort level) (relevance : Relevant level relevant)
    (domainLocation : Located (selected.header.origin.familyHeader selected.header.seedWF).reference (.ref headerDomain))
    (domainLineage : domainLocation.contextDerivation .nil = .nil)
    (headerRoute : PrefixRoute selected.header.origin.source U [] (.forallE C selected.header.signature.result)
      ((EndpointState.ref (selected.header.origin.familyHeader selected.header.seedWF).reference).cast
        (oneDomain_eq selected.header.signature domains) rfl)
      (.pi hcu hdv (.ref headerDomain) headerBody))
    (flagPresent : flag ∈ answer.packed.request.support.sortFlags)
    (paid : Sponsored frontier [parent]) :
    ∃ request : DataRequest (Profile answer.packed.request.rank),
      request.input = answer.packed.request.key.input ∧
      request.anchor = a.subst (sourceRaw.comp commonLeft) ∧
      flag ∈ request.support.sortFlags ∧
      RankedData.RequestAdmission env U (relations env U registry answer.packed.request.rank) target request
        (a.subst (sourceRaw.comp commonLeft)) (a.subst (sourceRaw.comp commonRight)) ∧
      ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target major.typeFormation.node
        answer.selected.locals (sourceRaw.comp commonLeft) relevant
        (.singleton (n := answer.packed.request.rank+1) (.family ⟨name, selected.header.seed, relevant, [request]⟩)) footprint,
        footprint.Available answer.selected.available ∧
        Nonempty (ControlledStoredQuery sourceControls frontier (.certificate certificate)) := by
  obtain ⟨request, inputEq, anchorEq, flag, admitted, query, ⟨queryReady⟩⟩ :=
    answer.oneParameterIndependentDescriptor selected initial domain (assignedFamilyApplication major 0 rfl).view.codomain (assignedFamilyApplication major 0 rfl).view.function
      (assignedFamilyApplication major 0 rfl).view.argument (assignedFamilyApplication major 0 rfl).view.result (assignedFamilyApplication major 0 rfl).view.domainWF (assignedFamilyApplication major 0 rfl).view.bodyWF
      (domainEq ▸ (assignedFamilyApplication major 0 rfl).view.location) sourceGraph headerDomain headerBody hcu hdv headerLocation
      henv hscoped below formed domains resultSort relevance domainLocation domainLineage headerRoute
      flagPresent paid
  obtain ⟨footprint, certificate, ready, resources, _, _⟩ :=
    oneParameterFamilyAssignedCode major domain domainEq sourceControls frontier henv admitted query queryReady
  exact ⟨request, inputEq, anchorEq, flag, admitted, footprint, certificate, resources, ⟨ready⟩⟩

end Formation

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
