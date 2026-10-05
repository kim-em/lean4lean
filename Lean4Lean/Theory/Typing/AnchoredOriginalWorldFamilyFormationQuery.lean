import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPackedFamilyDescriptor
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentPair

/-! The rebuilt one-parameter descriptor follows the actual original prefix
back to the major's assigned formation. No comparison or replacement frame
is needed; the certificate keeps exactly the query-selected resources. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private checks AtomWF FamilyWF RequestWF AtomTyped from
  Lean4Lean.Theory.Typing.AnchoredProfiles
open private headerEmptyGraph from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPackedFamilyDescriptor
open private oneDomain_eq from Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyTerminalEnrichment
set_option quotPrecheck false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private theorem requestFamilySorted
    {request : DataRequest (Profile n)}
    (admitted : RankedData.RequestAdmission env U (relations env U registry n) target request left right)
    (name : Name) (levels : List VLevel) (relevant : Bool) :
    (Profile.singleton (n := n+1) (.family ⟨name, levels, relevant, [request]⟩)).HasType
      (.sort relevant) := by
  refine ⟨?_, Profile.WF.sort (n := n+1) relevant, ?_⟩
  · intro atom member
    cases List.mem_singleton.mp member
    intro selected member
    cases List.mem_singleton.mp member
    exact ⟨admitted.2.2.1.wf_value, admitted.2.2.2.1.wf_value⟩
  · intro atom member
    cases List.mem_singleton.mp member
    exact ⟨_, List.mem_singleton_self _, rfl⟩

/-- This is the prefix computed by the same singleton spine selector used
by the first retained family history. Its start is the actual major formation. -/
noncomputable def oneParameterFormationRoute
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) [argument])) :
    let application := assignedFamilyApplication major 0 rfl
    PrefixRoute sourceEnv U source (.app (.const name levels) argument)
      major.typeFormation.node
      (.app (application).view.domainWF (application).view.bodyWF (application).view.domain
        (application).view.codomain (application).view.function (application).view.argument (application).view.result) :=
  (assignedFamilyApplication major 0 rfl).selected.route

/-- Restore the SAME enriched descriptor at its proper original assigned
endpoint. The admission is the actual one returned by the terminal producer;
it provides well-formedness even when the value input is empty. -/
theorem oneParameterFamilyAssignedCode
    {strata : EquationStratification env}
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) [argument]))
    (domain : EndpointRef sourceEnv U source
      (assignedFamilyApplication major 0 rfl).view.domainExpression
      (.sort (assignedFamilyApplication major 0 rfl).view.domainLevel))
    (domainEq : (assignedFamilyApplication major 0 rfl).view.domain = .ref domain)
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length))
    (henv : env.Ordered)
    {request : DataRequest (Profile n)}
    (admitted : RankedData.RequestAdmission env U (relations env U registry n) target request left right)
    (query : RichGradedResult sourceEnv env U registry target
      (.app (assignedFamilyApplication major 0 rfl).view.domainWF
        (assignedFamilyApplication major 0 rfl).view.bodyWF
        (.ref domain)
        (assignedFamilyApplication major 0 rfl).view.codomain
        (assignedFamilyApplication major 0 rfl).view.function
        (assignedFamilyApplication major 0 rfl).view.argument
        (assignedFamilyApplication major 0 rfl).view.result)
      locals σ available (.singleton (n := n+1) (.family ⟨name, seed, relevant, [request]⟩)))
    (ready : ControlledStoredQuery controls frontier (.observation query.observation)) :
    ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target major.typeFormation.node
        locals σ relevant (.singleton (n := n+1) (.family ⟨name, seed, relevant, [request]⟩)) footprint,
      ∃ output : ControlledStoredQuery controls frontier (.certificate certificate),
        footprint.Available available ∧ output.annotation.worlds ⊆ ready.annotation.worlds ∧
        ∀ policy, certificate.headDepth policy ≤ query.observation.headDepth policy := by
  obtain ⟨footprint, certificate, annotation, resources, worlds, depth⟩ :=
    query.code_worlds_depth henv ready.annotation (requestFamilySorted admitted name seed relevant)
  have route := oneParameterFormationRoute major
  dsimp only at route
  rw [domainEq] at route
  let restored := RichCert.route route certificate
  let restoredReady : ControlledStoredQuery controls frontier (.certificate restored) := {
    annotation := .route route annotation
    within := by
      intro control active
      exact Nat.le_trans (by simpa only [restored, StoredOriginalQuery.headDepth, RichCert.headDepth] using depth _)
        (ready.within control active)
    sponsored := fun world member => ready.sponsored world (worlds member) }
  refine ⟨footprint, restored, restoredReady, resources, worlds, ?_⟩
  intro policy
  simpa only [restored, RichCert.headDepth] using depth policy

section Descriptor
variable
  {common : List VExpr}
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  (major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) [a]))
  (seed : RetainedRichFamilySeed major env registry target name levels)
  (initial : ContextDerivation sourceEnv U source)


variable
  (domain : EndpointRef sourceEnv U source (assignedFamilyApplication major 0 rfl).view.domainExpression (.sort (assignedFamilyApplication major 0 rfl).view.domainLevel))
  (domainEq : (assignedFamilyApplication major 0 rfl).view.domain = .ref domain)


variable
  (sourceGraph : OriginalCaptureMap (common := common) ((domainEq ▸ (assignedFamilyApplication major 0 rfl).view.location).contextDerivation initial) sourceRaw)
  (headerDomain : EndpointRef seed.origin.source U [] C (.sort cu))
  (headerBody : EndpointState seed.origin.source U [C] seed.signature.result (.sort dv))
  (hcu : cu.WF U) (hdv : dv.WF U)
  (headerLocation : Located (seed.origin.familyHeader seed.seedWF).reference
    (.pi hcu hdv (.ref headerDomain) headerBody))

local notation "headerGraph" => headerEmptyGraph (headerLocation.contextDerivation .nil) common
local notation "sourceSide" => originalApplicationTypeRouteSide initial domain (assignedFamilyApplication major 0 rfl).view.codomain
  (assignedFamilyApplication major 0 rfl).view.function (assignedFamilyApplication major 0 rfl).view.argument (assignedFamilyApplication major 0 rfl).view.result (assignedFamilyApplication major 0 rfl).view.domainWF
  (assignedFamilyApplication major 0 rfl).view.bodyWF (domainEq ▸ (assignedFamilyApplication major 0 rfl).view.location) sourceGraph
local notation "headerSide" => originalNativePiRouteSide .nil headerDomain headerBody hcu hdv headerLocation headerGraph

/-- The actual captured descriptor is now a controlled query at the major's
assigned formation, ready for the proper-major assigned recursive case.
The original prefix is computed internally from this SAME major. -/
theorem WorldApplyPiReplayResult.oneParameterAssignedCertificate
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {sourceControls : OriginalWorldControls strata sourceEnv}
    {headerControls : OriginalWorldControls strata seed.origin.source}
    {frontier : List (World strata.rules.length)}
    {history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide}
    {initialProvenance : WorldEnvironmentProvenance strata U ownerInitial}
    {sourceWorld : WorldEnvironmentProvenance strata U
      (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)}
    {priorWorld : WorldEnvironmentProvenance strata U history.final}
    {wholeInputs : history.whole.WorldInputs strata}
    (answer : WorldApplyPiReplayResult history field major ownerInitial base caps profile P
      sourceControls headerControls frontier initialProvenance sourceWorld priorWorld wholeInputs)
    (sameControls : headerControls.HasPrefix sourceControls.cutoff sourceControls.fuel)
    (packedReady : answer.packed.Controlled sourceControls frontier)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (domains : seed.signature.domains = [C])
    (resultSort : seed.signature.result = .sort level) (relevance : Relevant level relevant)
    (domainLocation : Located (seed.origin.familyHeader seed.seedWF).reference (.ref headerDomain))
    (domainLineage : domainLocation.contextDerivation .nil = .nil)
    (headerRoute : PrefixRoute seed.origin.source U [] (.forallE C seed.signature.result)
      ((EndpointState.ref (seed.origin.familyHeader seed.seedWF).reference).cast
        (oneDomain_eq seed.signature domains) rfl)
      (.pi hcu hdv (.ref headerDomain) headerBody))
    (flagPresent : flag ∈ answer.packed.request.support.sortFlags)
    (caller : EndpointState sourceEnv U source callerExpression callerAssigned)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase)
    (paid : Sponsored frontier [originalCallWorld sourceControls phase caller captured]) :
    ∃ request : DataRequest (Profile answer.packed.request.rank),
      request.input = answer.packed.request.key.input ∧
      request.anchor = a.subst (sourceRaw.comp commonLeft) ∧
      flag ∈ request.support.sortFlags ∧
      RankedData.RequestAdmission env U (relations env U registry answer.packed.request.rank) target request
        (a.subst (sourceRaw.comp commonLeft)) (a.subst (sourceRaw.comp commonLeft)) ∧
      ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target major.typeFormation.node
        answer.selected.locals (sourceRaw.comp commonLeft) relevant
        (.singleton (n := answer.packed.request.rank+1) (.family ⟨name, seed.seed, relevant, [request]⟩)) footprint,
        footprint.Available answer.selected.available ∧
        Nonempty (ControlledStoredQuery sourceControls frontier (.certificate certificate)) := by
  obtain ⟨request, inputEq, anchorEq, flag, admitted, query, ⟨queryReady⟩⟩ :=
    answer.oneParameterDescriptor seed initial domain (assignedFamilyApplication major 0 rfl).view.codomain (assignedFamilyApplication major 0 rfl).view.function
      (assignedFamilyApplication major 0 rfl).view.argument (assignedFamilyApplication major 0 rfl).view.result (assignedFamilyApplication major 0 rfl).view.domainWF (assignedFamilyApplication major 0 rfl).view.bodyWF
      (domainEq ▸ (assignedFamilyApplication major 0 rfl).view.location) sourceGraph headerDomain headerBody hcu hdv headerLocation sameControls packedReady
      henv hscoped below formed domains resultSort relevance domainLocation domainLineage headerRoute
      flagPresent caller captured phase paid
  obtain ⟨footprint, certificate, ready, resources, _, _⟩ :=
    oneParameterFamilyAssignedCode major domain domainEq sourceControls frontier henv admitted query queryReady
  exact ⟨request, inputEq, anchorEq, flag, admitted, footprint, certificate, resources, ⟨ready⟩⟩

end Descriptor

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
