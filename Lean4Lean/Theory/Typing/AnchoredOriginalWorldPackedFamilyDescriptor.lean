import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedFamilyApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplyPiPackedReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPairedFamilyRequest
import Lean4Lean.Theory.Typing.AnchoredOriginalIndependentFamilyHeader

/-! Consume the SAME operative one-parameter history reply to build its
stronger family observer. The requested assigned sort flag is preserved
from packing through the selected capture and the actual source query. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private oneDomain_eq from
  Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyTerminalEnrichment
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

private def headerEmptyGraph (context : ContextDerivation sourceEnv U []) (common : List VExpr) :
    OriginalCaptureMap (common := common) context .id := by
  cases context
  exact .empty common

private theorem headerEmptyGraph_locals (context : ContextDerivation sourceEnv U [])
    (common : List VExpr) (initial : List Nat) :
    (headerEmptyGraph context common).locals initial = [] := by
  cases context
  rfl

private def emptyGraphResources
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw) (available : Valuation) : Prop :=
  match graph with
  | .empty _ => available = (fun _ => [])
  | _ => True

private theorem emptyGraphResources_merge
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (one : emptyGraphResources graph left) (two : emptyGraphResources graph right) :
    emptyGraphResources graph (fun i => left i ++ right i) := by
  cases graph <;> try trivial
  change left = (fun _ => []) at one
  change right = (fun _ => []) at two
  rw [one, two]
  rfl

private theorem WorldGenerated.empty_property
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame controls) :
    emptyGraphResources graph available := by
  induction generated with
  | merge first second one two => exact emptyGraphResources_merge _ one two
  | empty => rfl
  | identity => trivial
  | bind => trivial
  | weaken => trivial
  | capture => trivial
  | historyGroup => trivial

private theorem WorldGenerated.closed_resources
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U []}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : WorldGenerated strata P base caps commonLeft commonRight
      (headerEmptyGraph context common) frame controls) : available = (fun _ => []) := by
  cases context
  exact generated.empty_property

section
variable
  {common : List VExpr}
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  (seed : RetainedRichFamilySeed major env registry target name levels)
  (initial : ContextDerivation sourceEnv U source)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source (.const name levels) (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located major (.app hu hv (.ref domain) body function argument result))
  (sourceGraph : OriginalCaptureMap (common := common) (location.contextDerivation initial) sourceRaw)
  (headerDomain : EndpointRef seed.origin.source U [] C (.sort cu))
  (headerBody : EndpointState seed.origin.source U [C] seed.signature.result (.sort dv))
  (hcu : cu.WF U) (hdv : dv.WF U)
  (headerLocation : Located (seed.origin.familyHeader seed.seedWF).reference
    (.pi hcu hdv (.ref headerDomain) headerBody))

local notation "headerGraph" => headerEmptyGraph (headerLocation.contextDerivation .nil) common
local notation "sourceSide" => originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph
local notation "headerSide" => originalNativePiRouteSide .nil headerDomain headerBody hcu hdv headerLocation headerGraph

/-- No descriptor or selected-frame answer is supplied separately: this
consumer reads the exact captured entries, support witnesses and controlled
argument from the operative replay packet. -/
theorem WorldApplyPiReplayResult.oneParameterDescriptor
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
    (route : PrefixRoute seed.origin.source U [] (.forallE C seed.signature.result)
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
      ∃ query : RichGradedResult sourceEnv env U registry target
        (.app hu hv (.ref domain) body function argument result) answer.selected.locals
        (sourceRaw.comp commonLeft) answer.selected.available
        (.singleton (n := answer.packed.request.rank+1) (.family ⟨name, seed.seed, relevant, [request]⟩)),
        Nonempty (ControlledStoredQuery sourceControls frontier (.observation query.observation)) := by
  have localsEq : answer.whole.reply.answer.reply.locals = [] := by
    have eq := answer.whole.reply.answer.reply.locals_eq
    change answer.whole.reply.answer.reply.locals =
      (headerEmptyGraph (headerLocation.contextDerivation .nil) common).locals base.locals at eq
    exact eq.trans (headerEmptyGraph_locals _ _ _)
  have availableEq : answer.whole.reply.answer.reply.available = (fun _ => []) :=
    answer.wholeWorld.closed_resources
  have headerEq : history.rightDomain = headerDomain :=
    (EndpointState.ref.inj history.rightDomainEq).symm
  have consume : ∀
      (entries : RichGroupedCapture (field := field) (major := major) headerDomain env registry target
        answer.whole.reply.answer.reply.locals (Subst.id.comp commonLeft) answer.whole.reply.answer.reply.available
        ownerInitial a answer.packed.request.key.anchor (a.subst (sourceRaw.comp commonRight))),
      (∀ entry ∈ entries, entry.answer.value.support.sortFlags = answer.packed.request.support.sortFlags) →
      (∀ entry ∈ entries, Nonempty (ControlledStoredQuery headerControls frontier
        (.certificate entry.answer.aligned.certificate))) →
      ((⟨answer.packed.request.rank, answer.packed.request.key.input⟩ : Need) ∈ entries.needs) →
      ∃ request : DataRequest (Profile answer.packed.request.rank),
        request.input = answer.packed.request.key.input ∧
        request.anchor = a.subst (sourceRaw.comp commonLeft) ∧ flag ∈ request.support.sortFlags ∧
        RankedData.RequestAdmission env U (relations env U registry answer.packed.request.rank) target request
          (a.subst (sourceRaw.comp commonLeft)) (a.subst (sourceRaw.comp commonLeft)) ∧
        ∃ query : RichGradedResult sourceEnv env U registry target
          (.app hu hv (.ref domain) body function argument result) answer.selected.locals
          (sourceRaw.comp commonLeft) answer.selected.available
          (.singleton (n := answer.packed.request.rank+1) (.family ⟨name, seed.seed, relevant, [request]⟩)),
          Nonempty (ControlledStoredQuery sourceControls frontier (.observation query.observation)) := by
    rw [localsEq, availableEq]
    intro entries supports ready present
    have sourceReady : ∀ entry ∈ entries, Nonempty (ControlledStoredQuery sourceControls frontier
        (.certificate entry.answer.aligned.certificate)) := by
      intro entry member
      obtain ⟨controlled⟩ := ready entry member
      exact ⟨controlled.recontrol sourceControls sameControls.1 sameControls.2⟩
    obtain ⟨request, inputEq, anchorEq, selected, admission, query, queryReady⟩ :=
      seed.oneParameterApplicationWorld sourceControls frontier (sourceDomain := .ref domain)
        (sourceBody := body) (function := function) (result := result) henv hscoped below formed hu hv hcu hdv domains
        resultSort relevance domainLocation domainLineage route entries sourceReady present answer.packed.argumentQuery
        packedReady.argument answer.packed.request.anchor_eq caller captured phase paid
    obtain ⟨entry, member, flags⟩ := selected
    have presentFlag : flag ∈ request.support.sortFlags := by
      rw [flags, supports entry member]
      exact flagPresent
    exact ⟨request, inputEq, anchorEq, presentFlag, admission, query, queryReady⟩
  cases history with
  | mk leftOrdered rightOrdered leftBelow selected selectedEq sourceFrame headerFrame whole =>
    have selectedEq' : headerDomain = selected := EndpointState.ref.inj selectedEq
    subst selected
    exact consume answer.entries answer.entrySupports answer.entryDeclaredReady answer.captureTrace.inputPresent

end
section Independent
variable
  {common : List VExpr}
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  (seed : IndependentFamilyHeader env U registry target name levels)
  (initial : ContextDerivation sourceEnv U source)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source (.const name levels) (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located major (.app hu hv (.ref domain) body function argument result))
  (sourceGraph : OriginalCaptureMap (common := common) (location.contextDerivation initial) sourceRaw)
  (headerDomain : EndpointRef seed.origin.source U [] C (.sort cu))
  (headerBody : EndpointState seed.origin.source U [C] seed.signature.result (.sort dv))
  (hcu : cu.WF U) (hdv : dv.WF U)
  (headerLocation : Located (seed.origin.familyHeader seed.seedWF).reference
    (.pi hcu hdv (.ref headerDomain) headerBody))

local notation "headerGraph" => headerEmptyGraph (headerLocation.contextDerivation .nil) common
local notation "sourceSide" => originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph
local notation "headerSide" => originalNativePiRouteSide .nil headerDomain headerBody hcu hdv headerLocation headerGraph

/-- Consume the actual selected replay entries at their independent header.
The output keeps the paired request and the controlled header plan together;
no caller-relative constant origin or field comparison is assumed. -/
theorem WorldApplyPiReplayResult.oneParameterIndependentPairedPlan
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
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (domains : seed.signature.domains = [C])
    (resultSort : seed.signature.result = .sort level) (relevance : Relevant level relevant)
    (domainLocation : Located (seed.origin.familyHeader seed.seedWF).reference (.ref headerDomain))
    (domainLineage : domainLocation.contextDerivation .nil = .nil)
    (flagPresent : flag ∈ answer.packed.request.support.sortFlags) :
    ∃ request : DataRequest (Profile answer.packed.request.rank),
      request.input = answer.packed.request.key.input ∧
      request.anchor = a.subst (sourceRaw.comp commonLeft) ∧
      flag ∈ request.support.sortFlags ∧
      RankedData.RequestAdmission env U (relations env U registry answer.packed.request.rank) target request
        (a.subst (sourceRaw.comp commonLeft)) (a.subst (sourceRaw.comp commonRight)) ∧
      ∃ plan : RichFamilyPlanResult env U registry target
          (seed.origin.familyHeader seed.seedWF).reference name seed.seed seed.signature
          .nil (.pi hcu hdv (.ref headerDomain) headerBody) (Subst.id.comp commonLeft)
          [] (fun _ => []) (n := answer.packed.request.rank+2)
          (.fn (Key.pad request.toKeyData) (.family ⟨name, seed.seed, relevant, [request]⟩)),
        Nonempty (plan.WorldControlled headerControls frontier) := by
  have localsEq : answer.whole.reply.answer.reply.locals = [] := by
    exact answer.whole.reply.answer.reply.locals_eq.trans (headerEmptyGraph_locals _ _ _)
  have availableEq : answer.whole.reply.answer.reply.available = (fun _ => []) :=
    answer.wholeWorld.closed_resources
  have headerEq : history.rightDomain = headerDomain :=
    (EndpointState.ref.inj history.rightDomainEq).symm
  have consume : ∀
      (entries : RichGroupedCapture (field := field) (major := major) headerDomain env registry target
        answer.whole.reply.answer.reply.locals (Subst.id.comp commonLeft) answer.whole.reply.answer.reply.available
        ownerInitial a answer.packed.request.key.anchor (a.subst (sourceRaw.comp commonRight))),
      (∀ entry ∈ entries, entry.answer.value.support.sortFlags = answer.packed.request.support.sortFlags) →
      (∀ entry ∈ entries, Nonempty (ControlledStoredQuery headerControls frontier
        (.certificate entry.answer.aligned.certificate))) →
      ((⟨answer.packed.request.rank, answer.packed.request.key.input⟩ : Need) ∈ entries.needs) →
      ∃ request : DataRequest (Profile answer.packed.request.rank),
        request.input = answer.packed.request.key.input ∧
        request.anchor = a.subst (sourceRaw.comp commonLeft) ∧
        flag ∈ request.support.sortFlags ∧
        RankedData.RequestAdmission env U (relations env U registry answer.packed.request.rank) target request
          (a.subst (sourceRaw.comp commonLeft)) (a.subst (sourceRaw.comp commonRight)) ∧
        ∃ plan : RichFamilyPlanResult env U registry target
            (seed.origin.familyHeader seed.seedWF).reference name seed.seed seed.signature
            .nil (.pi hcu hdv (.ref headerDomain) headerBody) (Subst.id.comp commonLeft)
            [] (fun _ => []) (n := answer.packed.request.rank+2)
            (.fn (Key.pad request.toKeyData) (.family ⟨name, seed.seed, relevant, [request]⟩)),
          Nonempty (plan.WorldControlled headerControls frontier) := by
    rw [localsEq, availableEq]
    intro entries supports ready present
    obtain ⟨request, inputEq, anchorEq, selected, admission, plan, planReady⟩ :=
      entries.oneParameterPairedPlanWorld headerControls frontier
        (header := (seed.origin.familyHeader seed.seedWF).reference)
        (signature := seed.signature) (name := name) (levels := seed.seed) (body := headerBody)
        henv below formed hcu hdv domains resultSort relevance domainLocation domainLineage ready present
    obtain ⟨entry, member, flags⟩ := selected
    have presentFlag : flag ∈ request.support.sortFlags := by
      rw [flags, supports entry member]
      exact flagPresent
    refine ⟨request, inputEq, anchorEq.trans answer.packed.request.anchor_eq, presentFlag, ?_, plan, planReady⟩
    rw [answer.packed.request.anchor_eq] at admission
    exact admission
  cases history with
  | mk leftOrdered rightOrdered leftBelow selected selectedEq sourceFrame headerFrame whole =>
    have selectedEq' : headerDomain = selected := EndpointState.ref.inj selectedEq
    subst selected
    exact consume answer.entries answer.entrySupports answer.entryDeclaredReady answer.captureTrace.inputPresent

end Independent

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
