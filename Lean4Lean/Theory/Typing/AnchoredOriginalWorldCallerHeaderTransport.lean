import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationFunctionFormation
import Lean4Lean.Theory.Typing.AnchoredOriginalPrefixDisplay
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyHeaderSelection
import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderWorldCalls

/-! Enriched code is transferred through the actual caller constant proof to
its own earlier declaration header. The two original comparisons retain the
caller control prefix; no independent canonical-header controls are equated. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  (initial : ContextDerivation sourceEnv U rootSource)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source (.const name levels) (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located root (.app hu hv (.ref domain) body function argument result))
  (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)

local notation "side" => originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph

/-- The returned origin is selected from the caller's primitive original.
It is a new actual header endpoint, not a relabeling of an incoming carrier. -/
theorem callerConstantHeaderWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (incoming : AmbientBoundedParameterReply base caps
      ((VExpr.forallE A B).subst (raw.comp commonLeft)) (side).functionFormationDisplay
      commonLeft commonRight (profile : Profile n) (environmentCost baselineEnvironment))
    (incomingData : WorldParameterReplyData (P := P) controls baseline frontier incoming)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (below : sourceEnv ≤ env)
    (sorted : profile.HasType (.sort relevant))
    (sourceClosed : ∀ source, source ≤ env → P source)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental (side).node baseline])
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (side).node baseline])) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels controls.ordered,
    ∃ origin : ConstantHeaderOrigin sourceEnv name selection.info,
    ∃ answer : AmbientBoundedParameterReply base caps
      ((VExpr.forallE A B).subst (raw.comp commonLeft))
      (RetainedHeaderUniverse.display origin selection.seedWF common) commonLeft commonRight
      profile (environmentCost ([] : List Closure)),
      Nonempty (WorldParameterReplyData (P := P) (controls.atHeader origin) .nil frontier answer) := by
  let head := constantPrefix function
  obtain ⟨selection, ledger, assignedEq, _weight⟩ :=
    primitiveHeaderSelection_retained controls.ordered head.reference rfl head.primitive
  obtain ⟨origin⟩ := controls.ordered.constantHeaderOrigin selection.lookup
  let first := OriginalNestedDisplay.ofOccurrence initial (.appFunction location) graph
  let last := originalPrefixDisplay initial (.appFunction location) graph head.route
  let parent := originalCallWorld controls .fundamental (side).node baseline
  have functionLess : (Closure.close (function.dependencyOrigin controls.ordered) baselineEnvironment).cost <
      (Closure.close ((side).node.dependencyOrigin controls.ordered) baselineEnvironment).cost := by
    apply Nat.lt_of_lt_of_le _ (application_cost_le_captured _ _ _ _ _ _)
    exact binder_other_cost (by simp [originalApplicationTypeRouteSide]) _
  have primitiveLess := Nat.lt_of_le_of_lt (head.route.dependency_cost_le controls.ordered baselineEnvironment) functionLess
  have formationLess := Nat.lt_of_le_of_lt
    ((EndpointState.ref head.reference).typeFormation_dependency_cost_le controls.ordered baselineEnvironment) primitiveLess
  have lower {context expression assigned}
      (node : EndpointState sourceEnv U context expression assigned) (phase : RichPhase)
      (cost : (Closure.close (node.dependencyOrigin controls.ordered) baselineEnvironment).cost <
        (Closure.close ((side).node.dependencyOrigin controls.ordered) baselineEnvironment).cost) :
      WorldBelow strata.rules.length (originalCallWorld controls phase node baseline) parent :=
    original_child (richSchedule_strict cost _ _) _ _ _ _ _
  have functionBelow := lower function .assignedComparison functionLess
  have primitiveBelow := lower (.ref head.reference) .assignedComparison primitiveLess
  have formationBelow := lower (EndpointState.ref head.reference).typeFormation.node .expressionReindex formationLess
  have headerBelow := originalClosedHeader_below controls origin
    (.ref (origin.familyHeader selection.seedWF).reference) (side).node baseline .expressionReindex .fundamental
  have fund {calls : List (World strata.rules.length)}
      (smaller : ∀ child ∈ calls, WorldBelow strata.rules.length child parent) :
      CallBelow strata.rules.length (frontier ++ calls) (frontier ++ [parent]) := by
    have step := split_call smaller
    have prefixed : ∀ sponsors : List (World strata.rules.length),
        CallBelow strata.rules.length (sponsors ++ calls) (sponsors ++ [parent]) := by
      intro sponsors
      induction sponsors with
      | nil => exact step
      | cons world rest ih => exact ih.cons world
    exact prefixed frontier
  have assignedFunded := fund (calls := [originalCallWorld controls .assignedComparison first.node baseline,
      originalCallWorld controls .assignedComparison last.node baseline]) (fun child member => by
    rcases List.mem_cons.mp member with rfl | member
    · exact functionBelow
    · cases List.mem_singleton.mp member; exact primitiveBelow)
  have assignedPaid : Sponsored frontier [originalCallWorld controls .assignedComparison first.node baseline,
      originalCallWorld controls .assignedComparison last.node baseline] := by
    intro world member
    rcases List.mem_cons.mp member with rfl | member
    · exact singletonSponsoredBelow paid functionBelow _ (List.mem_singleton_self _)
    · cases List.mem_singleton.mp member
      exact singletonSponsoredBelow paid primitiveBelow _ (List.mem_singleton_self _)
  let current := incoming.reply.answer.reply
  let firstData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := first) controls baseline frontier current.realization := {
    generation := incomingData.generation, replayable := incomingData.replayable,
    controlled := incomingData.controlled, compatible := incomingData.compatible,
    closed := current.closed, capacity := incoming.reply.bounded controls.ordered,
    covered := incomingData.covered, hereditary := incomingData.hereditary }
  let lastData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := last) controls baseline frontier current.realization := {
    generation := incomingData.generation, replayable := incomingData.replayable,
    controlled := incomingData.controlled, compatible := incomingData.compatible,
    closed := current.closed, capacity := incoming.reply.bounded controls.ordered,
    covered := incomingData.covered, hereditary := incomingData.hereditary }
  obtain ⟨footprint, certificate, certificateReady, resources, _⟩ :=
    current.query.code_controlled henv controls incomingData.query sorted
  obtain ⟨compared, ⟨comparedData⟩⟩ := (bank _ assignedFunded).assigned base caps first last commonLeft commonRight
    controls controls rfl rfl baseline baseline frontier rfl assignedPaid
    current.realization firstData current.realization lastData certificate resources certificateReady
  have typeEq : head.type.subst raw = selection.info.type.instL selection.seed := by
    rw [assignedEq, (controls.ordered.closedC selection.lookup).instL.subst_eq (σ := raw) .zero]
  let left : OriginalNestedDisplay U common (selection.info.type.instL selection.seed)
      (.sort (EndpointState.ref head.reference).typeFormation.level) :=
    { last.formationDisplay with expression_eq := typeEq.symm }
  let right := RetainedHeaderUniverse.display origin selection.seedWF common
  let empty := RetainedHeaderUniverse.frame origin selection.seedWF common env registry target commonLeft commonRight
  let emptyGenerated : WorldGenerated strata P base caps commonLeft commonRight right.graph
      empty.realization.frame.raw (controls.atHeader origin) :=
    .empty common commonLeft commonRight (origin.sourceBelow.trans below)
      (sourceClosed _ (origin.sourceBelow.trans below)) (controls.atHeader origin)
  have emptyReady : emptyGenerated.Controlled frontier :=
    ⟨.nil, by intro control active; exact Nat.zero_le _, by intro world member; cases member⟩
  let headerData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := right) (controls.atHeader origin) .nil frontier empty.realization := {
    generation := emptyGenerated, replayable := trivial, controlled := emptyReady,
    compatible := ⟨rfl, rfl⟩, closed := by
      intro index need member
      cases member
    capacity := Nat.le_refl _, covered := Covered.refl [],
    hereditary := ⟨trivial, .nil, trivial⟩ }
  let leftData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := left) controls baseline frontier compared.reply.answer.reply.realization := {
    generation := comparedData.generation, replayable := comparedData.replayable,
    controlled := comparedData.controlled, compatible := comparedData.compatible,
    closed := compared.reply.answer.reply.closed, capacity := compared.reply.bounded controls.ordered,
    covered := comparedData.covered, hereditary := comparedData.hereditary }
  have replayFunded := fund (calls := [originalCallWorld controls .expressionReindex left.node baseline,
      originalCallWorld (controls.atHeader origin) .expressionReindex right.node .nil]) (fun child member => by
    rcases List.mem_cons.mp member with rfl | member
    · exact formationBelow
    · cases List.mem_singleton.mp member; exact headerBelow)
  have replayPaid : Sponsored frontier [originalCallWorld controls .expressionReindex left.node baseline,
      originalCallWorld (controls.atHeader origin) .expressionReindex right.node .nil] := by
    intro world member
    rcases List.mem_cons.mp member with rfl | member
    · exact singletonSponsoredBelow paid formationBelow _ (List.mem_singleton_self _)
    · cases List.mem_singleton.mp member
      exact singletonSponsoredBelow paid headerBelow _ (List.mem_singleton_self _)
  obtain ⟨replayed, ⟨replayedData⟩⟩ := (bank _ replayFunded).observation base caps left right commonLeft commonRight
    controls (controls.atHeader origin) rfl rfl baseline .nil frontier rfl replayPaid
    compared.reply.answer.reply.realization leftData empty.realization headerData
    compared.reply.answer.reply.query.observation compared.reply.answer.reply.query.resources comparedData.query
  let adapted := replayed.mapQuery
    (replayed.answer.reply.query.adaptRequest henv hscoped formed
      compared.reply.answer.reply.query.bound compared.reply.answer.reply.query.adapter)
  let answer : AmbientBoundedParameterReply base caps
      ((VExpr.forallE A B).subst (raw.comp commonLeft)) right commonLeft commonRight profile
      (environmentCost ([] : List Closure)) := {
    reply := adapted.toBoundedGeneratedQueryReply
    related := by
      have equal := congrArg (fun expression : VExpr => expression.subst commonLeft) typeEq
      change TypeRelated env U registry target ((VExpr.forallE A B).subst (raw.comp commonLeft))
        ((selection.info.type.instL selection.seed).subst commonLeft) profile
      rw [← equal]
      simpa only [subst_subst] using compared.related
    path := by
      have equal := congrArg (fun expression : VExpr => expression.subst commonLeft) typeEq
      change TypeConversion env U target ((VExpr.forallE A B).subst (raw.comp commonLeft))
        ((selection.info.type.instL selection.seed).subst commonLeft)
      rw [← equal]
      simpa only [subst_subst] using compared.path
    generation := adapted.generation }
  exact ⟨selection, origin, answer, ⟨⟨replayedData.generation, replayedData.replayable, replayedData.controlled,
    replayedData.compatible, replayedData.query, replayedData.covered, replayedData.hereditary⟩⟩⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
