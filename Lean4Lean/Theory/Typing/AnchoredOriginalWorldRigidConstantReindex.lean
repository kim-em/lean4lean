import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidConstantControl
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldConstantAssignedHeader
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
import Lean4Lean.Theory.Typing.AnchoredRigidFamilySpineLive

/-! Independent-source R for an actual rigid constant leaf. The destination's
own primitive constant chooses a genuine earlier header. The same frozen
spine and header universe seed are transported by lower header F/R calls;
the destination's actual generated frame and all hereditary data are retained. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private worldCode singletonSponsoredBelow from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
open private from_left from_both from
  Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

/-- A literal source constant remains that constant under every actual
capture map. The original node, context and map are retained independently. -/
def rigidConstantDisplay
    (node : EndpointState sourceEnv U source (.const name levels) assigned)
    (provenance : EndpointProvenance context node)
    (graph : OriginalCaptureMap (common := common) context raw) :
    OriginalNestedDisplay U common (.const name levels) (assigned.subst raw) :=
  ⟨sourceEnv, source, .const name levels, assigned, context, node, provenance,
    raw, graph, rfl, rfl⟩

private theorem prependCallBelow
    {count : Nat} {calls parent : List (World count)}
    (frontier : List (World count)) (lower : CallBelow count calls parent) :
    CallBelow count (frontier ++ calls) (frontier ++ parent) := by
  induction frontier with
  | nil => exact lower
  | cons world rest ih => exact ih.cons world

/-- Both originals and their frames may be independent. The literal target
constant may have arbitrary original conversion/universe prefixes: its own
primitive source is selected internally, never taken from the incoming leaf. -/
theorem RichRigidConstantInput.reindexWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {leftContext : ContextDerivation leftEnv U leftSource}
    {rightContext : ContextDerivation rightEnv U rightSource}
    {plan : RigidFamilySpine n} {support : Profile n}
    (input : RichRigidConstantInput leftEnv env U registry target name frozenLevels levels plan support)
    (left : EndpointState leftEnv U leftSource (.const name levels) leftType)
    (right : EndpointState rightEnv U rightSource (.const name levels) rightType)
    (leftProvenance : EndpointProvenance leftContext left)
    (rightProvenance : EndpointProvenance rightContext right)
    (leftGraph : OriginalCaptureMap (common := common) leftContext leftRaw)
    (rightGraph : OriginalCaptureMap (common := common) rightContext rightRaw)
    (leftControls : OriginalWorldControls strata leftEnv)
    (rightControls : OriginalWorldControls strata rightEnv)
    (sameCutoff : leftControls.cutoff = rightControls.cutoff)
    (sameFuel : leftControls.fuel = rightControls.fuel)
    (leftBaseline : WorldEnvironmentProvenance strata U leftEnvironment)
    (rightBaseline : WorldEnvironmentProvenance strata U rightEnvironment)
    (frontier : List (World strata.rules.length))
    (leftFrame : OriginalCaptureRealization leftGraph env registry target leftLocals
      commonLeft commonRight leftAvailable)
    (leftData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := rigidConstantDisplay left leftProvenance leftGraph)
      leftControls leftBaseline frontier leftFrame)
    (rightFrame : OriginalCaptureRealization rightGraph env registry target rightLocals
      commonLeft commonRight rightAvailable)
    (rightData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := rigidConstantDisplay right rightProvenance rightGraph)
      rightControls rightBaseline frontier rightFrame)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceClosed : ∀ source, source ≤ env → P source)
    (queryReady : ControlledStoredQuery leftControls frontier
      (.observation (input.observation left leftLocals (leftRaw.comp commonLeft))))
    (paid : Sponsored frontier
      [originalCallWorld leftControls .expressionReindex left leftBaseline,
       originalCallWorld rightControls .expressionReindex right rightBaseline])
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld leftControls .expressionReindex left leftBaseline,
       originalCallWorld rightControls .expressionReindex right rightBaseline]))
    (replay : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld leftControls .expressionReindex left leftBaseline,
       originalCallWorld rightControls .expressionReindex right rightBaseline])) :
    ∃ result : AmbientBoundedGeneratedQueryReply base caps
        (rigidConstantDisplay right rightProvenance rightGraph) commonLeft commonRight
        (.singleton (plan.atom name frozenLevels [])) (environmentCost rightEnvironment),
      Nonempty (WorldGeneratedQueryReplyData (P := P) rightControls rightBaseline frontier result) := by
  have leftBelow : leftEnv ≤ env := leftData.generation.erase.ambientGenerated.ambient.2.below
  have rightBelow : rightEnv ≤ env := rightData.generation.erase.ambientGenerated.ambient.2.below
  have leftPaid : Sponsored frontier [originalCallWorld leftControls .expressionReindex left leftBaseline] :=
    fun world member => paid world (List.mem_cons.mpr (.inl (List.mem_singleton.mp member)))
  have rightPaid : Sponsored frontier [originalCallWorld rightControls .expressionReindex right rightBaseline] :=
    fun world member => paid world (List.mem_cons.mpr (.inr member))
  let sourceHeader := EndpointState.ref (input.origin.familyHeader input.seedWF).reference
  let sourceControls := leftControls.atHeader input.origin
  let sourceFrame : OriginalRichFrame input.origin.source env U registry target .nil []
      input.realization commonLeft (fun _ => []) := .nil
  have sourceData : WorldUnaryFrameData P sourceControls frontier sourceFrame .nil := by
    refine ⟨?_, ?_, ?_, .nil sourceControls, ?_⟩
    · simpa only [sourceFrame, OriginalRichFrame.Ambient, OriginalRichFrame.nil,
        RawOriginalRichFrame.Ambient, and_true] using input.origin.sourceBelow.trans leftBelow
    · simpa only [sourceFrame, OriginalRichFrame.nil, RawOriginalRichFrame.AllSources,
        and_true] using sourceClosed _ (input.origin.sourceBelow.trans leftBelow)
    · intro query member
      simp only [sourceFrame, OriginalRichFrame.nil, RawOriginalRichFrame.storedQueries,
        List.not_mem_nil] at member
    · exact ⟨(fun _ _ member => nomatch member), rfl, rfl⟩
  have sourceLower := originalClosedHeader_below leftControls input.origin sourceHeader
    left leftBaseline .fundamental .expressionReindex
  have sourceFunded := prependCallBelow frontier (from_left
    (other := originalCallWorld rightControls .expressionReindex right rightBaseline)
    (calls := [originalCallWorld sourceControls .fundamental sourceHeader .nil])
    (by intro world member; cases List.mem_singleton.mp member; exact sourceLower))
  obtain ⟨answer, ⟨answerReady⟩⟩ := worldCode sourceControls sourceFrame .nil frontier _ unary
    sourceFunded (singletonSponsoredBelow leftPaid sourceLower) (.ofLocation .here .nil) sourceData
    henv hscoped (by intro index need member; cases member) formed .nil input.certificate
    (by intro index need member; cases member)
    (input.certificateControlled leftControls left leftLocals (leftRaw.comp commonLeft) queryReady)
  let primitive := constantPrefix right
  obtain ⟨selection, ledger, assignedEq, weight⟩ :=
    primitiveHeaderSelection_retained rightControls.ordered primitive.reference rfl primitive.primitive
  have sameInfo : selection.info = input.info :=
    Option.some.inj ((rightBelow.constants selection.lookup).symm.trans input.lookup)
  have targetLookup : rightEnv.constants name = some input.info := sameInfo ▸ selection.lookup
  obtain ⟨origin⟩ := rightControls.ordered.constantHeaderOrigin targetLookup
  let targetControls := rightControls.atHeader origin
  let leftHeader := RetainedHeaderUniverse.display input.origin input.seedWF common
  let rightHeader := RetainedHeaderUniverse.display origin input.seedWF common
  let leftEmpty := RetainedHeaderUniverse.frame input.origin input.seedWF common env registry target commonLeft commonRight
  let rightEmpty := RetainedHeaderUniverse.frame origin input.seedWF common env registry target commonLeft commonRight
  let leftGenerated : WorldGenerated strata P base caps commonLeft commonRight leftHeader.graph
      leftEmpty.realization.frame.raw sourceControls :=
    .empty common commonLeft commonRight (input.origin.sourceBelow.trans leftBelow)
      (sourceClosed _ (input.origin.sourceBelow.trans leftBelow)) sourceControls
  let rightGenerated : WorldGenerated strata P base caps commonLeft commonRight rightHeader.graph
      rightEmpty.realization.frame.raw targetControls :=
    .empty common commonLeft commonRight (origin.sourceBelow.trans rightBelow)
      (sourceClosed _ (origin.sourceBelow.trans rightBelow)) targetControls
  have leftReady : leftGenerated.Controlled frontier :=
    ⟨.nil, by intro control active; exact Nat.zero_le _, by intro world member; cases member⟩
  have rightReady : rightGenerated.Controlled frontier :=
    ⟨.nil, by intro control active; exact Nat.zero_le _, by intro world member; cases member⟩
  let leftHeaderData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := leftHeader) sourceControls .nil frontier leftEmpty.realization := {
    generation := leftGenerated, replayable := trivial, controlled := leftReady,
    compatible := ⟨rfl, rfl⟩, closed := (fun _ _ member => nomatch member),
    capacity := Nat.le_refl _, covered := Covered.refl [], hereditary := ⟨trivial, .nil, trivial⟩ }
  let rightHeaderData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := rightHeader) targetControls .nil frontier rightEmpty.realization := {
    generation := rightGenerated, replayable := trivial, controlled := rightReady,
    compatible := ⟨rfl, rfl⟩, closed := (fun _ _ member => nomatch member),
    capacity := Nat.le_refl _, covered := Covered.refl [], hereditary := ⟨trivial, .nil, trivial⟩ }
  have leftHeaderLower := originalClosedHeader_below leftControls input.origin leftHeader.node
    left leftBaseline .expressionReindex .expressionReindex
  have rightHeaderLower := originalClosedHeader_below rightControls origin rightHeader.node
    right rightBaseline .expressionReindex .expressionReindex
  have headerPaid := (singletonSponsoredBelow leftPaid leftHeaderLower).merge
    (singletonSponsoredBelow rightPaid rightHeaderLower)
  have headerFunded := prependCallBelow frontier (from_both leftHeaderLower rightHeaderLower)
  obtain ⟨transported, ⟨transportedData⟩⟩ := (replay _ headerFunded).observation base caps
    leftHeader rightHeader commonLeft commonRight sourceControls targetControls sameCutoff sameFuel
    .nil .nil frontier rfl headerPaid leftEmpty.realization leftHeaderData rightEmpty.realization rightHeaderData
    (.code answer.certificate) answer.resources answerReady.code
  obtain ⟨footprint, certificate, certificateReady, resources, _⟩ :=
    transported.answer.reply.query.code_controlled henv targetControls transportedData.query input.certificate.formed
  have localsEq : transported.answer.reply.locals = [] := transported.answer.reply.locals_eq
  have footprintEq : footprint = [] := transportedData.generation.emptyFootprint resources
  have retain (locals : List Nat) (footprint : Footprint) (localsEq : locals = []) (footprintEq : footprint = [])
      (certificate : RichCert origin.source env U registry target rightHeader.node locals commonLeft true support footprint)
      (ready : ControlledStoredQuery targetControls frontier (.certificate certificate)) :
      ∃ actual : RichCert origin.source env U registry target rightHeader.node [] commonLeft true support [],
        Nonempty (ControlledStoredQuery targetControls frontier (.certificate actual)) := by
    cases localsEq
    cases footprintEq
    exact ⟨certificate, ⟨ready⟩⟩
  obtain ⟨actual, ⟨actualReady⟩⟩ := retain _ _ localsEq footprintEq certificate certificateReady
  let moved : RichRigidConstantInput rightEnv env U registry target name frozenLevels levels plan support := {
    info := input.info, origin := origin, lookup := input.lookup, inert := input.inert,
    seed := input.seed, seedWF := input.seedWF, seedLength := input.seedLength,
    frozenWF := input.frozenWF, levelsWF := input.levelsWF,
    seedFrozen := input.seedFrozen, frozenLevelsEq := input.frozenLevelsEq,
    typeClosed := input.typeClosed, realization := commonLeft, certificate := actual,
    ready := input.ready, typed := input.typed }
  let query : RichGradedResult rightEnv env U registry target right rightLocals (rightRaw.comp commonLeft)
      rightAvailable (.singleton (plan.atom name frozenLevels [])) := {
    rank := n, bound := Nat.le_refl _, raw := .singleton (plan.atom name frozenLevels []),
    footprint := [], observation := moved.observation right rightLocals (rightRaw.comp commonLeft),
    adapter := by rw [raiseProfile_self]; exact .refl _,
    resources := (fun _ _ member => nomatch member),
    live := input.ready.live plan name frozenLevels [] }
  let result : AmbientBoundedGeneratedQueryReply base caps
      (rigidConstantDisplay right rightProvenance rightGraph) commonLeft commonRight
      (.singleton (plan.atom name frozenLevels [])) (environmentCost rightEnvironment) := {
    answer := {
      reply := {
        locals := rightLocals, available := rightAvailable, realization := rightFrame,
        generated := rightData.generation.erase.capped.generated, query := query, closed := rightData.closed }
      capped := rightData.generation.erase.capped }
    bounded := fun _ => rightData.capacity
    generation := rightData.generation.erase.ambientGenerated }
  have targetHeaderPaid := singletonSponsoredBelow rightPaid
    (originalClosedHeader_below rightControls origin rightHeader.node right rightBaseline
      .fundamental .expressionReindex)
  exact ⟨result, ⟨{
    generation := rightData.generation, replayable := rightData.replayable,
    controlled := rightData.controlled, compatible := rightData.compatible,
    query := moved.observationControlled rightControls right rightLocals (rightRaw.comp commonLeft)
      actualReady targetHeaderPaid,
    covered := rightData.covered, hereditary := rightData.hereditary }⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
