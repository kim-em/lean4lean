import Lean4Lean.Theory.Typing.AnchoredOriginalWorldHistoryGroupDispatcher
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureHeadReindexData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureHeadActivation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBaseHistorySelection
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureMergePreservation

/-! Structural reconstruction of an actual destination capture-map head.
Merges select a real branch under the unchanged outer comparison budget;
ordinary and history captures execute their actual owner and route calls. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- Select the actual first merge branch. Its hereditary resource closure is
retained explicitly; closure of the outer union alone would not suffice. -/
theorem WorldGenerated.CaptureHeadReindex.merge
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {firstFrame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ firstAvailable}
    {secondFrame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ secondAvailable}
    {controls : OriginalWorldControls strata sourceEnv}
    {first : WorldGenerated strata P base caps commonLeft commonRight graph firstFrame controls}
    {second : WorldGenerated strata P base caps commonLeft commonRight graph secondFrame controls}
    (firstIH : first.CaptureHeadReindex) :
    (first.merge second).CaptureHeadReindex := by
  cases graph <;> try trivial
  intro frontier replayable compatible ready hereditary valid substitutions
    destinationEnvironment destinationBaseline capacity covered
    assigned variableNode variableProvenance leftAssigned left leftControls sameCutoff sameFuel
    leftEnvironment leftBaseline leftLocals leftAvailable leftFrame leftData henv hscoped formed
    rank profile requestedFootprint requested requestedAvailable requestedReady sponsored bank unary
  simp only [RawOriginalRichFrame.Valid] at valid
  obtain ⟨firstReady⟩ := ready.selectGeneration first
    (fun _ present => List.mem_append_left _ present) rfl rfl
  obtain ⟨firstHereditary⟩ := hereditary.selectGeneration first hereditary.tablesClosed.1
    (List.sublist_append_left _ _) rfl rfl
  have localCapacity : environmentCost (firstFrame.dependencyEnvironment controls.ordered) ≤
      environmentCost ((firstFrame.merge secondFrame).dependencyEnvironment controls.ordered) := by
    change environmentCost (firstFrame.dependencyEnvironment controls.ordered) ≤
      environmentCost (firstFrame.dependencyEnvironment controls.ordered ++ secondFrame.dependencyEnvironment controls.ordered)
    rw [merge_environmentCost_append]
    exact Nat.le_max_left _ _
  have firstCovered : Covered (@EquationControlMeasure.Less strata.rules.length) first.worlds destinationBaseline.worlds := by
    intro world present
    apply covered world
    rw [WorldGenerated.merge_worlds]
    exact List.mem_append_left _ present
  obtain ⟨reply, ⟨data⟩⟩ := firstIH frontier replayable.1 compatible.1 firstReady firstHereditary valid.1
    substitutions destinationBaseline (Nat.le_trans localCapacity capacity) firstCovered
    variableNode variableProvenance left leftControls sameCutoff sameFuel leftBaseline leftFrame leftData
    henv hscoped formed requested requestedAvailable requestedReady sponsored bank unary
  exact ⟨reply, ⟨{
    toWorldGeneratedQueryReplyData := data.toWorldGeneratedQueryReplyData
    localCapacity := fun ordered => Nat.le_trans (data.localCapacity ordered) localCapacity
    localCovered := by
      intro world member
      obtain ⟨previous, present, below⟩ := data.localCovered world member
      refine ⟨previous, ?_, below⟩
      change previous ∈ (first.merge second).worlds
      rw [WorldGenerated.merge_worlds]
      exact List.mem_append_left _ present
    footprint := data.footprint }⟩⟩

/-- The ordinary positive capture constructor exposes the same immutable
reservation and actual tail to the productive R/F/R activation branch. -/
theorem WorldGenerated.ReindexHeadAt.capture
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {tail : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {controls : OriginalWorldControls strata sourceEnv}
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph tail controls)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (tail.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (argument : EndpointState sourceEnv U source a A)
    (location : Located root argument)
    (lineage : location.contextDerivation initial = context)
    (query : RichObs sourceEnv env U registry target argument locals σ (rawInput : Profile k) argumentFootprint)
    (queryAvailable : argumentFootprint.Available available)
    (queryBound : n ≤ k)
    (queryAdapter : GeneralNormalProfileAdapter env U registry target rawInput (raiseProfile k queryBound (input : Profile n)))
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true (support : Profile n) footprint)
    (resources : footprint.Available available) (typed : input.HasType support)
    (arguments : Related env U registry target (a.subst σ) (a.subst τ) (A.subst σ) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    (WorldGenerated.capture generated baseline capacity domain initial argument location lineage query queryAvailable
      queryBound queryAdapter certificate resources typed arguments needs bounded covered).ReindexHeadAt := by
  cases lineage
  intro frontier replayable compatible ready hereditary valid substitutions
    destinationEnvironment destinationBaseline destinationCapacity destinationCovered
    assigned variableNode variableProvenance leftAssigned left leftControls sameCutoff sameFuel
    leftEnvironment leftBaseline leftLocals leftAvailable leftFrame leftData henv hscoped formed
    rank profile requestedFootprint requested requestedAvailable requestedReady sponsored bank unary
  simp only [RawOriginalRichFrame.Valid] at valid
  have tailSubstitutions := by
    cases substitutions with
    | cons tail _ _ => exact tail
  obtain ⟨tailReady⟩ := ready.selectGeneration generated
    (fun _ present => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ present)) rfl rfl
  let tailHereditary : generated.Hereditary frontier :=
    ⟨hereditary.tablesClosed.1, hereditary.bases, hereditary.ready⟩
  obtain ⟨leftEq, rightEq⟩ := generated.erase.capped.generated.realizations
  subst σ
  subst τ
  let tailFrame : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available :=
    ⟨⟨tail, valid⟩, tailSubstitutions⟩
  exact reindexWorldOwnCaptureHead initial argument location domain controls tailFrame generated frontier tailReady
    replayable.1 compatible tailHereditary baseline capacity replayable.2 destinationBaseline
    destinationCapacity destinationCovered variableNode variableProvenance left leftControls sameCutoff sameFuel
    leftBaseline leftFrame leftData henv hscoped formed requested requestedAvailable requestedReady sponsored bank unary

/-- The full structural capture-head dispatcher. All operative capture
constructors execute their genuine lower calls; merge selection retains the
fixed outer comparison budget. No completed head answer is an input. -/
private theorem WorldGenerated.captureHeadReindexInvariant
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {controls : OriginalWorldControls strata sourceEnv}
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame controls) :
    generated.CaptureHeadReindex := by
  induction generated with
  | merge _ _ first _ => exact first.merge
  | identity | empty | bind | weaken => trivial
  | capture generated baseline capacity domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered _ =>
    exact WorldGenerated.ReindexHeadAt.capture generated baseline capacity domain initial argument location lineage
      query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered
  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      _ _ _ _ _ =>
    exact WorldGenerated.ReindexHeadAt.historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed
      ownerOrdered headerOrdered ownerInitial seed seedScope seedControls seedGenerated domainProvenance prior history
      priorGenerated initialProvenance baselines routeInputs historyWellFormed historyControls historyGenerated tailBound
      entries scopes ownerControls owners ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources
      nominalSources priorSources routeSources

/-- An actual destination capture-map head accepts the incoming observation
and constructs its ordinary variable reply through the qualified banks.
The public motive retains the SAME original node, selected data, resource
bounds, hereditary ancestry, and fixed caller budget. -/
theorem WorldGenerated.reindexCaptureHead
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    {nominalContext : ContextDerivation nominalEnv U nominalSource}
    {nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw}
    {nominal : EndpointState nominalEnv U nominalSource argument assigned}
    {provenance : EndpointProvenance nominalContext nominal}
    {frame : RawOriginalRichFrame sourceEnv env U registry target (.cons context domain) locals σ τ available}
    {controls : OriginalWorldControls strata sourceEnv}
    (generated : WorldGenerated strata P base caps commonLeft commonRight
      (.capture graph domain nominalGraph nominal provenance) frame controls) :
    generated.ReindexHeadAt :=
  generated.captureHeadReindexInvariant

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
