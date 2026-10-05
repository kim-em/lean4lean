import Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionDemands
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeAction

/-! Replay a discovered projection demand with its ORIGINAL frozen request
and output path. No naturalized replacement record request is introduced. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem RichObs.replayOutputPath
    (path : GeneralOutputPath env U registry target a b)
    (query : RichObs sourceEnv env U registry target node locals σ (.singleton a) footprint)
    (resources : footprint.Available available) :
    ∃ nextFootprint, Nonempty (RichObs sourceEnv env U registry target node locals σ
      (.singleton b) nextFootprint) ∧ nextFootprint.Available available := by
  induction path with
  | refl => exact ⟨_, ⟨query⟩, resources⟩
  | action path action ih =>
    obtain ⟨fp, ⟨query⟩, resources⟩ := ih
    exact ⟨fp, ⟨.action query action⟩, resources⟩
  | code path action formed ih =>
    obtain ⟨fp, ⟨query⟩, resources⟩ := ih
    obtain ⟨fp, ⟨code⟩, resources⟩ := (RichCert.observe query formed).codeAction action resources
    exact ⟨fp, ⟨.code code⟩, resources⟩
  | pad path ih =>
    obtain ⟨fp, ⟨query⟩, resources⟩ := ih
    exact ⟨fp, ⟨.pad query⟩, resources⟩
  | unpad path ih =>
    obtain ⟨fp, ⟨query⟩, resources⟩ := ih
    exact ⟨fp, ⟨.unpad query⟩, resources⟩

/-- The source-facing completion consumes concrete replies for the retained
major and original field occurrences. Their induction schedules are provided
by projectionReindexSourceStep; the actual request and output path survive. -/
theorem RichProjectionDemand.rebuild
    {left : EndpointState leftEnv U leftSource (.proj name index leftMajor) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index rightMajor) rightType}
    (demand : RichProjectionDemand (node := left) (env := env) (registry := registry)
      (target := target) leftLocals σ leftAvailable atom)
    (rightHead : ProjectionHead right)
    (major : RichObs rightEnv env U registry target (.ref (.right rightHead.major)) rightLocals τ
      (Profile.singleton (n := demand.origin.rank + 1) (.record demand.origin.record)) majorFootprint)
    (majorResources : majorFootprint.Available rightAvailable)
    (field : RichProjectionAssignedReply demand.origin.head rightHead env registry target rightLocals σ τ
      rightAvailable demand.origin.support)
    (formed : (Profile.singleton atom).HasType (.sort relevant)) :
    ∃ footprint, Nonempty (RichCert rightEnv env U registry target right rightLocals τ relevant
      (.singleton atom) footprint) ∧ footprint.Available rightAvailable := by
  let chain := demand.origin.alignment.trans
    (.step field.path demand.origin.typed demand.origin.fieldCode.formed field.code.related (.refl _))
  let projection : RichObs rightEnv env U registry target right rightLocals τ
      demand.origin.request.input (majorFootprint ++ field.code.footprint) :=
    .projection rightHead demand.origin.nameEq demand.origin.member major field.code.certificate
      demand.origin.typed chain
  have available : (majorFootprint ++ field.code.footprint).Available rightAvailable :=
    fun i need hm => (List.mem_append.mp hm).elim (majorResources i need) (field.code.resources i need)
  let selected : RichObs rightEnv env U registry target right rightLocals τ
      (.singleton demand.origin.atom) (majorFootprint ++ field.code.footprint) :=
    .select projection demand.origin.atomMember
  obtain ⟨footprint, ⟨query⟩, resources⟩ := selected.replayOutputPath demand.path available
  exact ⟨footprint, ⟨.observe query formed⟩, resources⟩

/-- Activate the earlier slot with the actual discovered major query. The
argument is one concrete smaller-call answer for that query, not a factory
for arbitrary target profiles. -/
noncomputable def RichProjectionDemand.activatePrior
    {field : EndpointRef sourceEnv U rootSource fieldExpression fieldType}
    {major : EndpointRef sourceEnv U rootSource majorExpression majorType}
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    {location : Located field node} {rawCapture : VExpr}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight) (closed : available.AtomClosed)
    (demand : RichProjectionDemand (node := node) (env := env) (registry := registry)
      (target := target) locals σ available atom)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (headerLocals : List Nat) (declaredLeft : Subst) (headerAvailable : Valuation)
    (expressionEq : value = rawCapture.lift' (.skipN .refl location.binderPrefix.length))
    (answer : HeaderValueAlignment
      (demand.priorPending (major := major) occurrence sourceTail closed domain headerLocals declaredLeft headerAvailable expressionEq).owner
      domain env registry target locals headerLocals σ τ declaredLeft available headerAvailable
      (Profile.singleton (n := demand.origin.rank + 1) (.record demand.origin.record))) :
    RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable initialEnvironment rawCapture
      (rawCapture.subst rootLeft) (rawCapture.subst rootRight) :=
  (demand.priorPending occurrence sourceTail closed domain headerLocals declaredLeft headerAvailable expressionEq).complete answer

/-- Frozen record membership in the generated group is computed from the
retained original query; it is not an assumption on a pre-existing frame. -/
theorem RichProjectionDemand.activatePrior_needed
    {field : EndpointRef sourceEnv U rootSource fieldExpression fieldType}
    {major : EndpointRef sourceEnv U rootSource majorExpression majorType}
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    {location : Located field node} {rawCapture : VExpr}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight) (closed : available.AtomClosed)
    (demand : RichProjectionDemand (node := node) (env := env) (registry := registry)
      (target := target) locals σ available atom)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (headerLocals : List Nat) (declaredLeft : Subst) (headerAvailable : Valuation)
    (expressionEq : value = rawCapture.lift' (.skipN .refl location.binderPrefix.length))
    (answer : HeaderValueAlignment
      (demand.priorPending (major := major) occurrence sourceTail closed domain headerLocals declaredLeft headerAvailable expressionEq).owner
      domain env registry target locals headerLocals σ τ declaredLeft available headerAvailable
      (Profile.singleton (n := demand.origin.rank + 1) (.record demand.origin.record))) :
    majorNeed demand.origin.record ∈ RichGroupedCapture.needs
      [demand.activatePrior occurrence sourceTail closed domain headerLocals declaredLeft headerAvailable expressionEq answer] := by
  simp only [RichGroupedCapture.needs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    activatePrior, PendingRichCapture.complete, RichProjectionDemand.priorPending,
    RichQueryOccurrence.pendingField, RichProjectionDemand.majorOccurrence, RichQueryOccurrence.ofQuery]
  exact List.mem_append_left _ (List.mem_singleton_self _)

/-- A two-slot staged producer: the computed original-major answer creates
the prior group and its exact frozen demand; only then is the original field
comparison called, and its result reconstructs the projected declaration. -/
theorem RichProjectionDemand.captureReplay
    {field : EndpointRef sourceEnv U rootSource fieldExpression fieldType}
    {major : EndpointRef sourceEnv U rootSource majorExpression majorType}
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    {location : Located field node} {rawCapture : VExpr}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight) (closed : available.AtomClosed)
    (demand : RichProjectionDemand (node := node) (env := env) (registry := registry)
      (target := target) locals σ available atom)
    {context : ContextDerivation headerEnv U headerSource}
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (headerLocals : List Nat) (declaredLeft : Subst) (headerAvailable : Valuation)
    (expressionEq : value = rawCapture.lift' (.skipN .refl location.binderPrefix.length))
    (answer : HeaderValueAlignment
      (demand.priorPending (major := major) occurrence sourceTail closed domain headerLocals declaredLeft headerAvailable expressionEq).owner
      domain env registry target locals headerLocals σ τ declaredLeft available headerAvailable
      (Profile.singleton (n := demand.origin.rank + 1) (.record demand.origin.record)))
    (headerOrdered : headerEnv.Ordered)
    (base : OriginalRichFrame headerEnv env U registry target context headerLocals declaredLeft declaredRight headerAvailable)
    {domainX : EndpointRef headerEnv U (A :: headerSource) (.proj name index (.bvar 0)) (.sort xLevel)}
    (rightHead : ProjectionHead (.ref domainX))
    (sorted : (Profile.singleton atom).HasType (.sort relevant)) :
    let prior := demand.activatePrior occurrence sourceTail closed domain headerLocals declaredLeft headerAvailable expressionEq answer
    let nextAvailable := headerAvailable.push (RichGroupedCapture.needs [prior])
    let nextLeft := declaredLeft.cons (rawCapture.subst rootLeft)
    let nextRight := declaredRight.cons (rawCapture.subst rootRight)
    let rightFrame := base.group domain ordered initialEnvironment [prior]
    (RichCert sourceEnv env U registry target demand.origin.head.field locals σ true demand.origin.support demand.origin.fieldFootprint →
      demand.origin.fieldFootprint.Available available →
      richSchedule .assignedComparison
        ((Closure.close ((projectionNatural demand.origin.head).dependencyOrigin ordered)
          (occurrence.frame.dependencyEnvironment ordered)).cost +
         (Closure.close ((projectionNatural rightHead).dependencyOrigin headerOrdered)
          (rightFrame.dependencyEnvironment headerOrdered)).cost) <
      richSchedule .expressionReindex
        ((Closure.close (node.dependencyOrigin ordered) (occurrence.frame.dependencyEnvironment ordered)).cost +
         (Closure.close ((EndpointState.ref domainX).dependencyOrigin headerOrdered)
          (rightFrame.dependencyEnvironment headerOrdered)).cost) →
      Nonempty (RichProjectionAssignedReply demand.origin.head rightHead env registry target
        (Locals.push headerLocals) σ nextLeft nextAvailable demand.origin.support)) →
    ∃ frame : OriginalRichFrame headerEnv env U registry target (.cons context domain)
      (Locals.push headerLocals) nextLeft nextRight nextAvailable,
      frame = rightFrame ∧ ∃ footprint,
        Nonempty (RichCert headerEnv env U registry target (.ref domainX) (Locals.push headerLocals)
          nextLeft relevant (.singleton atom) footprint) ∧ footprint.Available nextAvailable := by
  dsimp only
  intro assignedC
  let prior := demand.activatePrior occurrence sourceTail closed domain headerLocals declaredLeft headerAvailable expressionEq answer
  let rightFrame := base.group domain ordered initialEnvironment [prior]
  have needed := demand.activatePrior_needed occurrence sourceTail closed domain headerLocals declaredLeft
    headerAvailable expressionEq answer
  have leftBound := demand.route.dependency_cost_le ordered (occurrence.frame.dependencyEnvironment ordered)
  have rightBound := rightHead.route.dependency_cost_le headerOrdered (rightFrame.dependencyEnvironment headerOrdered)
  have schedule : richSchedule .assignedComparison
      ((Closure.close ((projectionNatural demand.origin.head).dependencyOrigin ordered)
        (occurrence.frame.dependencyEnvironment ordered)).cost +
       (Closure.close ((projectionNatural rightHead).dependencyOrigin headerOrdered)
        (rightFrame.dependencyEnvironment headerOrdered)).cost) <
    richSchedule .expressionReindex
      ((Closure.close (node.dependencyOrigin ordered) (occurrence.frame.dependencyEnvironment ordered)).cost +
       (Closure.close ((EndpointState.ref domainX).dependencyOrigin headerOrdered)
        (rightFrame.dependencyEnvironment headerOrdered)).cost) := by
    simp only [richSchedule, RichPhase.code, projectionNatural] at *
    omega
  obtain ⟨fieldReply⟩ := assignedC demand.origin.fieldCode demand.fieldResources schedule
  let majorQuery : RichObs headerEnv env U registry target (.ref (.right rightHead.major))
      (Locals.push headerLocals) (declaredLeft.cons (rawCapture.subst rootLeft))
      (Profile.singleton (n := demand.origin.rank + 1) (.record demand.origin.record))
      [(0, majorNeed demand.origin.record)] := .legacy (.legacy (.var _ _ 0 _))
  have majorResources : Footprint.Available [(0, majorNeed demand.origin.record)]
      (headerAvailable.push (RichGroupedCapture.needs [prior])) := by
    intro i need member
    cases List.mem_singleton.mp member
    exact needed
  obtain ⟨fp, query, resources⟩ := demand.rebuild rightHead majorQuery majorResources fieldReply sorted
  exact ⟨rightFrame, rfl, fp, query, resources⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
