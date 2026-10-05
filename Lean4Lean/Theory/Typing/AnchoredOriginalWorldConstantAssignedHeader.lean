import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCallerHeaderTransport
import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstantHeader
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldEmptyResources

/-! The constant base of the rigid-application initializer. An actual assigned
certificate is compared with the actual primitive constant and replayed to its
genuine earlier declaration header. Zero-argument constants are included. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

private theorem primitiveConstantFormationCost
    (ordered : sourceEnv.Ordered)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expressionEq : expression = .const name levels) (primitive : reference.Primitive)
    (captured : List Closure) :
    (Closure.close ((EndpointState.ref reference).typeFormation.node.dependencyOrigin ordered) captured).cost <
      (Closure.close (reference.dependencyOrigin ordered) captured).cost := by
  cases reference with
  | left original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl otherWF levelWF lookup wf count equiv closed ambient =>
      exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _)
        (constantHeader_pair_lt ordered lookup wf otherWF count equiv levelWF closed ambient captured)
  | right original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl wf count levelWF lookup otherWF equiv closed ambient =>
      exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _)
        (constantHeader_pair_lt ordered lookup wf otherWF count equiv levelWF closed ambient captured)

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  (initial : ContextDerivation sourceEnv U rootSource)
  (node : EndpointState sourceEnv U source (.const name levels) assigned)
  (location : Located root node)
  (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)

/-- Only the actual current assigned-C world needs sponsorship. Primitive
formation R is a strict original child, and the closed header R is paid by its
actual earlier source. Both calls retain the incoming finite frontier. -/
theorem constantAssignedHeaderWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (frame : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (data : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := OriginalNestedDisplay.ofOccurrence initial location graph) controls baseline frontier frame)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (below : sourceEnv ≤ env)
    (sourceClosed : ∀ source, source ≤ env → P source)
    (paid : Sponsored frontier [originalCallWorld controls .assignedComparison node baseline])
    (banks : ∀ budget, WorldBoundedReplayAt env U registry strata P budget)
    (certificate : RichCert sourceEnv env U registry target node.typeFormation.node locals
      (raw.comp commonLeft) relevant (profile : Profile n) footprint)
    (resources : footprint.Available available)
    (certificateReady : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels controls.ordered,
    ∃ origin : ConstantHeaderOrigin sourceEnv name selection.info,
    ∃ answer : AmbientBoundedParameterReply base caps
      (assigned.subst (raw.comp commonLeft))
      (RetainedHeaderUniverse.display origin selection.seedWF common) commonLeft commonRight
      profile (environmentCost ([] : List Closure)),
      Nonempty (WorldParameterReplyData (P := P) (controls.atHeader origin) .nil frontier answer) := by
  let head := constantPrefix node
  obtain ⟨selection, ledger, assignedEq, _weight⟩ :=
    primitiveHeaderSelection_retained controls.ordered head.reference rfl head.primitive
  obtain ⟨origin⟩ := controls.ordered.constantHeaderOrigin selection.lookup
  let first := OriginalNestedDisplay.ofOccurrence initial location graph
  let last := originalPrefixDisplay initial location graph head.route
  let parent := originalCallWorld controls .assignedComparison node baseline
  have primitiveBound := head.route.dependency_cost_le controls.ordered baselineEnvironment
  have formationLess := Nat.lt_of_lt_of_le
    (primitiveConstantFormationCost controls.ordered head.reference rfl head.primitive baselineEnvironment)
    primitiveBound
  have formationBelow : WorldBelow strata.rules.length
      (originalCallWorld controls .expressionReindex (EndpointState.ref head.reference).typeFormation.node baseline)
      parent :=
    original_child (richSchedule_strict formationLess _ _) _ _ _ _ _
  have headerBelow := originalClosedHeader_below controls origin
    (.ref (origin.familyHeader selection.seedWF).reference) node baseline .expressionReindex .assignedComparison
  have primitivePaid : Sponsored frontier
      [originalCallWorld controls .assignedComparison (.ref head.reference) baseline] := by
    rcases Nat.eq_or_lt_of_le primitiveBound with equal | smaller
    · have worldEq : originalCallWorld controls .assignedComparison (.ref head.reference) baseline = parent := by
        simp only [parent, originalCallWorld, equal]
      simpa only [worldEq] using paid
    · exact singletonSponsoredBelow paid
        (original_child (richSchedule_strict smaller _ _) _ _ _ _ _)
  have assignedPaid : Sponsored frontier
      [originalCallWorld controls .assignedComparison first.node baseline,
       originalCallWorld controls .assignedComparison last.node baseline] := by
    exact paid.merge primitivePaid
  let lastData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := last) controls baseline frontier frame := {
    generation := data.generation, replayable := data.replayable,
    controlled := data.controlled, compatible := data.compatible,
    closed := data.closed, capacity := data.capacity,
    covered := data.covered, hereditary := data.hereditary }
  obtain ⟨compared, ⟨comparedData⟩⟩ := (banks (frontier ++
      [originalCallWorld controls .assignedComparison first.node baseline,
       originalCallWorld controls .assignedComparison last.node baseline])).assigned
    base caps first last commonLeft commonRight controls controls rfl rfl
    baseline baseline frontier rfl assignedPaid frame data frame lastData
    certificate resources certificateReady
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
  have replayPaid : Sponsored frontier [originalCallWorld controls .expressionReindex left.node baseline,
      originalCallWorld (controls.atHeader origin) .expressionReindex right.node .nil] := by
    intro world member
    rcases List.mem_cons.mp member with rfl | member
    · exact singletonSponsoredBelow paid formationBelow _ (List.mem_singleton_self _)
    · cases List.mem_singleton.mp member
      exact singletonSponsoredBelow paid headerBelow _ (List.mem_singleton_self _)
  obtain ⟨replayed, ⟨replayedData⟩⟩ := (banks (frontier ++
      [originalCallWorld controls .expressionReindex left.node baseline,
       originalCallWorld (controls.atHeader origin) .expressionReindex right.node .nil])).observation base caps left right commonLeft commonRight
    controls (controls.atHeader origin) rfl rfl baseline .nil frontier rfl replayPaid
    compared.reply.answer.reply.realization leftData empty.realization headerData
    compared.reply.answer.reply.query.observation compared.reply.answer.reply.query.resources comparedData.query
  let adapted := replayed.mapQuery
    (replayed.answer.reply.query.adaptRequest henv hscoped formed
      compared.reply.answer.reply.query.bound compared.reply.answer.reply.query.adapter)
  let answer : AmbientBoundedParameterReply base caps
      (assigned.subst (raw.comp commonLeft)) right commonLeft commonRight profile
      (environmentCost ([] : List Closure)) := {
    reply := adapted.toBoundedGeneratedQueryReply
    related := by
      have equal := congrArg (fun expression : VExpr => expression.subst commonLeft) typeEq
      change TypeRelated env U registry target (assigned.subst (raw.comp commonLeft))
        ((selection.info.type.instL selection.seed).subst commonLeft) profile
      rw [← equal]
      simpa only [subst_subst] using compared.related
    path := by
      have equal := congrArg (fun expression : VExpr => expression.subst commonLeft) typeEq
      change TypeConversion env U target (assigned.subst (raw.comp commonLeft))
        ((selection.info.type.instL selection.seed).subst commonLeft)
      rw [← equal]
      simpa only [subst_subst] using compared.path
    generation := adapted.generation }
  exact ⟨selection, origin, answer, ⟨⟨replayedData.generation, replayedData.replayable, replayedData.controlled,
    replayedData.compatible, replayedData.query, replayedData.covered, replayedData.hereditary⟩⟩⟩


end

/-- Extract the exact closed code to be retained by the constant query. The
empty footprint follows from the selected reply's actual positive generation,
including merges; it is not inferred from its numerical capacity. -/
theorem AmbientBoundedParameterReply.closedHeaderCertificateWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {levels : List VLevel}
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (controls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length))
    (answer : AmbientBoundedParameterReply base caps start
      (RetainedHeaderUniverse.display origin levelsWF common) commonLeft commonRight
      (profile : Profile n) (environmentCost ([] : List Closure)))
    (data : WorldParameterReplyData (P := P) (controls.atHeader origin) .nil frontier answer)
    (henv : env.Ordered) (sorted : profile.HasType (.sort relevant)) :
    ∃ realization, ∃ certificate : RichCert origin.source env U registry target
        (.ref (origin.familyHeader levelsWF).reference) [] realization relevant profile [],
      Nonempty (ControlledStoredQuery (controls.atHeader origin) frontier (.certificate certificate)) := by
  obtain ⟨footprint, certificate, ready, resources, _⟩ :=
    answer.reply.answer.reply.query.code_controlled henv (controls.atHeader origin) data.query sorted
  have localsEq : answer.reply.answer.reply.locals = [] := by
    exact answer.reply.answer.reply.locals_eq
  have footprintEq : footprint = [] := data.generation.emptyFootprint resources
  have close {realization : Subst} (locals : List Nat) (footprint : Footprint)
      (localsEq : locals = []) (footprintEq : footprint = [])
      (certificate : RichCert origin.source env U registry target
        (.ref (origin.familyHeader levelsWF).reference) locals realization relevant profile footprint)
      (ready : ControlledStoredQuery (controls.atHeader origin) frontier (.certificate certificate)) :
      ∃ output : RichCert origin.source env U registry target
          (.ref (origin.familyHeader levelsWF).reference) [] realization relevant profile [],
        Nonempty (ControlledStoredQuery (controls.atHeader origin) frontier (.certificate output)) := by
    cases localsEq
    cases footprintEq
    exact ⟨certificate, ⟨ready⟩⟩
  obtain ⟨output, outputReady⟩ := close _ _ localsEq footprintEq certificate ready
  exact ⟨_, output, outputReady⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
