import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidConstantControl
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldConstantAssignedHeader
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCallerHeaderUniverse
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldUnaryDiagonal
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyParameterReplay
import Lean4Lean.Theory.Typing.AnchoredRigidFamilySpineLive

/-! Primitive rigid constant F executes its retained earlier header, then
returns the same requested support to the caller's actual assigned formation.
The universe route and both original reindex endpoints are computed below the
constant; no header semantic answer or assigned certificate is supplied. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private worldCode singletonSponsoredBelow from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
open private primitiveConstantFormationCost from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldConstantAssignedHeader
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

private theorem prefixCalls
    {strata : EquationStratification env}
    {calls : List (World strata.rules.length)} {parent : World strata.rules.length}
    (frontier : List (World strata.rules.length))
    (lower : ∀ child ∈ calls, WorldBelow strata.rules.length child parent) :
    CallBelow strata.rules.length (frontier ++ calls) (frontier ++ [parent]) := by
  have initial := split_call lower
  induction frontier with
  | nil => exact initial
  | cons world rest ih => exact ih.cons world

/-- This is the primitive shared `rigidFamily` F clause. The retained header
query is run at its real declaration source with the caller's left realization
as the output realization. Its exact output is replayed through the real
universe equality and primitive formation, then frozen to the caller table. -/
theorem RichRigidConstantInput.primitiveWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {plan : RigidFamilySpine n} {support : Profile n}
    (input : RichRigidConstantInput sourceEnv env U registry target name frozenLevels levels plan support)
    (reference : EndpointRef sourceEnv U source (.const name levels) assigned)
    (primitive : reference.Primitive)
    (provenance : EndpointProvenance context (.ref reference))
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds)
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (sourceClosed : ∀ source, source ≤ env → P source)
    (queryReady : ControlledStoredQuery controls frontier
      (.observation (input.observation (.ref reference) locals σ)))
    (paid : Sponsored frontier [originalCallWorld controls .fundamental (.ref reference) baseline])
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref reference) baseline]))
    (replay : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref reference) baseline])) :
    ∃ answer : RichComputationalValue sourceEnv env U registry target (.ref reference)
        locals σ τ available (.singleton (plan.atom name frozenLevels [])),
      Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)) ∧
      Nonempty (ControlledStoredQuery controls frontier (.observation answer.rightQuery.observation)) := by
  let certificateReady := input.certificateControlled controls (.ref reference) locals σ queryReady
  have below : sourceEnv ≤ env := data.ambient.below
  let header := EndpointState.ref (input.origin.familyHeader input.seedWF).reference
  let hc := controls.atHeader input.origin
  let emptyFrame : OriginalRichFrame input.origin.source env U registry target .nil
      [] input.realization σ (fun _ => []) := .nil
  have emptyData : WorldUnaryFrameData P hc frontier emptyFrame .nil := by
    refine ⟨?_, ?_, ?_, .nil hc, ?_⟩
    · simpa only [emptyFrame, OriginalRichFrame.Ambient, OriginalRichFrame.nil,
        RawOriginalRichFrame.Ambient, and_true] using input.origin.sourceBelow.trans below
    · simpa only [emptyFrame, OriginalRichFrame.nil, RawOriginalRichFrame.AllSources,
        and_true] using sourceClosed _ (input.origin.sourceBelow.trans below)
    · intro query member
      simp only [emptyFrame, OriginalRichFrame.nil, RawOriginalRichFrame.storedQueries,
        List.not_mem_nil] at member
    · exact ⟨(fun _ _ member => nomatch member), rfl, rfl⟩
  have headerLower := originalClosedHeader_below controls input.origin header
    (.ref reference) baseline .fundamental .fundamental
  have headerPaid := singletonSponsoredBelow paid headerLower
  have headerFunded := prefixCalls frontier (calls := [originalCallWorld hc .fundamental header .nil])
    (by intro child member; cases List.mem_singleton.mp member; exact headerLower)
  obtain ⟨headerAnswer, ⟨headerReady⟩⟩ := worldCode hc emptyFrame .nil frontier _ unary
    headerFunded headerPaid (.ofLocation .here .nil) emptyData henv hscoped
    (by intro index need member; cases member) formed .nil
    input.certificate (by intro index need member; cases member) certificateReady
  obtain ⟨selection, ledger, assignedEq, weight⟩ :=
    primitiveHeaderSelection_retained controls.ordered reference rfl primitive
  have sameInfo : selection.info = input.info :=
    Option.some.inj ((below.constants selection.lookup).symm.trans input.lookup)
  have assignedEqual : assigned = input.info.type.instL selection.seed := by
    rw [assignedEq, sameInfo]
  have seedAssigned : List.Forall₂ (· ≈ ·) input.seed selection.seed :=
    Lean4Lean.List.Forall₂.trans (T := (· ≈ ·)) (fun _ _ _ a b => a.trans b)
      input.seedFrozen (Lean4Lean.List.Forall₂.trans (T := (· ≈ ·)) (fun _ _ _ a b => a.trans b)
        input.frozenLevelsEq (Lean4Lean.List.Forall₂.imp (fun _ _ equal => equal.symm)
          (Lean4Lean.List.Forall₂.flip selection.equivalent)))
  obtain ⟨typeCode, related⟩ := input.fromHeaderAnswerAt henv hscoped formed headerAnswer
    input.levelsWF input.frozenLevelsEq selection.seedWF seedAssigned
  let diagonal := frame.leftDiagonal
  let diagonalData := data.leftDiagonal
  let sandbox := diagonal.captureBase substitutions.left
  let identity := diagonalData.generation substitutions.left
  obtain ⟨identityReady⟩ := diagonalData.controlled substitutions.left
  let first := RetainedHeaderUniverse.display input.origin input.seedWF source
  let empty := RetainedHeaderUniverse.frame input.origin input.seedWF source env registry target σ σ
  let emptyGenerated : WorldGenerated strata P sandbox sandbox.initialCaps σ σ first.graph
      empty.realization.frame.raw hc :=
    .empty source σ σ (input.origin.sourceBelow.trans below)
      (sourceClosed _ (input.origin.sourceBelow.trans below)) hc
  have emptyReady : emptyGenerated.Controlled frontier :=
    ⟨.nil, by intro control active; exact Nat.zero_le _, by intro world member; cases member⟩
  let headerQuery : RichGradedResult input.origin.source env U registry target header [] σ
      (fun _ => []) support := {
    rank := n, bound := Nat.le_refl _, raw := support, footprint := headerAnswer.footprint,
    observation := .code headerAnswer.certificate,
    adapter := by rw [raiseProfile_self]; exact .refl _,
    resources := headerAnswer.resources,
    live := Profile.HasType.sortable_live headerAnswer.certificate.formed }
  let incoming : AmbientBoundedParameterReply sandbox sandbox.initialCaps
      ((input.info.type.instL input.seed).subst σ) first σ σ support (environmentCost ([] : List Closure)) := {
    reply := {
      answer := {
        reply := {
          locals := [], available := fun _ => [], realization := empty.realization,
          generated := emptyGenerated.erase.capped.generated,
          query := headerQuery, closed := by intro index need member; cases member }
        capped := emptyGenerated.erase.capped }
      bounded := fun _ => Nat.le_refl _ }
    related := by
      simpa only [input.typeClosed.instL.subst_eq (σ := input.realization) .zero,
        input.typeClosed.instL.subst_eq (σ := σ) .zero] using headerAnswer.related
    path := .refl
    generation := emptyGenerated.erase.ambientGenerated }
  let incomingData : WorldParameterReplyData (P := P) hc .nil frontier incoming := {
    generation := emptyGenerated, replayable := trivial, controlled := emptyReady,
    compatible := ⟨rfl, rfl⟩, query := headerReady.code, covered := Covered.refl [],
    hereditary := ⟨trivial, .nil, trivial⟩ }
  obtain ⟨changed, ⟨changedData⟩⟩ := RetainedHeaderUniverse.replayCallerWorld controls input.origin
    input.seedWF selection.seedWF seedAssigned (.ref reference) baseline frontier incoming incomingData
    henv hscoped formed below sourceClosed input.certificate.formed paid replay unary
  let left : OriginalNestedDisplay U source assigned
      (.sort (input.origin.familyHeader selection.seedWF).level) :=
    { RetainedHeaderUniverse.display input.origin selection.seedWF source with
      expression_eq := by simpa only [RetainedHeaderUniverse.display, subst_id] using assignedEqual }
  let right := OriginalNestedDisplay.identity sandbox (EndpointState.ref reference).typeFormation.node
    (OriginalNestedDisplay.identity sandbox (.ref reference) provenance).formationDisplay.provenance
  let leftData : WorldCallFrameData (P := P) (base := sandbox) (caps := sandbox.initialCaps)
      (display := left) hc .nil frontier changed.reply.answer.reply.realization := {
    generation := changedData.generation, replayable := changedData.replayable,
    controlled := changedData.controlled, compatible := changedData.compatible,
    closed := changed.reply.answer.reply.closed, capacity := changed.reply.bounded hc.ordered,
    covered := changedData.covered, hereditary := changedData.hereditary }
  let rightData : WorldCallFrameData (P := P) (base := sandbox) (caps := sandbox.initialCaps)
      (display := right) controls baseline frontier sandbox.identityRealization := {
    generation := identity, replayable := trivial, controlled := identityReady,
    compatible := ⟨rfl, rfl⟩, closed := closed,
    capacity := by
      change environmentCost (diagonal.dependencyEnvironment controls.ordered) ≤ _
      simpa only [diagonal, frame.dependencyEnvironment_leftDiagonal] using capacity,
    covered := by simpa only [WorldGenerated.worlds, WorldGenerated.environment, identity,
      WorldUnaryFrameData.generation, frame.diagonalWorld_worlds] using covered,
    hereditary := diagonalData.generation_hereditary substitutions.left }
  have formationLower : WorldBelow strata.rules.length
      (originalCallWorld controls .expressionReindex right.node baseline)
      (originalCallWorld controls .fundamental (.ref reference) baseline) :=
    original_child (richSchedule_strict
      (primitiveConstantFormationCost controls.ordered reference rfl primitive baselineEnvironment) _ _) _ _ _ _ _
  have finalHeaderLower := originalClosedHeader_below controls input.origin left.node
    (.ref reference) baseline .expressionReindex .fundamental
  have pairLower : ∀ child ∈ [originalCallWorld hc .expressionReindex left.node .nil,
      originalCallWorld controls .expressionReindex right.node baseline],
      WorldBelow strata.rules.length child (originalCallWorld controls .fundamental (.ref reference) baseline) := by
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact finalHeaderLower
    · cases List.mem_singleton.mp member; exact formationLower
  have pairPaid := (singletonSponsoredBelow paid finalHeaderLower).merge
    (singletonSponsoredBelow paid formationLower)
  obtain ⟨replayed, ⟨replayedData⟩⟩ := (replay _ (prefixCalls frontier pairLower)).observation
    sandbox sandbox.initialCaps left right σ σ hc controls rfl rfl .nil baseline frontier rfl
    pairPaid changed.reply.answer.reply.realization leftData sandbox.identityRealization rightData
    changed.reply.answer.reply.query.observation changed.reply.answer.reply.query.resources changedData.query
  let adapted := replayed.mapQuery (replayed.answer.reply.query.adaptRequest henv hscoped formed
    changed.reply.answer.reply.query.bound changed.reply.answer.reply.query.adapter)
  obtain ⟨frozenReady⟩ := adapted.answer.freezeBase_controlled replayedData.query
  obtain ⟨footprint, certificate, certificateOutputReady, resources, _⟩ :=
    adapted.answer.freezeBase.code_controlled henv controls frozenReady input.certificate.formed
  let output : RichComputationalValue sourceEnv env U registry target (.ref reference)
      locals σ τ available (.singleton (plan.atom name frozenLevels [])) := {
    support := support, footprint := footprint, certificate := certificate, resources := resources,
    typed := input.typed,
    related := by
      simpa only [assignedEqual, subst_const, input.typeClosed.instL.subst_eq (σ := σ) .zero] using related,
    typeCode := by
      simpa only [assignedEqual, input.typeClosed.instL.subst_eq (σ := σ) .zero] using typeCode,
    rightQuery := {
      rank := n, bound := Nat.le_refl _, raw := .singleton (plan.atom name frozenLevels []),
      footprint := [], observation := input.observation (.ref reference) locals τ,
      adapter := by rw [raiseProfile_self]; exact .refl _,
      resources := (fun _ _ member => nomatch member),
      live := input.ready.live plan name frozenLevels [] } }
  exact ⟨output, ⟨certificateOutputReady⟩,
    ⟨input.observationControlled controls (.ref reference) locals τ certificateReady headerPaid⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
