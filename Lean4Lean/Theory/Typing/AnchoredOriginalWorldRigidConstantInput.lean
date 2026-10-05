import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidSpineInitialization
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldConstantAssignedHeader
import Lean4Lean.Theory.Typing.AnchoredOriginalRigidConstantPrototype

/-! Close the actual backwards rigid spine at its genuine earlier constant
header. The selected certificate and its controlled annotation are retained;
neither an initial observer nor a header interpretation is supplied. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

private theorem primitiveConstantMetadata
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expressionEq : expression = .const name levels)
    (primitive : reference.Primitive)
    (lookup : sourceEnv.constants name = some info) :
    (∀ level ∈ levels, level.WF U) ∧ levels.length = info.uvars := by
  cases reference with
  | left original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl otherWF levelWF actual wf count equiv closed ambient =>
      cases Option.some.inj (actual.symm.trans lookup)
      exact ⟨wf, count⟩
  | right original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl wf count levelWF actual otherWF equiv closed ambient =>
      cases Option.some.inj (actual.symm.trans lookup)
      exact ⟨otherWF, (Lean4Lean.List.Forall₂.length_eq equiv).symm.trans count⟩

/-- Construct the new constant leaf's entire payload from the actual terminal
state of backwards execution. The source predicate is only used for genuine
earlier declaration sources; the final adequacy entry uses `True`. -/
theorem WorldRigidPrimitiveSeed.constantInputOfWorldBanks
    {registry : CanonicalHead.Registry} {target source : List VExpr}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {initial : ContextDerivation sourceEnv U rootSource}
    {controls : OriginalWorldControls strata sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
    {frontier : List (World strata.rules.length)}
    (seed : WorldRigidPrimitiveSeed (registry := registry) (target := target)
      (root := root) (source := source) (P := P) initial controls baseline frontier σ τ name levels)
    (relevant : seed.relevant = true)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (inert : CanonicalDataHead.HeadInert registry name)
    (sourceClosed : ∀ source, source ≤ env → P source)
    (banks : ∀ budget, WorldBoundedReplayAt env U registry strata P budget) :
    ∃ input : RichRigidConstantInput sourceEnv env U registry target name levels levels
        seed.prepared.plan seed.support,
      Nonempty (ControlledStoredQuery (controls.atHeader input.origin) frontier
        (.certificate input.certificate)) := by
  let query := seed.input
  let base := query.frame.captureBase query.substitutions
  let display := OriginalNestedDisplay.ofOccurrence initial seed.location (.identity _)
  let generated := query.frameData.generation query.substitutions
  obtain ⟨ready⟩ := query.frameData.controlled query.substitutions
  let data : WorldCallFrameData (P := P) (base := base) (caps := base.initialCaps)
      (display := display) controls baseline frontier base.identityRealization := {
    generation := generated, replayable := trivial, controlled := ready,
    compatible := ⟨rfl, rfl⟩,
    hereditary := query.frameData.generation_hereditary query.substitutions,
    closed := query.closed, capacity := query.capacity, covered := query.covered }
  have below : sourceEnv ≤ env := generated.erase.ambientGenerated.ambient.1.below
  obtain ⟨selection, origin, answer, ⟨answerData⟩⟩ :=
    constantAssignedHeaderWorld initial (.ref seed.reference) seed.location (.identity _)
      controls baseline frontier base.identityRealization data henv hscoped formed below sourceClosed
      seed.funded banks query.certificate query.resources query.certificateReady
  have sorted : seed.support.HasType (.sort true) := by
    simpa only [relevant] using seed.input.certificate.formed
  obtain ⟨realization, certificate, certificateReady⟩ :=
    answer.closedHeaderCertificateWorld origin selection.seedWF controls frontier answerData henv sorted
  obtain ⟨levelsWF, levelCount⟩ := primitiveConstantMetadata seed.reference rfl seed.primitive selection.lookup
  let input : RichRigidConstantInput sourceEnv env U registry target name levels levels
      seed.prepared.plan seed.support := {
    info := selection.info, origin := origin, lookup := below.constants selection.lookup,
    inert := inert, seed := selection.seed, seedWF := selection.seedWF,
    seedLength := (Lean4Lean.List.Forall₂.length_eq selection.equivalent).trans levelCount,
    frozenWF := levelsWF, levelsWF := levelsWF,
    seedFrozen := selection.equivalent,
    frozenLevelsEq := Lean4Lean.List.Forall₂.rfl (fun _ _ => rfl),
    typeClosed := controls.ordered.closedC selection.lookup,
    realization := realization, certificate := certificate,
    ready := seed.prepared.ready, typed := seed.prepared.typed [] }
  exact ⟨input, certificateReady⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
