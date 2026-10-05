import Lean4Lean.Theory.Typing.AnchoredOriginalWorldParameterComparison
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldEqualityReplay

/-! Typed normalization at an arbitrary original assigned type. The empty
assigned comparison supplies an unconditional type path; the full query is
transported separately. Every selected frame and replay history is retained. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem lower_pair_frontier
    {count : Nat} {first second left right : World count}
    (firstLower : WorldBelow count first left)
    (secondLower : WorldBelow count second right)
    (frontier : List (World count)) :
    CallBelow count (frontier ++ [first, second]) (frontier ++ [left, right]) := by
  have head : CallBelow count [first, second] [left, second] :=
    .single (.head (tail := [second]) (replacement := [first]) (by
      intro node member
      cases List.mem_singleton.mp member
      exact firstLower))
  have tail : CallBelow count [left, second] [left, right] :=
    (EquationWorldPolynomial.lower_mass (mass := [second]) (by
      intro node member
      cases List.mem_singleton.mp member
      exact secondLower)).cons left
  have pair := head.trans tail
  induction frontier with
  | nil => exact pair
  | cons head rest ih => exact ih.cons head

theorem AmbientBoundedParameterReply.typedEqualityStepWorld
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target common : List VExpr}
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {commonLeft commonRight : Subst} {start : VExpr}
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (original : Derivation sourceEnv U source A B assigned)
    (left : OriginalNestedDisplay U common (A.subst raw) (.sort level))
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    {strata : EquationStratification env} {P : VEnv → Prop}
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (controls : OriginalWorldControls strata sourceEnv)
    (sameCutoff : leftControls.cutoff = controls.cutoff)
    (sameFuel : leftControls.fuel = controls.fuel)
    (leftWorld : WorldEnvironmentProvenance strata U initialEnvironment)
    (rightWorld : WorldEnvironmentProvenance strata U finalEnvironment)
    (frontier parent : List (World strata.rules.length))
    (answer : AmbientBoundedParameterReply base commonCaps start left commonLeft commonRight
      (profile : Profile n) (environmentCost initialEnvironment))
    (answerData : WorldParameterReplyData (P := P) leftControls leftWorld frontier answer)
    (sorted : profile.HasType (.sort true))
    (frame : OriginalCaptureRealization graph env registry target rightLocals
      commonLeft commonRight rightAvailable)
    (frameData : WorldCallFrameData (P := P) (base := base) (caps := commonCaps)
      (display := graph.typeEqualityDisplay original true) controls rightWorld frontier frame)
    (reindexSponsored : Sponsored frontier
      [originalCallWorld leftControls .expressionReindex left.node leftWorld,
       originalCallWorld controls .expressionReindex (.ref (.left original)) rightWorld])
    (reindexSmaller : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld leftControls .expressionReindex left.node leftWorld,
       originalCallWorld controls .expressionReindex (.ref (.left original)) rightWorld]) parent)
    (equalitySponsored : Sponsored frontier
      [originalCallWorld controls .fundamental (.ref (.left original)) rightWorld])
    (equalitySmaller : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental (.ref (.left original)) rightWorld]) parent)
    (bank : WorldBoundedCallBank env U registry strata P parent)
    (unary : WorldBoundedUnaryCallBank env U registry strata P parent) :
    ∃ result : AmbientBoundedParameterReply base commonCaps start
        (graph.typeEqualityDisplay original false) commonLeft commonRight profile
        (environmentCost finalEnvironment),
      Nonempty (WorldParameterReplyData (P := P) controls rightWorld frontier result) := by
  have leftLower : WorldBelow strata.rules.length
      (originalCallWorld leftControls .assignedComparison left.node leftWorld)
      (originalCallWorld leftControls .expressionReindex left.node leftWorld) := by
    apply original_child
    simp only [richSchedule, RichPhase.code]
    omega
  have rightLower : WorldBelow strata.rules.length
      (originalCallWorld controls .assignedComparison (.ref (.left original)) rightWorld)
      (originalCallWorld controls .expressionReindex (.ref (.left original)) rightWorld) := by
    apply original_child
    simp only [richSchedule, RichPhase.code]
    omega
  have compareSmaller := (lower_pair_frontier leftLower rightLower frontier).trans reindexSmaller
  have compareSponsored : Sponsored frontier
      [originalCallWorld leftControls .assignedComparison left.node leftWorld,
       originalCallWorld controls .assignedComparison (.ref (.left original)) rightWorld] := by
    intro world member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨sponsor, present, bound⟩ := reindexSponsored _ List.mem_cons_self
      exact ⟨sponsor, present, EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans leftLower bound⟩
    · cases List.mem_singleton.mp member
      obtain ⟨sponsor, present, bound⟩ := reindexSponsored _ (List.mem_cons_of_mem _ List.mem_cons_self)
      exact ⟨sponsor, present, EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans rightLower bound⟩
  let prior := answer.reply.answer.reply
  let empty : RichCert left.sourceEnv env U registry target left.node.typeFormation.node
      prior.locals (left.raw.comp commonLeft) true (Profile.empty : Profile 0) [] :=
    .legacy (.seed .empty (.empty (.sort true)))
  have emptyReady : ControlledStoredQuery leftControls frontier (.certificate empty) := {
    annotation := .legacy _ (.seed _ _ .empty)
    within := by
      intro control active
      change empty.headDepth _ ≤ _
      simp only [empty, RichCert.headDepth, SortableCert.headDepth, Obs.headDepth]
      omega
    sponsored := by intro child member; cases member }
  obtain ⟨typeChanged, _⟩ := (bank _ compareSmaller).assigned base commonCaps left
    (graph.typeEqualityDisplay original true) commonLeft commonRight leftControls controls
    sameCutoff sameFuel leftWorld rightWorld frontier rfl compareSponsored
    prior.realization answerData.callFrame frame frameData empty
    (by intro _ _ member; cases member) emptyReady
  have typePath : TypeConversion env U target (.sort level) (assigned.subst (raw.comp commonLeft)) := by
    simpa only [OriginalNestedDisplay.formationDisplay, OriginalCaptureMap.typeEqualityDisplay,
      subst_subst, subst] using typeChanged.path
  obtain ⟨input, ⟨inputData⟩⟩ := answer.reindexAtWorld (right := graph.typeEqualityDisplay original true)
    henv leftControls controls sameCutoff sameFuel leftWorld rightWorld frontier parent answerData
    sorted frame frameData reindexSponsored reindexSmaller bank
  let selected := input.reply.answer.reply
  obtain ⟨footprint, certificate, ready, resources, _⟩ :=
    selected.query.code_controlled henv controls inputData.query sorted
  obtain ⟨unaryFrame⟩ := WorldUnaryFrameData.ofGenerated selected.realization.frame
    inputData.generation inputData.controlled
    inputData.replayable inputData.compatible inputData.hereditary
  let diagonal := selected.realization.frame.leftDiagonal
  let captured := selected.realization.frame.diagonalWorld controls inputData.generation.environment
  have capacity : environmentCost (diagonal.dependencyEnvironment controls.ordered) ≤
      environmentCost finalEnvironment := by
    simpa only [diagonal, OriginalRichFrame.dependencyEnvironment_leftDiagonal]
      using input.reply.bounded controls.ordered
  have covered : Covered (@EquationControlMeasure.Less strata.rules.length)
      captured.worlds rightWorld.worlds := by
    simpa only [captured, OriginalRichFrame.diagonalWorld_worlds, WorldGenerated.worlds]
      using inputData.covered
  obtain ⟨changed, ⟨changedReady⟩⟩ := (unary _ equalitySmaller).equality original true
    (.ofLocation .here context) controls diagonal captured rightWorld frontier capacity covered
    rfl equalitySponsored unaryFrame.leftDiagonal selected.closed formed
    selected.realization.substitutions.left (.code certificate) resources ready.code
  obtain ⟨outFootprint, outCertificate, outReady, outResources, _⟩ :=
    changed.rightQuery.code_controlled henv controls changedReady sorted
  let query : RichGradedResult sourceEnv env U registry target (.ref (.right original))
      selected.locals (raw.comp commonLeft) selected.available profile := {
    rank := n, bound := Nat.le_refl _, raw := profile
    footprint := outFootprint, observation := .code outCertificate
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := outResources
    live := Profile.HasType.sortable_live sorted }
  have related : TypeRelated env U registry target (A.subst (raw.comp commonLeft))
      (B.subst (raw.comp commonLeft)) profile :=
    changed.related.code_of_sortable henv hscoped formed sorted
  have rawEquality := (original.forget.defeq.mono input.ambient.below).substDF henv
    selected.realization.substitutions.left.wf formed selected.realization.substitutions.left
  have path := TypeConversion.single (typePath.symm.cast rawEquality)
  let result : AmbientBoundedParameterReply base commonCaps start
      (graph.typeEqualityDisplay original false) commonLeft commonRight profile
      (environmentCost finalEnvironment) := {
    reply := {
      answer := {
        reply := { selected with query := query }
        capped := input.reply.answer.capped }
      bounded := input.reply.bounded }
    related := input.related.trans henv (by
      simpa only [OriginalCaptureMap.typeEqualityDisplay, Bool.false_eq_true, reduceIte, subst_subst] using related)
    path := input.path.trans (by
      simpa only [OriginalCaptureMap.typeEqualityDisplay, Bool.false_eq_true, reduceIte, subst_subst] using path)
    generation := input.generation }
  exact ⟨result, ⟨{
    generation := inputData.generation
    hereditary := inputData.hereditary
    replayable := inputData.replayable
    controlled := inputData.controlled
    compatible := inputData.compatible
    query := outReady.code
    covered := inputData.covered }⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
