import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTwoParameterMajorAttachment
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldUnaryDiagonal
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramApplication

/-! Initialize source-program execution from the SAME selected major-C
reply. Its left diagonal retains hereditary frame data, and its formation
bank is paid by the original outer projection reserve. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private projectionMajor_cost_lt from Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionReindex
open private from_right from Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

section
variable {strata : EquationStratification env} {P : VEnv → Prop}
  {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
  {left : OriginalNestedDisplay U common leftExpression leftAssigned}
  {right : OriginalNestedDisplay U common rightExpression rightAssigned}
  {controls : OriginalWorldControls strata right.sourceEnv}
  {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
  {frontier : List (World strata.rules.length)}
  {profile : Profile n}

noncomputable def WorldTemplateAssignedReply.diagonalFrame
    (answer : WorldTemplateAssignedReply (P := P) base caps left right commonLeft commonRight
      controls baseline frontier profile) :=
  answer.reply.reply.answer.reply.realization.frame.leftDiagonal

noncomputable def WorldTemplateAssignedReply.diagonalCaptured
    (answer : WorldTemplateAssignedReply (P := P) base caps left right commonLeft commonRight
      controls baseline frontier profile) :
    WorldEnvironmentProvenance strata U (answer.diagonalFrame.dependencyEnvironment controls.ordered) :=
  answer.reply.reply.answer.reply.realization.frame.diagonalWorld controls answer.data.generation.environment

/-- Every field refers to the actual selected reply; this package does not
choose a different generation, certificate, or baseline. -/
structure WorldTemplateAssignedReply.FormationInput
    (answer : WorldTemplateAssignedReply (P := P) base caps left right commonLeft commonRight
      controls baseline frontier profile) where
  frameData : WorldUnaryFrameData P controls frontier answer.diagonalFrame answer.diagonalCaptured
  substitutions : Ctx.SubstEq env U target (right.raw.comp commonLeft) (right.raw.comp commonLeft) right.source
  sourceBelow : right.sourceEnv ≤ env
  closed : answer.reply.reply.answer.reply.available.AtomClosed
  paid : Sponsored frontier [originalCallWorld controls .fundamental right.node.typeFormation.node answer.diagonalCaptured]
  bank : WorldBoundedUnaryCallBank env U registry strata P
    (frontier ++ [originalCallWorld controls .fundamental right.node.typeFormation.node answer.diagonalCaptured])

/-- Formation execution follows the exact selected original occurrence. The
root and location remain available to fund later parameter histories. -/
noncomputable def WorldTemplateAssignedReply.FormationInput.provenance
    {answer : WorldTemplateAssignedReply (P := P) base caps left right commonLeft commonRight
      controls baseline frontier profile}
    (_input : answer.FormationInput) : EndpointProvenance right.context right.node.typeFormation.node :=
  right.formationDisplay.provenance

/-- The actual comparison certificate becomes the retained program without
reselection. The demand may target arbitrary operands; no variable shape is
asserted by this initializer. -/
noncomputable def WorldTemplateAssignedReply.FormationInput.programState
    {answer : WorldTemplateAssignedReply (P := P) base caps left right commonLeft commonRight
      controls baseline frontier profile}
    (input : answer.FormationInput)
    (code : TemplateAssignedResult env U registry target left.node right.node
      answer.reply.reply.answer.reply.locals (left.raw.comp commonLeft) (right.raw.comp commonLeft)
      answer.reply.reply.answer.reply.available relevant profile)
    (ready : ControlledStoredQuery controls frontier (.certificate code.certificate))
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput
      right.sourceType atom) (member : atom ∈ profile.atoms) :
    RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput :=
  RetainedProgramState.ofRich ready input.provenance answer.diagonalFrame answer.diagonalCaptured
    input.frameData input.closed input.substitutions code.resources input.sourceBelow input.paid input.bank
    demand member

/-- A literal application entry at the actual assigned type, including
arbitrary original parameter terms. Only the syntactic display is cast. -/
noncomputable def WorldTemplateAssignedReply.FormationInput.applicationState
    {answer : WorldTemplateAssignedReply (P := P) base caps left right commonLeft commonRight
      controls baseline frontier profile}
    (input : answer.FormationInput)
    (code : TemplateAssignedResult env U registry target left.node right.node
      answer.reply.reply.answer.reply.locals (left.raw.comp commonLeft) (right.raw.comp commonLeft)
      answer.reply.reply.answer.reply.available relevant profile)
    (ready : ControlledStoredQuery controls frontier (.certificate code.certificate))
    (expressionEq : right.sourceType = .app goalFunction goalArgument)
    (member : goalOutput ∈ profile.atoms) :
    RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput :=
  input.programState code ready (expressionEq.symm ▸ .application) member

end

/-- The formation of the selected proper major is strictly below the outer
projection even when C changed the captured frame. Capacity and coverage are
read from that SAME C reply, and all sponsors are inherited unchanged. -/
theorem WorldTemplateAssignedReply.initializeProjectionMajor
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {leftDisplay : OriginalNestedDisplay U common leftExpression leftAssigned}
    {rightNode : EndpointState rightEnv U rightSource (.proj name index rightValue) rightAssigned}
    (rightHead : ProjectionHead rightNode)
    {rightContext : ContextDerivation rightEnv U rightSource}
    (rightGraph : OriginalCaptureMap (common := common) rightContext rightRaw)
    (displayedEq : displayed = rightValue.subst rightRaw)
    (controls : OriginalWorldControls strata rightEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (answer : WorldTemplateAssignedReply (P := P) base caps leftDisplay
      (OriginalNestedDisplay.recordBridgeReference rightGraph (.right rightHead.major) displayedEq)
      commonLeft commonRight controls baseline frontier (profile : Profile n))
    {leftEnv : VEnv} {leftSource : List VExpr} {leftExpression leftAssigned : VExpr}
    (leftNode : EndpointState leftEnv U leftSource leftExpression leftAssigned)
    (leftControls : OriginalWorldControls strata leftEnv)
    (leftWorld : WorldEnvironmentProvenance strata U leftEnvironment)
    (paid : Sponsored frontier [originalCallWorld leftControls .assignedComparison leftNode leftWorld,
      originalCallWorld controls .assignedComparison rightNode baseline])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld leftControls .assignedComparison leftNode leftWorld,
        originalCallWorld controls .assignedComparison rightNode baseline])) :
    Nonempty answer.FormationInput := by
  let selected := answer.reply.reply.answer.reply
  obtain ⟨data⟩ := WorldUnaryFrameData.ofGenerated selected.realization.frame
    answer.data.generation answer.data.controlled answer.data.replayable answer.data.compatible answer.data.hereditary
  have capacity : environmentCost (answer.diagonalFrame.dependencyEnvironment controls.ordered) ≤
      environmentCost baselineEnvironment := by
    simpa only [WorldTemplateAssignedReply.diagonalFrame,
      OriginalRichFrame.dependencyEnvironment_leftDiagonal] using answer.reply.reply.bounded controls.ordered
  have covered : Covered (@EquationControlMeasure.Less strata.rules.length)
      answer.diagonalCaptured.worlds baseline.worlds := by
    simpa only [WorldTemplateAssignedReply.diagonalCaptured,
      OriginalRichFrame.diagonalWorld_worlds, WorldGenerated.worlds] using answer.data.covered
  have proper : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental (EndpointState.ref (.right rightHead.major)).typeFormation.node answer.diagonalCaptured)
      (originalCallWorld controls .assignedComparison rightNode baseline) := by
    apply originalCallWorld_retargetBelow controls rightNode .assignedComparison
      answer.diagonalCaptured baseline capacity covered
    exact original_child (richSchedule_strict
      (Nat.lt_of_le_of_lt
        ((EndpointState.ref (.right rightHead.major)).typeFormation_dependency_cost_le controls.ordered _)
        (projectionMajor_cost_lt rightHead controls.ordered _)) _ _) _ _ _ _ _
  have smaller : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental
        (EndpointState.ref (.right rightHead.major)).typeFormation.node answer.diagonalCaptured])
      (frontier ++ [originalCallWorld leftControls .assignedComparison leftNode leftWorld,
        originalCallWorld controls .assignedComparison rightNode baseline]) := by
    have selectedBelow := from_right (calls := [originalCallWorld controls .fundamental
      (EndpointState.ref (.right rightHead.major)).typeFormation.node answer.diagonalCaptured])
      (parent := originalCallWorld leftControls .assignedComparison leftNode leftWorld)
      (by intro child member; cases List.mem_singleton.mp member; exact proper)
    have inherited : ∀ extra : List (World strata.rules.length),
        CallBelow strata.rules.length
          (extra ++ [originalCallWorld controls .fundamental
            (EndpointState.ref (.right rightHead.major)).typeFormation.node answer.diagonalCaptured])
          (extra ++ [originalCallWorld leftControls .assignedComparison leftNode leftWorld,
            originalCallWorld controls .assignedComparison rightNode baseline]) := by
      intro extra
      induction extra with
      | nil => exact selectedBelow
      | cons world rest ih => exact ih.cons world
    exact inherited frontier
  refine ⟨⟨data.leftDiagonal, selected.realization.substitutions.left,
    answer.data.generation.erase.ambientGenerated.ambient.1.below, selected.closed, ?_, ?_⟩⟩
  · intro child member
    cases List.mem_singleton.mp member
    obtain ⟨sponsor, present, below⟩ := paid _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans proper below⟩
  · intro retained below
    exact bank retained (below.trans smaller)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
