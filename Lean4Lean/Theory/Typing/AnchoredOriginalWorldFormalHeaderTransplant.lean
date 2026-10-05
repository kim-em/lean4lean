import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFormalFamilyDestination
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplyPiSeedHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyApplyPiHistory

/-! Move the whole literal family header to its installed-types stage before
capturing parameters. Both domain originals are those of the formal endpoint,
so the ordinary successor history stays in one declaration context. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private RetainedHeaderUniverse.source_same trans_worldInputs trans_worldReserve from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteOperations
open private sameData sameData_coherent same_worlds transData transData_coherent from Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplyPiSeedHistory
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

/-- This appends an actual same-expression R edge; it neither supplies a
header relation nor changes the already selected caller source frame. -/
theorem FormalFamilyDestination.transplantFirstHistoryWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {levels : List VLevel} {C D : VExpr}
    (origin : ProjectionParameterOrigin sourceEnv name info)
    {signature : ConstantTelescope (origin.family.type.instL levels)}
    {domains : signature.domains = [C,D]}
    (destination : FormalFamilyDestination (U := U) origin signature domains)
    (familyOrigin : ConstantHeaderOrigin sourceEnv name origin.family.toVConstant)
    (wf : ∀ level ∈ levels, level.WF U)
    (shape : origin.family.type.instL levels = .forallE C (.forallE D signature.result))
    (common : List VExpr) (commonLeft commonRight : Subst)
    (left : OriginalApplicationTypeRouteSide U common)
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left
      (RetainedHeaderUniverse.nativeSide familyOrigin wf shape common))
    (controls : OriginalWorldControls strata sourceEnv)
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (frontier : List (World strata.rules.length))
    (sourceWorld : WorldEnvironmentProvenance strata U
      (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered))
    (headerWorld : WorldEnvironmentProvenance strata U history.final)
    (headerEmpty : headerWorld.worlds = [])
    (whole : history.whole.ControlledWorldData P base caps controls.cutoff controls.fuel frontier)
    (wholeBoundary : history.whole.WorldBoundary whole.inputs leftControls (controls.atHeader familyOrigin)
      sourceWorld headerWorld)
    (wholeCoherent : wholeBoundary.FrameOccurrenceCoherent whole.controls whole.frames)
    (below : sourceEnv ≤ env) (headerSource : P familyOrigin.source) (typesSource : P origin.types)
    (caller : EndpointState sourceEnv U callerSource callerExpression callerAssigned)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase)
    (wholePaid : Sponsored [originalCallWorld controls phase caller captured]
      (history.whole.worldReserve whole.inputs).worlds) :
    ∃ next : OriginalApplyPiHistory env registry target commonLeft commonRight left (destination.nativeSide common),
      ∃ sourceEq : next.sourceFrame = history.sourceFrame, next.rightDomain = destination.firstDomain ∧
      next.headerFrame = closedTypeRouteFrame (ContextDerivation.nil (env := origin.types) (U := U))
        common env registry target commonLeft commonRight ∧
      ∃ finalWorld : WorldEnvironmentProvenance strata U next.final,
        finalWorld.worlds = [] ∧
        ∃ data : next.whole.ControlledWorldData P base caps controls.cutoff controls.fuel frontier,
          ∃ boundary : next.whole.WorldBoundary data.inputs leftControls (controls.atHeader origin.constructorOrigin)
              ((congrArg (fun f => f.realization.frame.dependencyEnvironment next.leftOrdered) sourceEq).symm ▸ sourceWorld) finalWorld,
            boundary.FrameOccurrenceCoherent data.controls data.frames ∧
            Sponsored [originalCallWorld controls phase caller captured] (next.whole.worldReserve data.inputs).worlds := by
  let oldSide := RetainedHeaderUniverse.nativeSide familyOrigin wf shape common
  let nextSide := destination.nativeSide common
  let frame := closedTypeRouteFrame (ContextDerivation.nil (env := origin.types) (U := U)) common env registry target commonLeft commonRight
  let nextControls := controls.atHeader origin.constructorOrigin
  let generation : WorldGenerated strata P base caps commonLeft commonRight nextSide.graph
      frame.realization.frame.raw nextControls :=
    .empty common commonLeft commonRight (origin.typesBelow.trans below) typesSource nextControls
  have ready : generation.Controlled frontier :=
    ⟨.nil, by intro control active; exact Nat.zero_le _, by intro world member; cases member⟩
  have compatible : generation.UsesControlPrefix controls.cutoff controls.fuel := ⟨rfl, rfl⟩
  have replayable : generation.Replayable := trivial
  let hereditary : generation.Hereditary frontier := ⟨trivial, .nil, trivial⟩
  let bridge := RawGeneratedTypeRoute.same oldSide.display nextSide.display
    familyOrigin.ordered origin.typesOrdered history.final frame
  have generated : bridge.SourceGenerated P base caps :=
    RetainedHeaderUniverse.source_same _ _ rfl _ _ _ _ (familyOrigin.sourceBelow.trans below)
      (origin.typesBelow.trans below) headerSource typesSource generation.erase
  let bridgeData := sameData oldSide.display nextSide.display familyOrigin.ordered origin.typesOrdered history.final frame
    (controls.atHeader familyOrigin) nextControls headerWorld .nil generation ready compatible replayable hereditary
    (Covered.refl []) generated
  let bridgeBoundary := RawGeneratedTypeRoute.WorldBoundary.same oldSide.display nextSide.display
    familyOrigin.ordered origin.typesOrdered frame (controls.atHeader familyOrigin) nextControls
    headerWorld .nil ⟨rfl,rfl⟩
  have bridgeCoherent : bridgeBoundary.FrameOccurrenceCoherent bridgeData.controls bridgeData.frames :=
    sameData_coherent oldSide.display nextSide.display familyOrigin.ordered origin.typesOrdered history.final frame
      (controls.atHeader familyOrigin) nextControls headerWorld .nil generation ready compatible replayable hereditary
      (Covered.refl []) generated ⟨rfl,rfl⟩
  let combined := history.whole.trans bridge
  let data := transData whole bridgeData
  let boundary := wholeBoundary.trans bridgeBoundary
  have coherent : boundary.FrameOccurrenceCoherent data.controls data.frames :=
    transData_coherent whole bridgeData _ _ wholeCoherent bridgeCoherent
  let next : OriginalApplyPiHistory env registry target commonLeft commonRight left nextSide :=
    ⟨history.leftOrdered, origin.typesOrdered, history.leftBelow, destination.firstDomain, rfl,
      history.sourceFrame, frame, combined⟩
  have bridgeWorlds : (bridge.worldReserve bridgeData.inputs).worlds =
      [originalCallWorld (controls.atHeader familyOrigin) .expressionReindex oldSide.display.node headerWorld,
       originalCallWorld nextControls .expressionReindex nextSide.display.node .nil] :=
    same_worlds oldSide.display nextSide.display familyOrigin.ordered origin.typesOrdered history.final frame
      (controls.atHeader familyOrigin) nextControls headerWorld .nil
  have bridgePaid : Sponsored [originalCallWorld controls phase caller captured]
      (bridge.worldReserve bridgeData.inputs).worlds := by
    intro world member
    rw [bridgeWorlds] at member
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rcases List.mem_cons.mp member with rfl | member
    · apply Below.root (EquationControlMeasure.constantsDecrease (familyOrigin.count_lt controls.ordered) _ _ _ _ _)
      intro child present
      change child ∈ headerWorld.worlds at present
      rw [headerEmpty] at present
      cases present
    · cases List.mem_singleton.mp member
      exact originalClosedHeader_below controls origin.constructorOrigin nextSide.display.node caller captured .expressionReindex phase
  refine ⟨next, rfl, rfl, rfl, .nil, rfl, data, boundary, coherent, ?_⟩
  change Sponsored _ ((history.whole.trans bridge).worldReserve
    (trans_worldInputs whole.inputs bridgeData.inputs)).worlds
  rw [trans_worldReserve]
  exact wholePaid.merge bridgePaid

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
