import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplyPiSeedHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyApplyPiHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalParameterCaptureStep
import Lean4Lean.Theory.Typing.ProjectionParameterProvenance
import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderWorldCalls

/-! The first formal parameter cell is a real same-expression comparison
between two closed original domains. Its declaration stage pays both calls;
the chosen formal domain is retained verbatim. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private RetainedHeaderUniverse.source_same from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteOperations
open private sameData sameData_coherent same_worlds from Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplyPiSeedHistory
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

noncomputable def firstFamilyCellRoute
    (origin : ProjectionParameterOrigin sourceEnv name info)
    (familyOrigin : ConstantHeaderOrigin sourceEnv name origin.family.toVConstant)
    (wf : ∀ level ∈ levels, level.WF U)
    (shape : origin.family.type.instL levels = .forallE C D)
    (domain : EndpointRef origin.types U [] C (.sort level))
    (common : List VExpr) (env : VEnv) (registry : CanonicalHead.Registry)
    (target : List VExpr) (left right : Subst) :=
  let source := (RetainedHeaderUniverse.nativeSide familyOrigin wf shape common).domainDisplay
  let graph : OriginalCaptureMap (common := common) (ContextDerivation.nil (env := origin.types) (U := U)) .id := .empty common
  let provenance : EndpointProvenance .nil (.ref domain) := .ofLocation .here .nil
  let destination := graph.parameterCellDisplay domain provenance
  let frame := closedTypeRouteFrame (ContextDerivation.nil (env := origin.types) (U := U)) common env registry target left right
  RawGeneratedTypeRoute.same source destination familyOrigin.ordered origin.typesOrdered [] frame

theorem firstFamilyCellWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    (origin : ProjectionParameterOrigin sourceEnv name info)
    (familyOrigin : ConstantHeaderOrigin sourceEnv name origin.family.toVConstant)
    (wf : ∀ level ∈ levels, level.WF U)
    (shape : origin.family.type.instL levels = .forallE C D)
    (domain : EndpointRef origin.types U [] C (.sort level))
    (common : List VExpr) (left right : Subst)
    (controls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length))
    (below : sourceEnv ≤ env) (headerSource : P familyOrigin.source) (typesSource : P origin.types)
    (caller : EndpointState sourceEnv U callerSource callerExpression callerAssigned)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase)
    (paid : Sponsored frontier [originalCallWorld controls phase caller captured]) :
    let route := firstFamilyCellRoute origin familyOrigin wf shape domain common env registry target left right
    ∃ data : route.ControlledWorldData P base caps controls.cutoff controls.fuel frontier,
      ∃ boundary : route.WorldBoundary data.inputs (controls.atHeader familyOrigin)
          (controls.atHeader origin.constructorOrigin) .nil .nil,
        boundary.FrameOccurrenceCoherent data.controls data.frames ∧
        Sponsored frontier (route.worldReserve data.inputs).worlds ∧
        (∀ world ∈ (route.worldReserve data.inputs).worlds,
          WorldBelow strata.rules.length world (originalCallWorld controls phase caller captured)) := by
  dsimp only
  let source := (RetainedHeaderUniverse.nativeSide familyOrigin wf shape common).domainDisplay
  let graph : OriginalCaptureMap (common := common) (ContextDerivation.nil (env := origin.types) (U := U)) .id := .empty common
  let provenance : EndpointProvenance .nil (.ref domain) := .ofLocation .here .nil
  let destination := graph.parameterCellDisplay domain provenance
  let frame := closedTypeRouteFrame (ContextDerivation.nil (env := origin.types) (U := U)) common env registry target left right
  let nextControls := controls.atHeader origin.constructorOrigin
  let generation : WorldGenerated strata P base caps left right graph frame.realization.frame.raw nextControls :=
    .empty common left right (origin.typesBelow.trans below) typesSource nextControls
  have ready : generation.Controlled frontier :=
    ⟨.nil, by intro control active; exact Nat.zero_le _, by intro world member; cases member⟩
  have compatible : generation.UsesControlPrefix controls.cutoff controls.fuel := ⟨rfl, rfl⟩
  have replayable : generation.Replayable := trivial
  let hereditary : generation.Hereditary frontier := ⟨trivial, .nil, trivial⟩
  let route := RawGeneratedTypeRoute.same source destination familyOrigin.ordered origin.typesOrdered [] frame
  have generated : route.SourceGenerated P base caps :=
    RetainedHeaderUniverse.source_same _ _ rfl _ _ _ _ (familyOrigin.sourceBelow.trans below)
      (origin.typesBelow.trans below) headerSource typesSource generation.erase
  let data := sameData source destination familyOrigin.ordered origin.typesOrdered [] frame
    (controls.atHeader familyOrigin) nextControls .nil .nil generation ready compatible replayable hereditary
    (Covered.refl []) generated
  let boundary := RawGeneratedTypeRoute.WorldBoundary.same source destination familyOrigin.ordered origin.typesOrdered frame
    (controls.atHeader familyOrigin) nextControls .nil .nil ⟨rfl, rfl⟩
  have coherent : boundary.FrameOccurrenceCoherent data.controls data.frames :=
    sameData_coherent source destination familyOrigin.ordered origin.typesOrdered [] frame
      (controls.atHeader familyOrigin) nextControls .nil .nil generation ready compatible replayable hereditary
      (Covered.refl []) generated ⟨rfl, rfl⟩
  have worlds : (route.worldReserve data.inputs).worlds =
      [originalCallWorld (controls.atHeader familyOrigin) .expressionReindex source.node .nil,
       originalCallWorld nextControls .expressionReindex (.ref domain) .nil] :=
    same_worlds source destination familyOrigin.ordered origin.typesOrdered [] frame
      (controls.atHeader familyOrigin) nextControls .nil .nil
  have smaller : ∀ world ∈ (route.worldReserve data.inputs).worlds,
      WorldBelow strata.rules.length world (originalCallWorld controls phase caller captured) := by
    intro world member
    rw [worlds] at member
    rcases List.mem_cons.mp member with rfl | member
    · exact originalClosedHeader_below controls familyOrigin source.node caller captured .expressionReindex phase
    · cases List.mem_singleton.mp member
      exact originalClosedHeader_below controls origin.constructorOrigin (.ref domain) caller captured .expressionReindex phase
  refine ⟨data, boundary, coherent, ?_, smaller⟩
  intro world member
  obtain ⟨sponsor, present, lower⟩ := paid _ (List.mem_singleton_self _)
  exact ⟨sponsor, present, EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans
    (smaller world member) lower⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
