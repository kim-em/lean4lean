import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyApplyPiChain
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteExecutionFrames

/-! The next native header uses the same selected frame, transported only
along the actual original context equality exposed by its Pi prefix. Dormant
histories, query controls and world annotations are retained together. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private routeFrame_recontext routeFrame_recontext_environment piPrefix_context from
  Lean4Lean.Theory.Typing.AnchoredOriginalFamilyApplyPiChain
open private transportWorld transportWorld_worlds from
  Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyApplyPiWorldHistory
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private noncomputable def recontextExecution
    {strata : EquationStratification env} {P : VEnv → Prop}
    {frontier : List (World strata.rules.length)} {base : OriginalCaptureBase env U registry target}
    {first second : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) first raw}
    (equal : first = second)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (controls : OriginalWorldControls strata sourceEnv)
    (world : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment controls.ordered))
    (data : WorldBoundaryFrame.ExecutionData P base caps frontier ⟨frame.box, controls, world⟩) :
    WorldBoundaryFrame.ExecutionData P base caps frontier
      ⟨(routeFrame_recontext equal frame).box, controls,
        transportWorld (routeFrame_recontext_environment equal frame controls.ordered).symm world⟩ := by
  cases equal
  exact data

private theorem recontextExecution_environment
    {strata : EquationStratification env} {P : VEnv → Prop}
    {frontier : List (World strata.rules.length)} {base : OriginalCaptureBase env U registry target}
    {first second : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) first raw}
    (equal : first = second)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (controls : OriginalWorldControls strata sourceEnv)
    (world : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment controls.ordered))
    (data : WorldBoundaryFrame.ExecutionData P base caps frontier ⟨frame.box, controls, world⟩) :
    HEq (recontextExecution equal frame controls world data).generation.environment data.generation.environment := by
  cases equal
  rfl

noncomputable def nativeHeaderFrameExecution
    {strata : EquationStratification env} {P : VEnv → Prop}
    {frontier : List (World strata.rules.length)} {base : OriginalCaptureBase env U registry target}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (start : Located root node)
    (graph : OriginalCaptureMap (common := common) (start.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (controls : OriginalWorldControls strata sourceEnv)
    (world : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment controls.ordered))
    (data : WorldBoundaryFrame.ExecutionData P base caps frontier ⟨frame.box, controls, world⟩) :
    WorldBoundaryFrame.ExecutionData P base caps frontier
      ⟨(nativeHeaderFrame initial start graph frame).box, controls,
        transportWorld (nativeHeaderFrame_environment initial start graph frame controls.ordered).symm world⟩ :=
  recontextExecution (piPrefix_context (piPrefix start) initial).symm frame controls world data

theorem nativeHeaderFrameExecution_environment
    {strata : EquationStratification env} {P : VEnv → Prop}
    {frontier : List (World strata.rules.length)} {base : OriginalCaptureBase env U registry target}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (start : Located root node)
    (graph : OriginalCaptureMap (common := common) (start.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (controls : OriginalWorldControls strata sourceEnv)
    (world : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment controls.ordered))
    (data : WorldBoundaryFrame.ExecutionData P base caps frontier ⟨frame.box, controls, world⟩) :
    HEq (nativeHeaderFrameExecution initial start graph frame controls world data).generation.environment
      data.generation.environment :=
  recontextExecution_environment (piPrefix_context (piPrefix start) initial).symm frame controls world data

noncomputable def nativeHeaderWorldExecution
    {strata : EquationStratification env} {P : VEnv → Prop}
    {frontier : List (World strata.rules.length)} {base : OriginalCaptureBase env U registry target}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (start : Located root node)
    (graph : OriginalCaptureMap (common := common) (start.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (controls : OriginalWorldControls strata sourceEnv)
    (world : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment controls.ordered))
    (data : WorldBoundaryFrame.ExecutionData P base caps frontier ⟨frame.box, controls, world⟩) :
    (nativeHeaderWorldInputs_boundary initial start graph frame controls world).ExecutionFrames P base caps frontier := by
  intro occurrence member
  change occurrence ∈ [⟨(nativeHeaderFrame initial start graph frame).box, controls,
    transportWorld (nativeHeaderFrame_environment initial start graph frame controls.ordered).symm world⟩] at member
  cases List.mem_singleton.mp member
  exact nativeHeaderFrameExecution initial start graph frame controls world data

/-- The operative cursor exposes the actual next original Pi and carries its
selected positive generation through the exact context transport. -/
theorem OriginalNestedDisplay.nativePiCursorWorldExecution
    {sourceEnv : VEnv} {strata : EquationStratification env} {P : VEnv → Prop}
    {frontier : List (World strata.rules.length)} {base : OriginalCaptureBase env U registry target}
    (controls : OriginalWorldControls strata sourceEnv)
    (origin : ConstantHeaderOrigin sourceEnv familyName familyInfo)
    (caller : EndpointState sourceEnv U callerSource callerExpression callerType)
    (callerCaptured : WorldEnvironmentProvenance strata U callerEnvironment)
    (display : OriginalNestedDisplay U common expression assigned)
    (sourceEqual : display.sourceEnv = origin.source)
    (shape : display.sourceExpression = .forallE A B)
    (ordered : display.sourceEnv.Ordered)
    (frame : OriginalTypeRouteFrame env registry target display.graph commonLeft commonRight)
    (world : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment ordered))
    (data : WorldBoundaryFrame.ExecutionData P base caps frontier
      ⟨frame.box, (show OriginalWorldControls strata display.sourceEnv from
        sourceEqual.symm ▸ controls.atHeader origin), world⟩)
    (inherited : Sponsored [originalCallWorld controls .assignedComparison caller callerCaptured] world.worlds) :
    ∃ side : OriginalPiTypeRouteSide U common,
      ∃ sideOrdered : side.sourceEnv.Ordered,
      ∃ nextFrame : OriginalTypeRouteFrame env registry target side.graph commonLeft commonRight,
      ∃ route : RawGeneratedTypeRoute env registry target commonLeft commonRight display side.display
          (frame.realization.frame.dependencyEnvironment ordered)
          (nextFrame.realization.frame.dependencyEnvironment sideOrdered),
        route.AmbientGenerated base caps ∧
        side.sourceEnv = display.sourceEnv ∧
        side.A = A ∧ side.B = B ∧ side.raw = display.raw ∧
        nextFrame.realization.frame.dependencyEnvironment sideOrdered = frame.realization.frame.dependencyEnvironment ordered ∧
        (∃ domain : EndpointRef side.sourceEnv U side.source side.A (.sort side.u), side.domain = .ref domain) ∧
        ∃ nextWorld : WorldEnvironmentProvenance strata U (nextFrame.realization.frame.dependencyEnvironment sideOrdered),
          nextWorld.worlds = world.worlds ∧
          ∃ inputs : route.WorldInputs strata,
            Sponsored [originalCallWorld controls .assignedComparison caller callerCaptured] (route.worldReserve inputs).worlds ∧
            ∃ nextControls : OriginalWorldControls strata side.sourceEnv,
            ∃ boundary : route.WorldBoundary inputs (sourceEqual.symm ▸ controls.atHeader origin)
                nextControls world nextWorld,
              Nonempty (boundary.ExecutionFrames P base caps frontier) ∧
              ∃ nextData : WorldBoundaryFrame.ExecutionData P base caps frontier ⟨nextFrame.box, nextControls, nextWorld⟩,
                HEq nextData.generation.environment data.generation.environment := by
  rcases display with ⟨headerEnv, source, sourceExpression, sourceType, context, node,
    provenance, raw, graph, expressionEq, typeEq⟩
  dsimp only at sourceEqual shape ordered frame world data inherited ⊢
  subst headerEnv
  subst sourceExpression
  cases expressionEq
  cases typeEq
  rcases provenance with ⟨rootSource, rootExpression, rootType, root, initial, start, contextEq⟩
  cases contextEq
  let side := nativeHeaderSide initial start graph
  let nextFrame := nativeHeaderFrame initial start graph frame
  let nextWorld := transportWorld (nativeHeaderFrame_environment initial start graph frame ordered).symm world
  refine ⟨side, ordered, nextFrame, nativeHeaderRoute initial start graph frame ordered,
    nativeHeaderRoute_ambientGenerated initial start graph frame ordered data.generation.erase.ambientGenerated,
    rfl, rfl, rfl, rfl, nativeHeaderFrame_environment initial start graph frame ordered,
    (piPrefix start).view.location.originalDomains.1, nextWorld, transportWorld_worlds _ world,
    nativeHeaderWorldInputs initial start graph frame (controls.atHeader origin) world, ?_,
    controls.atHeader origin, nativeHeaderWorldInputs_boundary initial start graph frame (controls.atHeader origin) world,
    ⟨nativeHeaderWorldExecution initial start graph frame (controls.atHeader origin) world data⟩,
    nativeHeaderFrameExecution initial start graph frame (controls.atHeader origin) world data,
    nativeHeaderFrameExecution_environment initial start graph frame (controls.atHeader origin) world data⟩
  rw [nativeHeaderWorldInputs_worlds]
  intro child member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨_, List.mem_singleton_self _, originalRetainedHeader_below controls origin node world
      caller callerCaptured _ _ inherited⟩
  · cases List.mem_singleton.mp member
    exact ⟨_, List.mem_singleton_self _, originalRetainedHeader_below controls origin side.display.node world
      caller callerCaptured _ _ inherited⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
