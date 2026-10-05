import Lean4Lean.Theory.Typing.AnchoredOriginalDeltaAssignedOrigin
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyNormalizationRoute

/-! A delta support returns to the caller through two distinct original
comparisons. The first compares identical assigned-type expressions; the
second compares identical displayed constants, without identifying their
assigned types. Both endpoints are fixed before the body interpretation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles OriginalClosureMeasure OriginalEndpointFactor
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable def deltaBodyDisplay
    (origin : DefinitionDeclarationOrigin env declarations value)
    (seedWF : ∀ level ∈ seedLevels, level.WF U) (common : List VExpr) :
    OriginalNestedDisplay U common (value.value.instL seedLevels) (value.type.instL seedLevels) where
  sourceEnv := origin.stage.header
  source := []
  sourceExpression := value.value.instL seedLevels
  sourceType := value.type.instL seedLevels
  context := .nil
  node := .ref (.left (DefinitionDeclarationOrigin.instantiatedBody origin seedWF))
  provenance := .ofLocation .here .nil
  raw := .id
  graph := .empty common
  expression_eq := subst_id.symm
  type_eq := subst_id.symm

noncomputable def deltaConstantDisplay
    (packet : ClosedPrimitiveConstant sourceEnv U name levels assigned)
    (common : List VExpr) : OriginalNestedDisplay U common (.const name levels) assigned where
  sourceEnv := sourceEnv
  source := []
  sourceExpression := .const name levels
  sourceType := packet.info.type.instL packet.assignedLevels
  context := .nil
  node := .ref packet.site
  provenance := .ofLocation .here .nil
  raw := .id
  graph := .empty common
  expression_eq := subst_id.symm
  type_eq := packet.assignedEq.trans subst_id.symm

/-- These are actual finite R then C edges, not a supplied compatibility map.
The independent caller frame is retained exactly. In particular the first
comparison is between type formations, while the second compares the terms. -/
noncomputable def deltaAssignedTypeRoute
    (origin : DefinitionDeclarationOrigin env declarations value)
    (seedWF : ∀ level ∈ seedLevels, level.WF U)
    (packet : ClosedPrimitiveConstant origin.stage.header U value.name levels
      (value.type.instL seedLevels))
    (caller : OriginalNestedDisplay U common (.const value.name levels) assigned)
    (ordered : caller.sourceEnv.Ordered)
    (frame : OriginalTypeRouteFrame env registry target caller.graph commonLeft commonRight) :
    RawGeneratedTypeRoute env registry target commonLeft commonRight
      (deltaBodyDisplay origin seedWF common).formationDisplay caller.formationDisplay []
      (frame.realization.frame.dependencyEnvironment ordered) :=
  .trans
    (.same (deltaBodyDisplay origin seedWF common).formationDisplay
      (deltaConstantDisplay packet common).formationDisplay
      origin.headerWF.ordered origin.headerWF.ordered []
      (closedTypeRouteFrame .nil common env registry target commonLeft commonRight))
    (.assigned (deltaConstantDisplay packet common) caller origin.headerWF.ordered ordered [] frame)

/-- The intermediate original is generated from the origin itself; the only
nonempty resource frame in this history is the actual caller's frame. -/
theorem deltaAssignedTypeRoute_generated
    (origin : DefinitionDeclarationOrigin env declarations value)
    (seedWF : ∀ level ∈ seedLevels, level.WF U)
    (packet : ClosedPrimitiveConstant origin.stage.header U value.name levels
      (value.type.instL seedLevels))
    (caller : OriginalNestedDisplay U common (.const value.name levels) assigned)
    (ordered : caller.sourceEnv.Ordered)
    (frame : OriginalTypeRouteFrame env registry target caller.graph commonLeft commonRight)
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    (generated : CappedCaptureGenerated base caps commonLeft commonRight
      caller.graph frame.realization.frame.raw) :
    (deltaAssignedTypeRoute origin seedWF packet caller ordered frame).Generated base caps := by
  refine ⟨?_, ?_⟩
  · simp only [deltaAssignedTypeRoute, RawGeneratedTypeRoute.WellFormed.eq_def, and_self]
  · intro boxed member
    simp only [deltaAssignedTypeRoute, RawGeneratedTypeRoute.frames.eq_def,
      List.mem_append, List.mem_singleton] at member
    rcases member with rfl | rfl
    · exact .empty common commonLeft commonRight
    · exact generated

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
