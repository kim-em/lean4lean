import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderUniverseRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteProvenance
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls

/-! The retained universe route opens actual earlier declaration sources at
the caller's SAME cutoff and fuel. Its equality proof may be arbitrarily
large: constant-count descent, rather than a synthesized cost bound, pays
for every actual R/F/R endpoint. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Restrict the actual source while preserving every equation control. -/
def OriginalWorldControls.atHeader
    (controls : OriginalWorldControls strata sourceEnv)
    (origin : ConstantHeaderOrigin sourceEnv name info) : OriginalWorldControls strata origin.source :=
  ⟨origin.ordered, controls.cutoff, controls.cutoffBound,
    controls.sourceCutoff.source_mono origin.sourceBelow, controls.fuel⟩

/-- Any actual closed original in this earlier declaration source is paid
at the unchanged control prefix, independently of its proof size. -/
theorem originalClosedHeader_below
    (controls : OriginalWorldControls strata sourceEnv)
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (node : EndpointState origin.source U [] expression assigned)
    (caller : EndpointState sourceEnv U source callerExpression callerAssigned)
    (captured : WorldEnvironmentProvenance strata U environment)
    (phase callerPhase : RichPhase) :
    WorldBelow strata.rules.length
      (originalCallWorld (controls.atHeader origin) phase node .nil)
      (originalCallWorld controls callerPhase caller captured) := by
  apply Below.root
    (EquationControlMeasure.constantsDecrease (origin.count_lt controls.ordered) _ _ _ _ _)
  intro child member
  cases member

private theorem environment_worlds_mpr
    {first second : List OriginalClosureMeasure.Closure}
    (indices : first = second)
    (equal : WorldEnvironmentProvenance strata U first = WorldEnvironmentProvenance strata U second)
    (annotation : WorldEnvironmentProvenance strata U second) :
    (equal.mpr annotation).worlds = annotation.worlds := by
  cases indices
  cases equal
  rfl

private noncomputable def sameExpression_worldInputs
    (left : OriginalNestedDisplay U common leftExpression leftAssigned)
    (right : OriginalNestedDisplay U common rightExpression rightAssigned)
    (same : leftExpression = rightExpression)
    (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (initial : List OriginalClosureMeasure.Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (rightControls : OriginalWorldControls strata right.sourceEnv)
    (leftWorld : WorldEnvironmentProvenance strata U initial)
    (rightWorld : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment rf)) :
    (RawGeneratedTypeRoute.sameExpression left right same lf rf initial frame).WorldInputs strata := by
  cases same
  change OriginalWorldControls strata left.sourceEnv × OriginalWorldControls strata right.sourceEnv ×
    WorldEnvironmentProvenance strata U initial ×
    WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment rf)
  exact ⟨leftControls, rightControls, leftWorld, rightWorld⟩

private theorem sameExpression_worldReserve
    (left : OriginalNestedDisplay U common leftExpression leftAssigned)
    (right : OriginalNestedDisplay U common rightExpression rightAssigned)
    (same : leftExpression = rightExpression)
    (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (initial : List OriginalClosureMeasure.Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (rightControls : OriginalWorldControls strata right.sourceEnv)
    (leftWorld : WorldEnvironmentProvenance strata U initial)
    (rightWorld : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment rf)) :
    ((RawGeneratedTypeRoute.sameExpression left right same lf rf initial frame).worldReserve
      (sameExpression_worldInputs left right same lf rf initial frame
        leftControls rightControls leftWorld rightWorld)).worlds =
      [originalCallWorld leftControls .expressionReindex left.node leftWorld,
       originalCallWorld rightControls .expressionReindex right.node rightWorld] := by
  cases same
  have indices := RawGeneratedTypeRoute.reserve.eq_def
    (RawGeneratedTypeRoute.same left right lf rf initial frame)
  simp only [sameExpression_worldInputs, RawGeneratedTypeRoute.sameExpression,
    RawGeneratedTypeRoute.WorldInputs, RawGeneratedTypeRoute.worldReserve]
  rw [environment_worlds_mpr indices]
  rfl

private noncomputable def trans_worldInputs
    {strata : EquationStratification env}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    (firstInput : first.WorldInputs strata) (secondInput : second.WorldInputs strata) :
    (first.trans second).WorldInputs strata := by
  rw [RawGeneratedTypeRoute.WorldInputs.eq_def]
  exact ⟨firstInput, secondInput⟩

private theorem trans_worldReserve
    {strata : EquationStratification env}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    (firstInput : first.WorldInputs strata) (secondInput : second.WorldInputs strata) :
    ((first.trans second).worldReserve (trans_worldInputs firstInput secondInput)).worlds =
      (first.worldReserve firstInput).worlds ++ (second.worldReserve secondInput).worlds := by
  simp only [RawGeneratedTypeRoute.worldReserve, RawGeneratedTypeRoute.WorldInputs, trans_worldInputs]
  rw [environment_worlds_mpr (RawGeneratedTypeRoute.reserve.eq_def (first.trans second))]
  exact WorldEnvironmentProvenance.worlds_append _ _

private theorem equality_worldReserve
    {strata : EquationStratification env}
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (original : Derivation sourceEnv U source A B (.sort level)) (forward : Bool)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env) (initial : List OriginalClosureMeasure.Closure)
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U initial) :
    ((RawGeneratedTypeRoute.equality (registry := registry) (target := target)
      (commonLeft := left) (commonRight := right) graph original forward ordered below initial).worldReserve
      (controls, captured)).worlds =
      [originalCallWorld controls .fundamental (.ref (.left original)) captured] := by
  simp only [RawGeneratedTypeRoute.worldReserve, RawGeneratedTypeRoute.WorldInputs]
  rw [environment_worlds_mpr (RawGeneratedTypeRoute.reserve.eq_def
    (RawGeneratedTypeRoute.equality (registry := registry) (target := target)
      (commonLeft := left) (commonRight := right) graph original forward ordered below initial))]
  rfl

namespace RetainedHeaderUniverse

variable {U : Nat} {leftLevels rightLevels : List VLevel}

/-- The exact two R pairs and middle equality F in `route`, all below the
actual caller. No new sponsor or raw equality answer is assumed. -/
theorem worldFunding
    (controls : OriginalWorldControls strata sourceEnv)
    (leftOrigin rightOrigin : ConstantHeaderOrigin sourceEnv name info)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (caller : EndpointState sourceEnv U source expression assigned)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase) :
    let equality := original rightOrigin leftWF rightWF equivalent
    let parent := originalCallWorld controls phase caller captured
    CallBelow strata.rules.length
      [originalCallWorld (controls.atHeader leftOrigin) .expressionReindex
        (.ref (leftOrigin.familyHeader leftWF).reference) .nil,
       originalCallWorld (controls.atHeader rightOrigin) .expressionReindex (.ref (.left equality)) .nil] [parent] ∧
    CallBelow strata.rules.length
      [originalCallWorld (controls.atHeader rightOrigin) .fundamental (.ref (.left equality)) .nil] [parent] ∧
    CallBelow strata.rules.length
      [originalCallWorld (controls.atHeader rightOrigin) .expressionReindex (.ref (.right equality)) .nil,
       originalCallWorld (controls.atHeader rightOrigin) .expressionReindex
        (.ref (rightOrigin.familyHeader rightWF).reference) .nil] [parent] := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · apply split_call
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact originalClosedHeader_below controls leftOrigin _ caller captured _ _
    · cases List.mem_singleton.mp member
      exact originalClosedHeader_below controls rightOrigin _ caller captured _ _
  · apply split_call
    intro child member
    cases List.mem_singleton.mp member
    exact originalClosedHeader_below controls rightOrigin _ caller captured _ _
  · apply split_call
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact originalClosedHeader_below controls rightOrigin _ caller captured _ _
    · cases List.mem_singleton.mp member
      exact originalClosedHeader_below controls rightOrigin _ caller captured _ _

/-- Controls and typed empty ledgers for every actual node of the retained
R/F/R route. They are read by the shared history constructor; no arbitrary
reserve annotation is supplied. -/
noncomputable def worldInputs
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (leftOrigin rightOrigin : ConstantHeaderOrigin sourceEnv name info)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (below : sourceEnv ≤ env) (common : List VExpr)
    (registry : CanonicalHead.Registry) (target : List VExpr) (left right : Subst) :
    (route leftOrigin rightOrigin leftWF rightWF equivalent below common registry target left right).WorldInputs strata := by
  let equality := original rightOrigin leftWF rightWF equivalent
  let graph := closedCaptureGraph (ContextDerivation.nil (env := rightOrigin.source) (U := U)) common
  let equalityFrame := closedTypeRouteFrame
    (ContextDerivation.nil (env := rightOrigin.source) (U := U)) common env registry target left right
  have first := sameExpression_worldInputs
    (display leftOrigin leftWF common) (graph.typeEqualityDisplay equality true)
    subst_id.symm leftOrigin.ordered rightOrigin.ordered [] equalityFrame
    (controls.atHeader leftOrigin) (controls.atHeader rightOrigin) .nil .nil
  have last := sameExpression_worldInputs
    (graph.typeEqualityDisplay equality false) (display rightOrigin rightWF common)
    subst_id rightOrigin.ordered rightOrigin.ordered []
    (frame rightOrigin rightWF common env registry target left right)
    (controls.atHeader rightOrigin) (controls.atHeader rightOrigin) .nil .nil
  have middle : (RawGeneratedTypeRoute.equality (registry := registry) (target := target)
      (commonLeft := left) (commonRight := right) graph equality true rightOrigin.ordered
      (rightOrigin.sourceBelow.trans below) []).WorldInputs strata := by
    change OriginalWorldControls strata rightOrigin.source × WorldEnvironmentProvenance strata U []
    exact ⟨controls.atHeader rightOrigin, .nil⟩
  exact trans_worldInputs first (trans_worldInputs middle last)

/-- The computed reserve retains exactly the actual header/equality/header
worlds, including their multiplicities. -/
theorem worldReserve_worlds
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (leftOrigin rightOrigin : ConstantHeaderOrigin sourceEnv name info)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (below : sourceEnv ≤ env) (common : List VExpr)
    (registry : CanonicalHead.Registry) (target : List VExpr) (left right : Subst) :
    let equality := original rightOrigin leftWF rightWF equivalent
    let first := originalCallWorld (controls.atHeader leftOrigin) .expressionReindex
      (.ref (leftOrigin.familyHeader leftWF).reference) .nil
    let middleR := originalCallWorld (controls.atHeader rightOrigin) .expressionReindex (.ref (.left equality)) .nil
    let middleF := originalCallWorld (controls.atHeader rightOrigin) .fundamental (.ref (.left equality)) .nil
    let last := originalCallWorld (controls.atHeader rightOrigin) .expressionReindex
      (.ref (rightOrigin.familyHeader rightWF).reference) .nil
    ((route leftOrigin rightOrigin leftWF rightWF equivalent below common registry target left right).worldReserve
      (worldInputs controls leftOrigin rightOrigin leftWF rightWF equivalent below common registry target left right)).worlds =
      [first, middleR, middleF, middleR, last] := by
  dsimp only
  simp only [worldInputs, route]
  rw [trans_worldReserve, trans_worldReserve]
  simp only [id_eq]
  erw [sameExpression_worldReserve, equality_worldReserve, sameExpression_worldReserve]
  rfl

/-- Dormant universe-route history is funded by this SAME caller, with no
fresh envelope around the returned reserve. -/
theorem worldReserve_sponsored
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (leftOrigin rightOrigin : ConstantHeaderOrigin sourceEnv name info)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (below : sourceEnv ≤ env) (common : List VExpr)
    (registry : CanonicalHead.Registry) (target : List VExpr) (left right : Subst)
    (caller : EndpointState sourceEnv U source expression assigned)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase) :
    Sponsored [originalCallWorld controls phase caller captured]
      ((route leftOrigin rightOrigin leftWF rightWF equivalent below common registry target left right).worldReserve
        (worldInputs controls leftOrigin rightOrigin leftWF rightWF equivalent below common registry target left right)).worlds := by
  rw [worldReserve_worlds]
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨_, List.mem_singleton_self _, originalClosedHeader_below controls _ _ caller captured _ _⟩

end RetainedHeaderUniverse
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
