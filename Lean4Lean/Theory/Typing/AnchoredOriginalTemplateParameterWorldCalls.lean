import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentPair

/-! A richer parameter demand is replayed at the retained actual argument,
not justified by inclusion in its old frozen input. Both source occurrences
are paid by their own outer projection world, including two same-side calls.
No cross-side parameter comparison is inferred from a common slot number. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private Located.dependencyEnvironment_of_prefix_nil from
  Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentPair
open private projectionMajor_cost_lt from
  Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionReindex
open private field_cost_lt from_left from_right from_both from
  Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- A retained argument at the root source cannot secretly be under another
source binder. This follows from its actual location, not from a new scope
assumption supplied by the caller. -/
theorem Located.sameSource_prefix_nil
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    (location : Located root node) : location.binderPrefix = [] := by
  have count := congrArg List.length location.context_eq
  simp only [List.length_append] at count
  apply List.length_eq_zero_iff.mp
  omega

theorem Located.sameSource_cost_le
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    (location : Located root node) (ordered : sourceEnv.Ordered) (initial : List Closure) :
    (Closure.close (node.dependencyOrigin ordered) initial).cost ≤
      (Closure.close (root.dependencyOrigin ordered) initial).cost := by
  have bound := location.dependency_cost_le ordered initial
  simpa only [Located.dependencyEnvironment_of_prefix_nil ordered location (Located.sameSource_prefix_nil location) initial] using bound

/-- The source parameter query remains at a real original descendant of the
major, even when the old finite slot demand was empty. -/
theorem ProjectionHead.parameter_below
    {outer : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead outer)
    {argument : EndpointState sourceEnv U source expression argumentType}
    (location : Located (.right head.major) argument)
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U environment)
    (phase parentPhase : RichPhase) :
    WorldBelow strata.rules.length (originalCallWorld controls phase argument captured)
      (originalCallWorld controls parentPhase outer captured) :=
  original_child (richSchedule_strict
    (Nat.lt_of_le_of_lt (Located.sameSource_cost_le location controls.ordered environment)
      (projectionMajor_cost_lt head controls.ordered environment)) phase parentPhase) _ _ _ _ _

/-- The independently typed occurrence discovered in the field is paid by
that exact original field child. No source node for a residual template is
constructed. -/
theorem ProjectionHead.parameterOwner_below
    {outer : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead outer)
    (field : EndpointRef sourceEnv U source head.fieldType (.sort head.fieldLevel))
    (field_eq : head.field = .ref field)
    {owner : EndpointState sourceEnv U source expression ownerType}
    (location : Located field owner)
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U environment)
    (phase parentPhase : RichPhase) :
    WorldBelow strata.rules.length (originalCallWorld controls phase owner captured)
      (originalCallWorld controls parentPhase outer captured) := by
  have fieldBound := field_cost_lt head controls.ordered environment
  rw [field_eq] at fieldBound
  exact original_child (richSchedule_strict
    (Nat.lt_of_le_of_lt (Located.sameSource_cost_le location controls.ordered environment) fieldBound)
      phase parentPhase) _ _ _ _ _

/-- All source-side calls needed to replay a newly discovered hole demand.
Expression agreement is checked by the consumer; these are the exact
original C/R/F endpoints, independently of the new profile's size or grade. -/
theorem ProjectionHead.parameterSourceFunding
    {outer : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead outer)
    (field : EndpointRef sourceEnv U source head.fieldType (.sort head.fieldLevel))
    (field_eq : head.field = .ref field)
    {owner : EndpointState sourceEnv U source expression ownerType}
    {argument : EndpointState sourceEnv U source argumentExpression argumentType}
    (ownerLocation : Located field owner)
    (argumentLocation : Located (.right head.major) argument)
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U environment)
    (other : World strata.rules.length) :
    let parent := [originalCallWorld controls .assignedComparison outer captured, other]
    CallBelow strata.rules.length
      [originalCallWorld controls .assignedComparison owner captured,
       originalCallWorld controls .assignedComparison argument captured] parent ∧
    CallBelow strata.rules.length
      [originalCallWorld controls .expressionReindex owner captured,
       originalCallWorld controls .expressionReindex argument captured] parent ∧
    CallBelow strata.rules.length [originalCallWorld controls .fundamental argument captured] parent := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · apply from_left
    intro call member
    rcases List.mem_cons.mp member with rfl | member
    · exact ProjectionHead.parameterOwner_below head field field_eq ownerLocation controls captured _ _
    · cases List.mem_singleton.mp member
      exact ProjectionHead.parameter_below head argumentLocation controls captured _ _
  · apply from_left
    intro call member
    rcases List.mem_cons.mp member with rfl | member
    · exact ProjectionHead.parameterOwner_below head field field_eq ownerLocation controls captured _ _
    · cases List.mem_singleton.mp member
      exact ProjectionHead.parameter_below head argumentLocation controls captured _ _
  · apply from_left
    intro call member
    cases List.mem_singleton.mp member
    exact ProjectionHead.parameter_below head argumentLocation controls captured _ _

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
