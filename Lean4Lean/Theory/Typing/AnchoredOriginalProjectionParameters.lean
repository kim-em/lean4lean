import Lean4Lean.Theory.Typing.ProjectionParameterProvenance
import Lean4Lean.Theory.Typing.AnchoredOriginalParameterEqualities

/-! Frozen original normalization and common-parameter equality roots at the
actual declaration stages and universe instance. Family normalization stays
separate from both context-conversion legs and universe equivalence. -/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

structure ProjectionParameterShape (origin : ProjectionParameterOrigin env name info) where
  common : List VExpr
  normalized : VExpr
  familyParams : List VExpr
  familyTail : VExpr
  indices : List VExpr
  result : VExpr
  assigned : VExpr
  ctorParams : List VExpr
  ctorTail : VExpr
  normalization : origin.base.IsDefEq origin.declaration.uvars [] origin.family.type normalized assigned
  familyTake : normalized.takeForalls info.nparams = some (familyParams, familyTail)
  indicesTake : familyTail.takeForalls info.nindices = some (indices, result)
  familyEquality : IsDefEqCtx origin.base origin.declaration.uvars [] common.reverse familyParams.reverse
  resultSort : origin.base.IsDefEq origin.declaration.uvars (indices.reverse ++ familyParams.reverse)
    result (.sort info.resultLevel) (.sort (.succ info.resultLevel))
  ctorTake : info.ctorType.takeForalls info.nparams = some (ctorParams, ctorTail)
  constructorEquality : IsDefEqCtx origin.types origin.declaration.uvars [] common.reverse ctorParams.reverse

noncomputable def selectProjectionParameterOrigin (ordered : env.Ordered)
    (registered : env.projections name info) : ProjectionParameterOrigin env name info :=
  Classical.choice (ordered.projectionParameterOrigin registered)

noncomputable def selectProjectionParameterShape (origin : ProjectionParameterOrigin env name info) :
    ProjectionParameterShape origin := by
  have existsShape : Nonempty (ProjectionParameterShape origin) := by
    obtain ⟨common, normalized, familyParams, familyTail, indices, result, assigned, ctorParams, ctorTail,
      normalization, familyTake, indicesTake, familyEquality, resultSort, ctorTake, constructorEquality⟩ :=
      origin.correspondence
    exact ⟨⟨common, normalized, familyParams, familyTail, indices, result, assigned, ctorParams, ctorTail,
      normalization, familyTake, indicesTake, familyEquality, resultSort, ctorTake, constructorEquality⟩⟩
  exact Classical.choice existsShape

structure ProjectionParameterInstance
    {origin : ProjectionParameterOrigin env name info} (shape : ProjectionParameterShape origin)
    (U : Nat) (levels : List VLevel) where
  normalization : Derivation origin.base U [] (origin.family.type.instL levels)
    (shape.normalized.instL levels) (shape.assigned.instL levels)
  family : OriginalContextEquality origin.base U (shape.common.reverse.map (VExpr.instL levels))
    (shape.familyParams.reverse.map (VExpr.instL levels))
  constructor : OriginalContextEquality origin.types U (shape.common.reverse.map (VExpr.instL levels))
    (shape.ctorParams.reverse.map (VExpr.instL levels))

noncomputable def ProjectionParameterShape.instance
    {origin : ProjectionParameterOrigin env name info} (shape : ProjectionParameterShape origin)
    (levelsWF : ∀ level ∈ levels, level.WF U) : ProjectionParameterInstance shape U levels := {
  normalization := Classical.choice
    (ParameterEqualityRoot.normalizationInstance origin.baseOrdered shape.normalization levelsWF)
  family := Classical.choice (OriginalContextEquality.reifyInstance origin.baseOrdered shape.familyEquality levelsWF)
  constructor := Classical.choice
    (OriginalContextEquality.reifyInstance origin.typesOrdered shape.constructorEquality levelsWF) }

/-- Equivalent seed universes get their own finite original comparison;
they are never identified by equality or charged at another instance. -/
noncomputable def ProjectionParameterShape.commonUniverse
    {origin : ProjectionParameterOrigin env name info} (shape : ProjectionParameterShape origin)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels) :
    OriginalContextEquality origin.base U (shape.common.reverse.map (VExpr.instL leftLevels))
      (shape.common.reverse.map (VExpr.instL rightLevels)) :=
  Classical.choice ((Classical.choice (OriginalContextEquality.reify origin.baseOrdered shape.familyEquality)).universeInstance
    origin.baseOrdered leftWF rightWF equivalent)

namespace ProjectionParameterInstance

variable {origin : ProjectionParameterOrigin env name info} {shape : ProjectionParameterShape origin}

def baseRoots (retained : ProjectionParameterInstance shape U levels) : List (ParameterEqualityRoot origin.base U) :=
  ⟨[], .nil, _, _, _, retained.normalization⟩ :: retained.family.roots

def typeRoots (retained : ProjectionParameterInstance shape U levels) : List (ParameterEqualityRoot origin.types U) :=
  retained.constructor.roots

theorem baseRoots_length (retained : ProjectionParameterInstance shape U levels) :
    retained.baseRoots.length = info.nparams + 1 := by
  have params := VExpr.takeForalls_domains_length shape.familyTake
  have same := retained.family.length_eq
  simp only [List.length_map, List.length_reverse] at same
  simp only [baseRoots, List.length_cons, OriginalContextEquality.roots_length,
    List.length_map, List.length_reverse]
  omega

theorem typeRoots_length (retained : ProjectionParameterInstance shape U levels) :
    retained.typeRoots.length = info.nparams := by
  have params := VExpr.takeForalls_domains_length shape.ctorTake
  have same := retained.constructor.length_eq
  simp only [List.length_map, List.length_reverse] at same
  simp only [typeRoots, OriginalContextEquality.roots_length, List.length_map, List.length_reverse]
  omega

end ProjectionParameterInstance

/-- One fixed choice of stage and declaration shape serves every retained
instance. A dependency calculation can use its actual base/type root lists. -/
structure OriginalProjectionParameters (env : VEnv) (U : Nat) (name : Name)
    (info : VProjectionInfo) (levels : List VLevel) where
  origin : ProjectionParameterOrigin env name info
  shape : ProjectionParameterShape origin
  instantiated : ProjectionParameterInstance shape U levels

noncomputable def selectProjectionParameters (ordered : env.Ordered)
    (registered : env.projections name info) (levelsWF : ∀ level ∈ levels, level.WF U) :
    OriginalProjectionParameters env U name info levels :=
  let origin := selectProjectionParameterOrigin ordered registered
  let shape := selectProjectionParameterShape origin
  ⟨origin, shape, shape.instance levelsWF⟩

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
