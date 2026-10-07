import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.Typing.ConstantHeaderProvenance

/-! The actual declaration stages for a projection's parameter agreement.
The family normalization and the constructor parameter comparison are kept
at their original checking stages, before the constructor is installed. -/
namespace Lean4Lean.VEnv
open VExpr
set_option backward.isDefEq.respectTransparency false

structure ProjectionParameterOrigin (env : VEnv) (name : Name) (info : VProjectionInfo) where
  base : VEnv
  types : VEnv
  baseOrdered : base.Ordered
  typesOrdered : types.Ordered
  declaration : VInductDecl
  family : VInductiveType
  constructor : VConstVal
  familyMember : family ∈ declaration.types
  constructorOnly : family.ctors = [constructor]
  name_eq : family.name = name
  info_eq : info = {
    uvars := declaration.uvars
    nparams := declaration.nparams
    nindices := family.numIndices
    resultLevel := family.resultLevel
    ctorName := constructor.name
    ctorType := constructor.type }
  familyWF : family.toVConstant.WF base
  constructorWF : constructor.toVConstant.WF types
  parameters : declaration.SourceParameterWF base
  addTypes : base.addConstVals declaration.typeConstants = some types
  typesBelow : types ≤ env
  constructorFresh : types.constants constructor.name = none
  constructorPresent : env.constants constructor.name = some constructor.toVConstant
  familyPresent : env.constants name = some family.toVConstant

namespace ProjectionParameterOrigin

def extend (origin : ProjectionParameterOrigin env name info) (below : env ≤ extended) :
    ProjectionParameterOrigin extended name info := {
  origin with
  typesBelow := origin.typesBelow.trans below
  constructorPresent := below.constants origin.constructorPresent
  familyPresent := below.constants origin.familyPresent }

theorem baseBelow (origin : ProjectionParameterOrigin env name info) : origin.base ≤ env :=
  (VEnv.addConstVals_le origin.addTypes).trans origin.typesBelow

def constructorOrigin (origin : ProjectionParameterOrigin env name info) :
    ConstantHeaderOrigin env origin.constructor.name origin.constructor.toVConstant := {
  source := origin.types
  ordered := origin.typesOrdered
  formation := origin.constructorWF
  sourceBelow := origin.typesBelow
  fresh := origin.constructorFresh
  constant := origin.constructorPresent }

theorem types_count_lt (origin : ProjectionParameterOrigin env name info) (ordered : env.Ordered) :
    origin.typesOrdered.constantCount < ordered.constantCount := origin.constructorOrigin.count_lt ordered

theorem base_count_lt (origin : ProjectionParameterOrigin env name info) (ordered : env.Ordered) :
    origin.baseOrdered.constantCount < ordered.constantCount := by
  have bound := (Classical.choice origin.baseOrdered.constantDomain).length_le
    (Classical.choice origin.typesOrdered.constantDomain) (VEnv.addConstVals_le origin.addTypes)
  exact Nat.lt_of_le_of_lt bound (origin.types_count_lt ordered)

/-- The two parameter legs share the exact original context. They are not
composed using uniqueness of typing, and the normalized family header is
not identified with the raw family header. -/
theorem correspondence (origin : ProjectionParameterOrigin env name info) :
    ∃ (common : List VExpr) (normalized : VExpr) (familyParams : List VExpr)
      (familyTail : VExpr) (indices : List VExpr) (result assigned : VExpr)
      (ctorParams : List VExpr) (ctorTail : VExpr),
      origin.base.IsDefEq origin.declaration.uvars [] origin.family.type normalized assigned ∧
      normalized.takeForalls info.nparams = some (familyParams, familyTail) ∧
      familyTail.takeForalls info.nindices = some (indices, result) ∧
      IsDefEqCtx origin.base origin.declaration.uvars [] common.reverse familyParams.reverse ∧
      origin.base.IsDefEq origin.declaration.uvars (indices.reverse ++ familyParams.reverse)
        result (.sort info.resultLevel) (.sort (.succ info.resultLevel)) ∧
      info.ctorType.takeForalls info.nparams = some (ctorParams, ctorTail) ∧
      IsDefEqCtx origin.types origin.declaration.uvars [] common.reverse ctorParams.reverse := by
  obtain ⟨common, types, installed, families, constructors, raw⟩ := origin.parameters
  cases Option.some.inj (installed.symm.trans origin.addTypes)
  obtain ⟨normalized, familyParams, familyTail, indices, result, assigned, normal,
    familyTake, indicesTake, familyEqual, resultSort⟩ := families origin.family origin.familyMember
  have member : origin.constructor ∈ origin.family.ctors := by simp [origin.constructorOnly]
  obtain ⟨ctorParams, ctorTail, ctorTake, ctorEqual⟩ := constructors origin.family origin.familyMember
    origin.constructor member
  have np := congrArg VProjectionInfo.nparams origin.info_eq
  have ni := congrArg VProjectionInfo.nindices origin.info_eq
  have rl := congrArg VProjectionInfo.resultLevel origin.info_eq
  have ct := congrArg VProjectionInfo.ctorType origin.info_eq
  simp only at np ni rl ct
  rw [np, ni, rl, ct]
  exact ⟨common, normalized, familyParams, familyTail, indices, result, assigned, ctorParams, ctorTail,
    normal, familyTake, indicesTake, familyEqual, resultSort, ctorTake, ctorEqual⟩

end ProjectionParameterOrigin

/-- Registration retains the original pre-installation header typing, so
both original comparison stages are ordered without backwards inversion of
an unrelated final-environment formation proof. -/
theorem Ordered.projectionParameterOrigin (ordered : env.Ordered)
    (registered : env.projections name info) : Nonempty (ProjectionParameterOrigin env name info) := by
  induction ordered with
  | empty => cases registered
  | const _ _ added ih =>
    rw [VEnv.addConst_projections added] at registered
    obtain ⟨origin⟩ := ih registered
    exact ⟨origin.extend (VEnv.addConst_le added)⟩
  | defeq _ _ ih =>
    obtain ⟨origin⟩ := ih registered
    exact ⟨origin.extend VEnv.addDefEq_le⟩
  | eliminator _ ih =>
    obtain ⟨origin⟩ := ih registered
    exact ⟨origin.extend VEnv.addEliminator_le⟩
  | @inductProjections base types ctors decl block _es baseOrdered ctorsOrdered names typeHeadersWF
      ctorUvars ctorWF parameters raw types_eq ctors_eq projections_eq addTypes addCtors ihBase ihCtors =>
    rw [VEnv.addProjections_iff, VEnv.addEliminators_projections] at registered
    rcases registered with fresh | previous
    · obtain ⟨entry, member, rfl, rfl⟩ := fresh
      rw [projections_eq] at member
      obtain ⟨family, familyMember, ctor, only, rfl⟩ := VInductDecl.projectionEntries_origin member
      have typed : ∀ value ∈ block.types, value.toVConstant.WF base := by
        rw [types_eq]
        intro value member
        change value ∈ decl.types.map VInductiveType.toVConstVal at member
        obtain ⟨targetType, targetMember, equality⟩ := List.mem_map.mp member
        cases equality
        exact typeHeadersWF targetType targetMember
      have typesOrdered := baseOrdered.addConstVals typed addTypes
      have ctorMember : ctor ∈ decl.constructorConstants :=
        List.mem_flatMap.mpr ⟨family, familyMember, by simp [only]⟩
      have ctorInBlock : ctor ∈ block.ctors := by rw [ctors_eq]; exact ctorMember
      have familyInBlock : family.toVConstVal ∈ block.types := by
        rw [types_eq]
        exact List.mem_map.mpr ⟨family, familyMember, rfl⟩
      have below : types ≤ (ctors.addEliminators _es).addProjections block.projections :=
        (VEnv.addConstVals_le addCtors).trans VEnv.addEliminators_addProjections_le
      exact ⟨{
        base := base, types := types, baseOrdered := baseOrdered, typesOrdered := typesOrdered
        declaration := decl, family := family, constructor := ctor, familyMember := familyMember
        constructorOnly := only, name_eq := rfl, info_eq := rfl
        familyWF := typeHeadersWF family familyMember
        constructorWF := ctorWF ctor ctorMember
        parameters := parameters, addTypes := types_eq ▸ addTypes
        typesBelow := below
        constructorFresh := VEnv.addConstVals_names_fresh addCtors ctor ctorInBlock
        constructorPresent := VEnv.addEliminators_addProjections_le.constants
          (VEnv.addConstVals_get addCtors ctorInBlock)
        familyPresent := below.constants (VEnv.addConstVals_get addTypes familyInBlock) }⟩
    · obtain ⟨origin⟩ := ihCtors previous
      exact ⟨origin.extend VEnv.addEliminators_addProjections_le⟩

end Lean4Lean.VEnv
