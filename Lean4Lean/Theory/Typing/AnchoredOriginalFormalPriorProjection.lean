import Lean4Lean.Theory.Typing.AnchoredOriginalDerivationRenaming
import Lean4Lean.Theory.Typing.AnchoredOriginalTypeFormation

/-! A genuine formal first projection, built from retained original
formation references. No semantic typing proof is reified. -/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

noncomputable def EndpointRef.reflexiveOriginal
    (reference : EndpointRef env U source expression type) :
    Derivation env U source expression expression type :=
  match reference with
  | .left original => .trans original (.symm original)
  | .right original => .trans (.symm original) original

noncomputable def EndpointRef.weakNOriginal (ordered : env.Ordered)
    (insertion : Ctx.LiftN n k source destination)
    (reference : EndpointRef env U source expression type) :
    EndpointRef env U destination (expression.liftN n k) (type.liftN n k) :=
  match reference with
  | .left original => .left (original.weakN ordered insertion)
  | .right original => .right (original.weakN ordered insertion)

private theorem fieldType_zero_major (info : VProjectionInfo) :
    info.fieldType name levels params 0 first = info.fieldType name levels params 0 second := by
  unfold VProjectionInfo.fieldType
  split
  · rfl
  · cases VProjectionInfo.instantiateProjectionParameters (info.ctorType.instL levels) params with
    | none => rfl
    | some tail => cases tail <;> rfl

noncomputable def formalMajorVariableOriginal
    (ordered : env.Ordered)
    (major : Derivation env U source sourceMajor expression
      (mkApps (.const name levels) (parameters ++ indices))) :
    Derivation env U
      (mkApps (.const name levels) (parameters ++ indices) :: source)
      (.bvar 0) (.bvar 0)
      (mkApps (.const name levels)
        (parameters.map (fun p => p.lift) ++ indices.map (fun i => i.lift))) := by
  let formation := major.familyFormationRef
  let lifted := formation.reference.reflexiveOriginal.weakN ordered
    (Ctx.LiftN.one (A := mkApps (.const name levels) (parameters ++ indices)))
  let node : Derivation env U
      (mkApps (.const name levels) (parameters ++ indices) :: source)
      (.bvar 0) (.bvar 0)
      ((mkApps (.const name levels) (parameters ++ indices)).lift) :=
    .bvar .zero formation.levelWF lifted
  exact node.castIndices rfl rfl rfl
    (by simp only [VExpr.liftN_mkApps, VExpr.liftN, List.map_append])

/-- The actual major's assigned family formation supplies the new variable
binder. The first field is independent of that major, so its retained
formation is merely weakened. -/
noncomputable def formalFirstProjection
    (ordered : env.Ordered)
    (registered : env.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : parameters.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels parameters 0 sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef env U source fieldType (.sort fieldLevel))
    (major : Derivation env U source sourceMajor expression
      (mkApps (.const name levels) (parameters ++ indices)))
    (closed : info.ctorType.Closed)
    (relevance : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero) :
    EndpointState env U
      (mkApps (.const name levels) (parameters ++ indices) :: source)
      (.proj name 0 (.bvar 0)) fieldType.lift := by
  let majorVariable := formalMajorVariableOriginal ordered major
  have selectedLift := VProjectionInfo.fieldType_liftN
    (typeName := name) (levels := levels) (params := parameters)
    (index := 0) (major := sourceMajor) (n := 1) (k := 0) info closed
  rw [selected] at selectedLift
  have selectedVariable : info.fieldType name levels
      (parameters.map fun parameter => parameter.lift) 0 (.bvar 0) = some fieldType.lift := by
    rw [fieldType_zero_major (second := sourceMajor.lift)]
    exact selectedLift
  simpa only [VExpr.liftN_mkApps, VExpr.liftN, List.map_append] using
    (EndpointState.proj (indices := indices.map fun i => i.lift) registered levelsWF levelCount
      (by simpa using parameterCount) (by simpa using indexCount)
      selectedVariable fieldWF (EndpointState.ref (field.weakNOriginal ordered Ctx.LiftN.one))
      majorVariable closed relevance)

noncomputable def formalFirstProjectionOriginal
    (ordered : env.Ordered)
    (registered : env.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : parameters.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels parameters 0 sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef env U source fieldType (.sort fieldLevel))
    (major : Derivation env U source sourceMajor expression
      (mkApps (.const name levels) (parameters ++ indices)))
    (closed : info.ctorType.Closed)
    (relevance : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero) :
    Derivation env U
      (mkApps (.const name levels) (parameters ++ indices) :: source)
      (.proj name 0 (.bvar 0)) (.proj name 0 (.bvar 0)) fieldType.lift := by
  let majorVariable := formalMajorVariableOriginal ordered major
  have selectedLift := VProjectionInfo.fieldType_liftN
    (typeName := name) (levels := levels) (params := parameters)
    (index := 0) (major := sourceMajor) (n := 1) (k := 0) info closed
  rw [selected] at selectedLift
  have selectedVariable : info.fieldType name levels
      (parameters.map fun parameter => parameter.lift) 0 (.bvar 0) = some fieldType.lift := by
    rw [fieldType_zero_major (second := sourceMajor.lift)]
    exact selectedLift
  exact
    (Derivation.projDF (indexArgs := indices.map fun i => i.lift) registered levelsWF levelCount
      (by simpa using parameterCount) (by simpa using indexCount)
      selectedVariable fieldWF
      (field.reflexiveOriginal.weakN ordered Ctx.LiftN.one)
      majorVariable
      majorVariable
      closed relevance)


end Lean4Lean.AnchoredSource.OriginalClosureMeasure
