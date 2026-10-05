import Lean4Lean.Theory.Typing.AnchoredLiteralProjectionOrigins
import Lean4Lean.Theory.Typing.AnchoredFamilyCaptureDomains

/-! Connect literal primitive-projection origins to the exact requests
retained by a constructor capture tree. Both endpoint field types are
aligned through the original declared domain and paired substitution. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem FamilyCaptures.literalProjectionOrigins
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    {info : VProjectionInfo} {name : Name} {domains : List VExpr} {result : VExpr}
    (registered : env.projections name info)
    (shape : info.ctorType = wrapForalls domains result)
    {levels : List VLevel}
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (ctorClosed : info.ctorType.Closed)
    (relevant : (info.resultLevel.inst levels).IsNeverZero)
    {arguments newValues indices newIndices : List VExpr}
    (argumentCount : arguments.length = domains.length)
    (newCount : newValues.length = domains.length)
    (paramBound : info.nparams ≤ domains.length)
    (indexCount : indices.length = info.nindices)
    (newIndexCount : newIndices.length = info.nindices)
    {locals : List Nat} {keys : List (DataRequest (Profile n))} {footprint : Footprint}
    (captures : FamilyCaptures env U registry target (domains.map (·.instL levels)).reverse locals
      (nativeCaptureSubst arguments) (constantCaptureVariables domains.length) keys footprint)
    (raw : Ctx.SubstEq env U target (nativeCaptureSubst arguments)
      (nativeCaptureSubst newValues) (domains.map (·.instL levels)).reverse)
    (leftTyped : env.HasType U target (mkApps (.const info.ctorName levels) arguments)
      (mkApps (.const name levels) (arguments.take info.nparams ++ indices)))
    (rightTyped : env.HasType U target (mkApps (.const info.ctorName levels) newValues)
      (mkApps (.const name levels) (newValues.take info.nparams ++ newIndices)))
    {assignedType : VExpr}
    (leftFamily : TypeConversion env U target assignedType
      (mkApps (.const name levels) (arguments.take info.nparams ++ indices)))
    (rightFamily : TypeConversion env U target assignedType
      (mkApps (.const name levels) (newValues.take info.nparams ++ newIndices)))
    {index : Nat} {key : DataRequest (Profile n)}
    (fieldBound : info.nparams + index < domains.length)
    (keyAt : keys[info.nparams + index]? = some key) :
    Nonempty (RankedData.ProjectionOrigin env U target info name index
      (mkApps (.const info.ctorName levels) arguments) assignedType key.domain) ∧
    Nonempty (RankedData.ProjectionOrigin env U target info name index
      (mkApps (.const info.ctorName levels) newValues) assignedType key.domain) := by
  have leftLength : arguments.length = (domains.map (·.instL levels)).length := by
    simpa only [List.length_map] using argumentCount
  have rightLength : newValues.length = (domains.map (·.instL levels)).length := by
    simpa only [List.length_map] using newCount
  have rightRaw := Ctx.SubstEq.right henv hTarget raw
  obtain ⟨_, leftOrigins⟩ := literalProjectionPrefix henv hTarget registered shape levelsWF
    levelCount ctorClosed relevant argumentCount paramBound indexCount raw.left leftTyped
    (index + 1) (by omega)
  obtain ⟨_, rightOrigins⟩ := literalProjectionPrefix henv hTarget registered shape levelsWF
    levelCount ctorClosed relevant newCount paramBound newIndexCount rightRaw rightTyped
    (index + 1) (by omega)
  obtain ⟨⟨leftOrigin⟩, _⟩ := leftOrigins index (by omega)
  obtain ⟨⟨rightOrigin⟩, _⟩ := rightOrigins index (by omega)
  have alignment := FamilyCaptures.declaredDomain leftLength
    (by simpa only [List.length_map] using captures)
    (position := info.nparams + index) (by simpa only [List.length_map] using fieldBound) keyAt
  simp only [List.getElem_map] at alignment
  obtain ⟨fieldLevel, sourceFormation, _⟩ := Ctx.SubstEq.nativeArgument leftLength raw.left
    (position := info.nparams + index) (by simpa only [List.length_map] using fieldBound)
  have pairs := Ctx.SubstEq.nativeTake leftLength rightLength raw
    (count := info.nparams + index) (by simp only [List.length_map]; omega)
  have domainEq := sourceFormation.substDF henv pairs.wf hTarget pairs
  simp only [List.getElem_map, subst_sort] at domainEq
  exact ⟨⟨{ leftOrigin with
    familyPath := leftFamily.trans leftOrigin.familyPath
    fieldPath := leftOrigin.fieldPath.trans alignment.symm }⟩,
    ⟨{ rightOrigin with
      familyPath := rightFamily.trans rightOrigin.familyPath
      fieldPath := (rightOrigin.fieldPath.trans (.single domainEq.symm)).trans alignment.symm }⟩⟩

end Lean4Lean.AnchoredSource.Adapted
