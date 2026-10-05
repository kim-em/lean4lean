import Lean4Lean.Theory.Typing.AnchoredCapturedProjectionOrigins
import Lean4Lean.Theory.Typing.AnchoredLiteralRecord

/-! Actual constructor captures introduce a finite record demand. Every
selected field request is the unchanged request at its declaration position;
primitive projection origins are constructed from the declared telescope. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles

theorem Arguments.selectedRequest
    {env : VEnv} {U n : Nat} {lower : Relations n} {target : List VExpr}
    {keys : List (DataRequest (Profile n))} {left right : List VExpr}
    (arguments : Arguments env U lower target keys left right)
    {position : Nat} {request : DataRequest (Profile n)}
    (selected : keys[position]? = some request) :
    ∃ value value', left[position]? = some value ∧ right[position]? = some value' ∧
      RequestAdmission env U lower target request value value' := by
  induction arguments generalizing position with
  | nil => simp at selected
  | @cons key value value' keys left right admitted rest ih =>
    cases position with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
      subst request
      exact ⟨value, value', rfl, rfl, admitted⟩
    | succ position => exact ih selected

end Lean4Lean.AnchoredSemantics.RankedData

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem FamilyCaptures.literalRecordFromArguments
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {info : VProjectionInfo} {demand : RecordData (Profile n)}
    {domains : List VExpr} {result : VExpr}
    (registered : env.projections demand.family.name info)
    (lookup : registry.projections demand.family.name = some info)
    (inert : CanonicalDataHead.HeadInert registry info.ctorName)
    (shape : info.ctorType = wrapForalls domains result)
    (layout : domains.length = info.nparams + info.numFields)
    {levels : List VLevel}
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (ctorClosed : info.ctorType.Closed)
    (relevant : (info.resultLevel.inst levels).IsNeverZero)
    {arguments newValues indices newIndices : List VExpr}
    (argumentCount : arguments.length = domains.length)
    (newCount : newValues.length = domains.length)
    (indexCount : indices.length = info.nindices)
    (newIndexCount : newIndices.length = info.nindices)
    {locals : List Nat} {keys : List (DataRequest (Profile n))} {footprint : Footprint}
    (captures : FamilyCaptures env U registry target (domains.map (·.instL levels)).reverse locals
      (nativeCaptureSubst arguments) (constantCaptureVariables domains.length) keys footprint)
    (raw : Ctx.SubstEq env U target (nativeCaptureSubst arguments)
      (nativeCaptureSubst newValues) (domains.map (·.instL levels)).reverse)
    (leftTyped : env.HasType U target (mkApps (.const info.ctorName levels) arguments)
      (mkApps (.const demand.family.name levels) (arguments.take info.nparams ++ indices)))
    (rightTyped : env.HasType U target (mkApps (.const info.ctorName levels) newValues)
      (mkApps (.const demand.family.name levels) (newValues.take info.nparams ++ newIndices)))
    {assignedType : VExpr}
    (leftFamily : TypeConversion env U target assignedType
      (mkApps (.const demand.family.name levels) (arguments.take info.nparams ++ indices)))
    (rightFamily : TypeConversion env U target assignedType
      (mkApps (.const demand.family.name levels) (newValues.take info.nparams ++ newIndices)))
    (bounded : ∀ entry ∈ demand.fields, entry.1 < info.numFields)
    (selected : ∀ entry ∈ demand.fields, keys[info.nparams + entry.1]? = some entry.2)
    (admitted : RankedData.Arguments env U (relations env U registry n) target keys arguments newValues)
    (code : RankedData.FamilyRelation env U registry (relations env U registry n) target
      assignedType assignedType demand.family) :
    RankedData.RecordRelation env U registry (relations env U registry n) target
      (mkApps (.const info.ctorName levels) arguments)
      (mkApps (.const info.ctorName levels) newValues) assignedType demand := by
  have origins : ∀ entry ∈ demand.fields,
      Nonempty (RankedData.ProjectionOrigin env U target info demand.family.name entry.1
        (mkApps (.const info.ctorName levels) arguments) assignedType entry.2.domain) ∧
      Nonempty (RankedData.ProjectionOrigin env U target info demand.family.name entry.1
        (mkApps (.const info.ctorName levels) newValues) assignedType entry.2.domain) := by
    intro entry member
    exact captures.literalProjectionOrigins henv hTarget registered shape levelsWF levelCount
      ctorClosed relevant argumentCount newCount (by omega) indexCount newIndexCount raw
      leftTyped rightTyped leftFamily rightFamily (by have := bounded entry member; omega)
      (selected entry member)
  exact RankedData.literalRecord henv hscoped hTarget lookup inert bounded code
    (leftFamily.symm.cast leftTyped) (rightFamily.symm.cast rightTyped)
    (fun entry member => (origins entry member).1) (fun entry member => (origins entry member).2)
    (fun entry member => admitted.selectedRequest (selected entry member))

end Lean4Lean.AnchoredSource.Adapted
