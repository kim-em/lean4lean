import Lean4Lean.Theory.Typing.AnchoredCapturedLiteralRecord
import Lean4Lean.Theory.Typing.AnchoredRegisteredCapturedRecord
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceRealization
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyBinder
import Lean4Lean.Theory.Typing.AnchoredFamilyCaptureDomains

/-! Connect literal primitive-projection origins to the exact requests
retained by a constructor capture tree. Both endpoint field types are
aligned through the original declared domain and paired substitution. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalRecordSource
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

private theorem selectedCaptureAt (count : Nat) (σ : Subst) (i : Nat) (hi : i < count) :
    nativeCaptureSubst (realizedCaptures count σ) i = σ i := by
  simp [nativeCaptureSubst, realizedCaptures, constantCaptureVariables, hi,
    List.getElem_reverse, List.getElem_range]
  congr 1 <;> omega

/-- A header frame's arbitrary realization can be restricted to its actual
finite declaration prefix without changing any capture or resource. -/
noncomputable def FamilyCaptures.atRealizedPrefix
    (captures : FamilyCaptures env U registry target source locals σ expressions keys footprint)
    (scope : CtxClosed source) :
    FamilyCaptures env U registry target source locals
      (nativeCaptureSubst (realizedCaptures source.length σ)) expressions keys footprint :=
  captures.realizePrefix scope _ (fun i hi => (selectedCaptureAt source.length σ i hi).symm)

open private substitution_of_lookups from Lean4Lean.Theory.Typing.AnchoredFamilyCaptureSubstitution

/-- Paired raw substitutions restrict to the same actual finite prefix;
this uses source scope, not equality of substitutions outside that prefix. -/
theorem realizedCaptureSubstitution
    (henv : env.Ordered)
    (sourceFormed : OnCtx source (env.IsType U))
    (raw : Ctx.SubstEq env U target σ τ source) :
    Ctx.SubstEq env U target
      (nativeCaptureSubst (realizedCaptures source.length σ))
      (nativeCaptureSubst (realizedCaptures source.length τ)) source := by
  apply substitution_of_lookups sourceFormed
  intro index type lookup
  have pair := raw.lookup lookup
  have sameType := subst_congr_closedN ((CtxWF.closed henv sourceFormed).lookup lookup)
    (fun i hi => selectedCaptureAt source.length σ i hi)
  simpa only [selectedCaptureAt source.length σ index lookup.lt,
    selectedCaptureAt source.length τ index lookup.lt, sameType] using pair

theorem FamilyCaptures.selectedLiteralProjectionOrigins
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
    {locals : List Nat} {expressions : List VExpr} {keys : List (DataRequest (Profile n))} {footprint : Footprint}
    (captures : FamilyCaptures env U registry target (domains.map (·.instL levels)).reverse locals
      (nativeCaptureSubst arguments) expressions keys footprint)
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
    (capturePosition : Nat)
    (keyAt : keys[capturePosition]? = some key)
    (expressionAt : expressions[capturePosition]? =
      some (.bvar (domains.length - 1 - (info.nparams + index)))) :
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
  have domainLookup := Lookup.reverse_append (domains.map (·.instL levels)) []
    (info.nparams + index) (by simpa only [List.length_map] using fieldBound)
  simp only [List.append_nil, List.length_map] at domainLookup
  simp only [List.getElem_map] at domainLookup
  have alignment := captures.lookupDomain keyAt expressionAt domainLookup
  have domainEq : ((domains[info.nparams + index].instL levels).liftN
      (domains.length - (info.nparams + index))).subst (nativeCaptureSubst arguments) =
      (domains[info.nparams + index].instL levels).subst
        (nativeCaptureSubst (arguments.take (info.nparams + index))) := by
    rw [← lift'_consN_skipN (k := 0), subst_lift']
    simp only [Lift.consN]
    rw [← argumentCount, nativeCaptureSubst_prefix _ _ (by omega)]
  rw [domainEq] at alignment
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

theorem FamilyCaptures.literalRecordFromSelectedCaptures
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
    (relevant : demand.fields ≠ [] → (info.resultLevel.inst levels).IsNeverZero)
    {arguments newValues indices newIndices : List VExpr}
    (argumentCount : arguments.length = domains.length)
    (newCount : newValues.length = domains.length)
    (indexCount : indices.length = info.nindices)
    (newIndexCount : newIndices.length = info.nindices)
    {locals : List Nat} {footprint : Footprint}
    (captures : FamilyCaptures env U registry target (domains.map (·.instL levels)).reverse locals
      (nativeCaptureSubst arguments)
      (demand.fields.map fun entry => .bvar (domains.length - 1 - (info.nparams + entry.1)))
      (demand.fields.map (·.2)) footprint)
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
    (admitted : RankedData.Arguments env U (relations env U registry n) target
      (demand.fields.map (·.2))
      (demand.fields.map fun entry => nativeCaptureSubst arguments
        (domains.length - 1 - (info.nparams + entry.1)))
      (demand.fields.map fun entry => nativeCaptureSubst newValues
        (domains.length - 1 - (info.nparams + entry.1))))
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
    obtain ⟨position, bound, rfl⟩ := List.mem_iff_getElem.mp member
    exact captures.selectedLiteralProjectionOrigins henv hTarget registered shape levelsWF levelCount
      ctorClosed (relevant (List.ne_nil_of_mem (List.getElem_mem bound)))
      argumentCount newCount (by omega) indexCount newIndexCount raw
      leftTyped rightTyped leftFamily rightFamily
      (by have := bounded demand.fields[position] (List.getElem_mem bound); omega)
      position (by simp [bound]) (by simp [bound])
  exact RankedData.literalRecord henv hscoped hTarget lookup inert bounded code
    (leftFamily.symm.cast leftTyped) (rightFamily.symm.cast rightTyped)
    (fun entry member => (origins entry member).1) (fun entry member => (origins entry member).2)
    (fun entry member => by
      have fieldBound : info.nparams + entry.1 < domains.length := by
        have := bounded entry member; omega
      have leftBound : info.nparams + entry.1 < arguments.length := by omega
      have rightBound : info.nparams + entry.1 < newValues.length := by omega
      refine ⟨arguments[info.nparams + entry.1], newValues[info.nparams + entry.1],
        List.getElem?_eq_getElem leftBound, List.getElem?_eq_getElem rightBound, ?_⟩
      have actual := admitted.map_member member
      have leftIndex : domains.length - 1 - (info.nparams + entry.1) < arguments.length := by omega
      have rightIndex : domains.length - 1 - (info.nparams + entry.1) < newValues.length := by omega
      have leftReverse : arguments.length - 1 - (domains.length - 1 -
          (info.nparams + entry.1)) = info.nparams + entry.1 := by omega
      have rightReverse : newValues.length - 1 - (domains.length - 1 -
          (info.nparams + entry.1)) = info.nparams + entry.1 := by omega
      simpa only [nativeCaptureSubst, dif_pos leftIndex, dif_pos rightIndex,
        leftReverse, rightReverse] using actual)


theorem FamilyCaptures.registeredLiteralRecordSelected
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {projection : VProjectionInfo} {demand : RecordData (Profile n)}
    (registered : env.projections demand.family.name projection)
    (projectionLookup : registry.projections demand.family.name = some projection)
    (unindexed : projection.nindices = 0)
    (inert : CanonicalDataHead.HeadInert registry projection.ctorName)
    {info : VConstant} {levels : List VLevel}
    {signature : ConstantTelescope (info.type.instL levels)}
    (lookup : env.constants projection.ctorName = some info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelLength : levels.length = info.uvars)
    (relevant : demand.fields ≠ [] → (projection.resultLevel.inst levels).IsNeverZero)
    {familyLevels : List VLevel} {familyArguments : List VExpr}
    (resultShape : signature.result = mkApps (.const demand.family.name familyLevels) familyArguments)
    {arguments newValues : List VExpr}
    {locals : List Nat} {footprint : Footprint}
    (saturated : arguments.length = signature.domains.length)
    (newLength : newValues.length = arguments.length)
    (captures : FamilyCaptures env U registry target signature.domains.reverse locals
      (nativeCaptureSubst arguments)
      (demand.fields.map fun entry => .bvar
        (arguments.length - 1 - (projection.nparams + entry.1)))
      (demand.fields.map (·.2)) footprint)
    (raw : Ctx.SubstEq env U target (nativeCaptureSubst arguments)
      (nativeCaptureSubst newValues) signature.domains.reverse)
    (bounded : ∀ entry ∈ demand.fields, entry.1 < projection.numFields)
    (admitted : RankedData.Arguments env U (relations env U registry n) target
      (demand.fields.map (·.2))
      (demand.fields.map fun entry => nativeCaptureSubst arguments
        (arguments.length - 1 - (projection.nparams + entry.1)))
      (demand.fields.map fun entry => nativeCaptureSubst newValues
        (arguments.length - 1 - (projection.nparams + entry.1))))
    (code : RankedData.FamilyRelation env U registry (relations env U registry n) target
      (signature.result.subst (nativeCaptureSubst arguments))
      (signature.result.subst (nativeCaptureSubst arguments)) demand.family) :
    RankedData.RecordRelation env U registry (relations env U registry n) target
      (mkApps (.const projection.ctorName levels) arguments)
      (mkApps (.const projection.ctorName levels) newValues)
      (signature.result.subst (nativeCaptureSubst arguments)) demand := by
  have sameInfo : info = { uvars := projection.uvars, type := projection.ctorType } :=
    Option.some.inj (lookup.symm.trans (henv.projectionConstructor registered))
  have levelCount : levels.length = projection.uvars := by simpa only [sameInfo] using levelLength
  let leftHeader : ConstructorResultHeader env projection.ctorName demand.family.name levels arguments := {
    info := info, lookup := lookup, domains := signature.domains
    familyLevels := familyLevels, familyArguments := familyArguments
    telescope := signature.type_eq.trans (congrArg (wrapForalls signature.domains) resultShape)
    saturated := saturated.symm }
  let rightHeader : ConstructorResultHeader env projection.ctorName demand.family.name levels newValues := {
    info := info, lookup := lookup, domains := signature.domains
    familyLevels := familyLevels, familyArguments := familyArguments
    telescope := signature.type_eq.trans (congrArg (wrapForalls signature.domains) resultShape)
    saturated := saturated.symm.trans newLength.symm }
  have leftResult : leftHeader.result = signature.result.subst (nativeCaptureSubst arguments) := by
    simp only [leftHeader, ConstructorResultHeader.result, resultShape, nativeCaptureSubst_spec]
  have rightResult : rightHeader.result = signature.result.subst (nativeCaptureSubst newValues) := by
    simp only [rightHeader, ConstructorResultHeader.result, resultShape, nativeCaptureSubst_spec]
  have leftFamily := (leftHeader.registered_result henv registered unindexed levelCount).2
  have rightFamily := (rightHeader.registered_result henv registered unindexed levelCount).2
  rw [leftResult] at leftFamily
  rw [rightResult] at rightFamily
  obtain ⟨domains, result, shape, layout, domainShape, _⟩ := leftHeader.registered_domains henv registered
  change signature.domains = domains.map (·.instL levels) at domainShape
  have argumentCount : arguments.length = domains.length := by
    simpa only [domainShape, List.length_map] using saturated
  obtain ⟨pair, resultPath⟩ := signature.prefixArgumentsEqual henv hTarget
    (.const lookup levelsWF levelLength) (Nat.le_refl _) saturated (newLength.trans saturated)
    (by simpa only [List.take_length] using raw)
  simp only [List.drop_length, wrapForalls, List.foldr_nil] at pair resultPath
  have leftTyped := pair.hasType.1
  have rightTyped := resultPath.cast pair.hasType.2
  rw [leftFamily] at leftTyped
  rw [rightFamily] at rightTyped
  have ctorClosed : projection.ctorType.Closed := by
    obtain ⟨level, formation⟩ := henv.constWF (henv.projectionConstructor registered)
    exact VExpr.WF.closedN henv ⟨_, formation⟩ trivial
  apply FamilyCaptures.literalRecordFromSelectedCaptures henv hscoped hTarget registered projectionLookup
    inert shape layout levelsWF levelCount ctorClosed relevant argumentCount
    (newLength.trans argumentCount) (indices := []) (newIndices := [])
    (by simpa only [List.length_nil] using unindexed.symm)
    (by simpa only [List.length_nil] using unindexed.symm)
    (by simpa only [domainShape, argumentCount] using captures)
    (by simpa only [domainShape] using raw)
    (by simpa only [List.append_nil] using leftTyped)
    (by simpa only [List.append_nil, HasType] using rightTyped)
    (by rw [List.append_nil, leftFamily]; exact .refl)
    (by simpa only [List.append_nil, rightFamily] using resultPath)
    bounded (by simpa only [argumentCount] using admitted) code


end Lean4Lean.AnchoredSource.Adapted
