import Lean4Lean.Theory.Typing.AnchoredCapturedLiteralRecord
import Lean4Lean.Theory.Typing.AnchoredConstructorRecordMetadata
import Lean4Lean.Theory.Typing.AnchoredConstantTelescope

/-! The record terminal consumes the actual registered constant header and
existing capture admissions. Constructor typings, literal family parameters,
field origins and dependent conversions are all derived here. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem FamilyCaptures.registeredLiteralRecord
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
    (relevant : (projection.resultLevel.inst levels).IsNeverZero)
    {familyLevels : List VLevel} {familyArguments : List VExpr}
    (resultShape : signature.result = mkApps (.const demand.family.name familyLevels) familyArguments)
    {arguments newValues : List VExpr} {keys : List (DataRequest (Profile n))}
    {locals : List Nat} {footprint : Footprint}
    (saturated : arguments.length = signature.domains.length)
    (newLength : newValues.length = arguments.length)
    (captures : FamilyCaptures env U registry target signature.domains.reverse locals
      (nativeCaptureSubst arguments) (constantCaptureVariables arguments.length) keys footprint)
    (raw : Ctx.SubstEq env U target (nativeCaptureSubst arguments)
      (nativeCaptureSubst newValues) signature.domains.reverse)
    (bounded : ∀ entry ∈ demand.fields, entry.1 < projection.numFields)
    (selected : ∀ entry ∈ demand.fields, keys[projection.nparams + entry.1]? = some entry.2)
    (admitted : RankedData.Arguments env U (relations env U registry n) target keys arguments newValues)
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
  apply FamilyCaptures.literalRecordFromArguments henv hscoped hTarget registered projectionLookup
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
    bounded selected admitted code

end Lean4Lean.AnchoredSource.Adapted
