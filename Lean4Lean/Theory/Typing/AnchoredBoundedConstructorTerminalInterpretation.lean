import Lean4Lean.Theory.Typing.AnchoredConstructorIntroduction
import Lean4Lean.Theory.Typing.AnchoredBoundedFamilyCaptureInterpretation
import Lean4Lean.Theory.Typing.AnchoredBoundedCode
import Lean4Lean.Theory.Typing.AnchoredConstantTelescope

/-! Constructor terminal interpretation uses the original declaration's
literal family result. Its certificate is transferred through that original
formation child, retaining dependent argument demands and both result bridges. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open private capture_vars from Lean4Lean.Theory.Typing.AnchoredNativePartialTelescope
set_option backward.isDefEq.respectTransparency false

private theorem captureVariables_subst (arguments : List VExpr) :
    (constantCaptureVariables arguments.length).map (·.subst (nativeCaptureSubst arguments)) =
      arguments := by
  simpa only [constantCaptureVariables, vars, Nat.zero_add] using capture_vars arguments

/-- Interpret the actual constructor leaf of a declaration telescope plan.
All argument observations and the family-result certificate are finite source
syntax. The semantic input is the theorem for the original earlier header. -/
theorem FamilyCaptures.constructorSupported
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (earlier : ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A → Joint current fuel env U registry Γ l r A)
    {info : VConstant} {demand : ConstructorData (Profile n)}
    {signature : ConstantTelescope (info.type.instL demand.levels)}
    (lookup : env.constants demand.name = some info)
    (levelsWF : ∀ level ∈ demand.levels, level.WF U)
    (levelLength : demand.levels.length = info.uvars)
    (inert : CanonicalDataHead.HeadInert registry demand.name)
    {familyLevels : List VLevel} {familyArguments : List VExpr}
    (resultShape : signature.result = mkApps (.const demand.family.name familyLevels) familyArguments)
    (typeFormation : sourceEnv.IsDefEqStrong U [] (info.type.instL demand.levels)
      (info.type.instL demand.levels) (.sort typeLevel))
    {target : List VExpr} {arguments newValues : List VExpr}
    {captureFootprint resultFootprint : Footprint} {available : Valuation}
    (saturated : arguments.length = signature.domains.length)
    (newLength : newValues.length = arguments.length)
    (captures : Adapted.FamilyCaptures env U registry target signature.domains.reverse (List.range arguments.length)
      (nativeCaptureSubst arguments) (constantCaptureVariables arguments.length)
      demand.arguments captureFootprint)
    (capturesBound : captures.nativeDepth current ≤ fuel)
    (resultCode : CodeCert env U registry target (List.range arguments.length)
      (nativeCaptureSubst arguments) signature.result
      (Profile.singleton (n := n + 1) (.family demand.family)) resultFootprint)
    (resultBound : resultCode.nativeDepth current ≤ fuel)
    (hTarget : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (raw : Ctx.SubstEq env U target (nativeCaptureSubst arguments) (nativeCaptureSubst newValues)
      signature.domains.reverse)
    (fits : PairedFits current fuel env U registry signature.domains.reverse target (List.range arguments.length)
      (nativeCaptureSubst arguments) (nativeCaptureSubst newValues) available)
    (resources : (captureFootprint ++ resultFootprint).Available available)
    {support : Profile (n + 1)}
    (typed : (Profile.singleton (n := n + 1) (.ctor demand)).HasType support)
    (code : TypeRelated env U registry target (signature.result.subst (nativeCaptureSubst arguments))
      (signature.result.subst (nativeCaptureSubst arguments)) support) :
    Related env U registry target
      (mkApps (.const demand.name demand.levels) arguments)
      (mkApps (.const demand.name demand.levels) newValues)
      (signature.result.subst (nativeCaptureSubst arguments))
      (Profile.singleton (n := n + 1) (.ctor demand)) support := by
  have sourceContext := signature.prefixCtxStrong typeFormation signature.domains.length
  rw [List.take_length] at sourceContext
  have fields := FamilyCaptures.interpret henv hscoped hsource earlier captures capturesBound
    sourceContext hTarget closed raw fits
    (fun i need member => resources i need (List.mem_append_left _ member))
  have rightVars :
      (constantCaptureVariables arguments.length).map (·.subst (nativeCaptureSubst newValues)) = newValues := by
    rw [← newLength, captureVariables_subst]
  rw [captureVariables_subst, rightVars] at fields
  obtain ⟨resultLevel, originalResult⟩ := (signature.prefixFormation typeFormation signature.domains.length).1
  simp only [List.take_length, List.drop_length, wrapForalls] at originalResult
  obtain ⟨familyResult⟩ := Transfer.codeCertificate henv hscoped hTarget closed
    ((earlier originalResult) target (List.range arguments.length)
      (nativeCaptureSubst arguments) (nativeCaptureSubst newValues) available
      closed hTarget raw fits).1 resultCode resultBound
    (fun i need member => resources i need (List.mem_append_right _ member))
  have reverseBridge := (familyResult.related.symm henv resultCode.formed.wf_value).familyRelation
    (List.mem_singleton_self _)
  have pair := (signature.prefixArgumentsEqual henv hTarget
    (.const lookup levelsWF levelLength) (Nat.le_refl _) saturated (newLength.trans saturated)
    (by simpa only [List.take_length] using raw)).1
  simp only [List.drop_length, wrapForalls] at pair
  let leftHeader : ConstructorResultHeader env demand.name demand.family.name demand.levels arguments := {
    info := info, lookup := lookup, domains := signature.domains
    familyLevels := familyLevels, familyArguments := familyArguments
    telescope := signature.type_eq.trans (congrArg (wrapForalls signature.domains) resultShape)
    saturated := saturated.symm }
  let rightHeader : ConstructorResultHeader env demand.name demand.family.name demand.levels newValues := {
    info := info, lookup := lookup, domains := signature.domains
    familyLevels := familyLevels, familyArguments := familyArguments
    telescope := signature.type_eq.trans (congrArg (wrapForalls signature.domains) resultShape)
    saturated := saturated.symm.trans newLength.symm }
  have leftResult : leftHeader.result = signature.result.subst (nativeCaptureSubst arguments) := by
    simp only [leftHeader, ConstructorResultHeader.result, resultShape, nativeCaptureSubst_spec]
  have rightResult : rightHeader.result = signature.result.subst (nativeCaptureSubst newValues) := by
    simp only [rightHeader, ConstructorResultHeader.result, resultShape, nativeCaptureSubst_spec]
  apply Related.constructor henv hscoped typed code
  apply RankedData.literalConstructor henv inert pair fields leftHeader rightHeader
  · rw [leftResult]
    exact code.familyRelation typed.ctor_family_mem
  · rw [rightResult]
    exact reverseBridge

end Lean4Lean.AnchoredSource.Adapted.Staged
