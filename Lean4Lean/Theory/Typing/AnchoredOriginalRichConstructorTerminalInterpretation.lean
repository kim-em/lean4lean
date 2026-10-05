import Lean4Lean.Theory.Typing.AnchoredOriginalLowerCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyPlanInterpretation
import Lean4Lean.Theory.Typing.AnchoredConstructorTerminalInterpretation

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail InductiveSignature
open private prefixRealizedEqual from Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyPlanInterpretation
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 1600000

private theorem constructorCaptureAt (count : Nat) (σ : Subst) (i : Nat) (hi : i < count) :
    nativeCaptureSubst (realizedCaptures count σ) i = σ i := by
  simp [nativeCaptureSubst, realizedCaptures, constantCaptureVariables, hi,
    List.getElem_reverse, List.getElem_range]
  congr 1 <;> omega

/-- The result call is measured against the actual enclosing original rule,
not strictly against the header: a nullary constructor's result is its header. -/
theorem richConstructorTerminal
    {info : VConstant} {demand : ConstructorData (Profile n)}
    {signature : ConstantTelescope (info.type.instL demand.levels)}
    {header : EndpointRef headerEnv U [] (info.type.instL demand.levels) (.sort headerLevel)}
    {field : EndpointRef sourceEnv U source fe ft}
    {major : EndpointRef sourceEnv U source me majorType}
    {headerSource : List VExpr} {context : ContextDerivation headerEnv U headerSource}
    {resultNode : EndpointState headerEnv U headerSource signature.result (.sort resultLevel)}
    (location : Located header resultNode)
    (lineage : location.contextDerivation .nil = context)
    (sourceEq : headerSource = signature.domains.reverse)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (ordered : headerEnv.Ordered) (below : headerEnv ≤ env)
    (capturedOrdered : sourceEnv.Ordered) (initial : List Closure)
    (bank : OriginalLowerCallBank env U registry limit)
    (lookup : env.constants demand.name = some info)
    (levelsWF : ∀ level ∈ demand.levels, level.WF U)
    (levelLength : demand.levels.length = info.uvars)
    (inert : CanonicalDataHead.HeadInert registry demand.name)
    {familyLevels : List VLevel} {familyArguments : List VExpr}
    (resultShape : signature.result = mkApps (.const demand.family.name familyLevels) familyArguments)
    {target : List VExpr} {arguments : List VExpr} {σ τ : Subst}
    {captureFootprint resultFootprint : Footprint} {available : Valuation}
    (saturated : arguments.length = signature.domains.length)
    (captures : FamilyCaptures env U registry target headerSource (List.range arguments.length)
      σ (constantCaptureVariables arguments.length) demand.arguments captureFootprint)
    (resultCode : RichCert headerEnv env U registry target resultNode
      (List.range arguments.length) σ true
      (Profile.singleton (n := n + 1) (.family demand.family)) resultFootprint)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (substitutions : Ctx.SubstEq env U target σ τ headerSource)
    (frame : HeaderBinderFrame header field major env registry target
      context (List.range arguments.length) σ τ available)
    (ambient : (OriginalRichFrame.header capturedOrdered initial frame).Ambient)
    (scheduled : richSchedule .fundamental
      (Closure.close (resultNode.dependencyOrigin ordered)
        ((OriginalRichFrame.header capturedOrdered initial frame).dependencyEnvironment ordered)).cost < limit)
    (resources : (captureFootprint ++ resultFootprint).Available available)
    {support : Profile (n + 1)}
    (typed : (Profile.singleton (n := n + 1) (.ctor demand)).HasType support)
    (code : TypeRelated env U registry target (signature.result.subst σ) (signature.result.subst σ) support) :
    Related env U registry target
      (mkApps (.const demand.name demand.levels) (realizedCaptures arguments.length σ))
      (mkApps (.const demand.name demand.levels) (realizedCaptures arguments.length τ))
      (signature.result.subst σ) (Profile.singleton (n := n + 1) (.ctor demand)) support := by
  cases lineage
  have fields := captures.interpretRichFrame henv hscoped formed frame substitutions
    (fun i need member => resources i need (List.mem_append_left _ member))
  obtain ⟨answer⟩ := bank.computational ordered below .nil location target
    (List.range arguments.length) σ τ available (.header capturedOrdered initial frame) ambient scheduled closed formed
    substitutions (.code resultCode) (fun i need member => resources i need (List.mem_append_right _ member))
  obtain ⟨familyResult⟩ := answer.code henv hscoped formed resultCode.formed
  have reverseBridge := (familyResult.related.symm henv resultCode.formed.wf_value).familyRelation
    (List.mem_singleton_self _)
  have raw : Ctx.SubstEq env U target σ τ (signature.domains.take arguments.length).reverse := by
    simpa only [saturated, List.take_length, sourceEq] using substitutions
  have pair := prefixRealizedEqual henv formed signature (.const lookup levelsWF levelLength)
    (Nat.le_of_eq saturated) raw
  simp only [saturated, List.drop_length, wrapForalls] at pair
  have lengthσ : (realizedCaptures arguments.length σ).length = signature.domains.length := by
    simp [realizedCaptures, constantCaptureVariables, saturated]
  have lengthτ : (realizedCaptures arguments.length τ).length = signature.domains.length := by
    simp [realizedCaptures, constantCaptureVariables, saturated]
  let leftHeader : ConstructorResultHeader env demand.name demand.family.name demand.levels
      (realizedCaptures arguments.length σ) := {
    info := info, lookup := lookup, domains := signature.domains
    familyLevels := familyLevels, familyArguments := familyArguments
    telescope := signature.type_eq.trans (congrArg (wrapForalls signature.domains) resultShape)
    saturated := lengthσ.symm }
  let rightHeader : ConstructorResultHeader env demand.name demand.family.name demand.levels
      (realizedCaptures arguments.length τ) := {
    info := info, lookup := lookup, domains := signature.domains
    familyLevels := familyLevels, familyArguments := familyArguments
    telescope := signature.type_eq.trans (congrArg (wrapForalls signature.domains) resultShape)
    saturated := lengthτ.symm }
  have leftResult : leftHeader.result = signature.result.subst σ := by
    change (mkApps (.const demand.family.name familyLevels) familyArguments).subst
      (nativeCaptureSubst (realizedCaptures arguments.length σ)) = signature.result.subst σ
    rw [← resultShape]
    apply subst_congr_closedN (show signature.result.ClosedN arguments.length from by
      simpa only [leftHeader, List.length_map, realizedCaptures, constantCaptureVariables,
        List.length_reverse, List.length_range, ← resultShape] using leftHeader.resultScoped henv)
    exact constructorCaptureAt arguments.length σ
  have rightResult : rightHeader.result = signature.result.subst τ := by
    change (mkApps (.const demand.family.name familyLevels) familyArguments).subst
      (nativeCaptureSubst (realizedCaptures arguments.length τ)) = signature.result.subst τ
    rw [← resultShape]
    apply subst_congr_closedN (show signature.result.ClosedN arguments.length from by
      simpa only [rightHeader, List.length_map, realizedCaptures, constantCaptureVariables,
        List.length_reverse, List.length_range, ← resultShape] using rightHeader.resultScoped henv)
    exact constructorCaptureAt arguments.length τ
  have pair' : env.IsDefEq U target
      (mkApps (.const demand.name demand.levels) (realizedCaptures arguments.length σ))
      (mkApps (.const demand.name demand.levels) (realizedCaptures arguments.length τ))
      (signature.result.subst σ) := by simpa only [saturated, List.foldr_nil] using pair
  apply Related.constructor henv hscoped typed code
  apply RankedData.literalConstructor henv inert pair' fields leftHeader rightHeader
  · rw [leftResult]
    exact code.familyRelation typed.ctor_family_mem
  · rw [rightResult]
    exact reverseBridge

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
