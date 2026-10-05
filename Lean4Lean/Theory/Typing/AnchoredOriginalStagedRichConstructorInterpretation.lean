import Lean4Lean.Theory.Typing.AnchoredOriginalRichRecordOrigins
import Lean4Lean.Theory.Typing.AnchoredOriginalStagedLowerCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyPlanInterpretation
import Lean4Lean.Theory.Typing.AnchoredConstructorTerminalInterpretation
import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstructorBinder

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail InductiveSignature
open private prefixRealizedEqual from Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyPlanInterpretation
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 1600000

private theorem stagedConstructorCaptureAt (count : Nat) (σ : Subst) (i : Nat) (hi : i < count) :
    nativeCaptureSubst (realizedCaptures count σ) i = σ i := by
  simp [nativeCaptureSubst, realizedCaptures, constantCaptureVariables, hi,
    List.getElem_reverse, List.getElem_range]
  congr 1 <;> omega

/-- The result call is measured against the actual enclosing original rule,
not strictly against the header: a nullary constructor's result is its header. -/
theorem richConstructorTerminalStaged
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
    (bank : StagedOriginalLowerCallBank env U registry stage limit)
    (callStage : Nat) (headerStage : SourceAtStage callStage headerEnv)
    (capturedStage : SourceAtStage callStage sourceEnv)
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
    (scheduled : Prod.Lex Nat.lt Nat.lt (callStage, richSchedule .fundamental
      (Closure.close (resultNode.dependencyOrigin ordered)
        ((OriginalRichFrame.header capturedOrdered initial frame).dependencyEnvironment ordered)).cost) (stage, limit))
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
  obtain ⟨answer⟩ := bank.computational callStage ordered below .nil location target
    (List.range arguments.length) σ τ available (.header capturedOrdered initial frame) ambient (by
      change (RawOriginalRichFrame.header capturedOrdered initial frame).AllSources _
      rw [RawOriginalRichFrame.AllSources.eq_def]
      exact ⟨headerStage, capturedStage⟩) scheduled closed formed
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
    exact stagedConstructorCaptureAt arguments.length σ
  have rightResult : rightHeader.result = signature.result.subst τ := by
    change (mkApps (.const demand.family.name familyLevels) familyArguments).subst
      (nativeCaptureSubst (realizedCaptures arguments.length τ)) = signature.result.subst τ
    rw [← resultShape]
    apply subst_congr_closedN (show signature.result.ClosedN arguments.length from by
      simpa only [rightHeader, List.length_map, realizedCaptures, constantCaptureVariables,
        List.length_reverse, List.length_range, ← resultShape] using rightHeader.resultScoped henv)
    exact stagedConstructorCaptureAt arguments.length τ
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

/-! Native constructor plans retain every original domain and result occurrence.
The sole original result call is paid by the enclosing constant's header reserve;
future binders preserve its exact original context environment. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail InductiveSignature
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem RichConstructorPlan.supportedStaged
    {info : VConstant} {header : EndpointRef headerEnv U [] (info.type.instL levels) (.sort headerLevel)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldAssigned}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {signature : ConstantTelescope (info.type.instL levels)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (ordered : headerEnv.Ordered) (capturedOrdered : sourceEnv.Ordered)
    (headerBelow : headerEnv ≤ env) (capturedBelow : sourceEnv ≤ env)
    (bank : StagedOriginalLowerCallBank env U registry stage limit)
    (callStage : Nat) (headerStage : SourceAtStage callStage headerEnv)
    (stageLess : callStage < stage) (capturedStage : SourceAtStage callStage sourceEnv)
    (lookup : env.constants name = some info)
    (levelsWF : ∀ level ∈ levels, level.WF U) (levelCount : levels.length = info.uvars)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    {target arguments headerSource} {context : ContextDerivation headerEnv U headerSource}
    {σ τ : Subst} {demand support : Profile n} {footprint available}
    (plan : RichConstructorPlan env U registry target header name levels signature context σ arguments demand footprint)
    (formed : OnCtx target (env.IsType U)) (bound : arguments.length ≤ signature.domains.length)
    (sourceEq : headerSource = (signature.domains.take arguments.length).reverse)
    (closed : available.AtomClosed) (substitutions : Ctx.SubstEq env U target σ τ headerSource)
    (frame : HeaderBinderFrame header field major env registry target context (List.range arguments.length) σ τ available)
    (exactEnvironment : frame.dependencyEnvironment ordered capturedOrdered [] = context.dependencyClosures ordered)
    (resources : footprint.Available available) (typed : demand.HasType support)
    (code : TypeRelated env U registry target
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst σ)
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst σ) support) :
    Related env U registry target (mkApps (.const name levels) (realizedCaptures arguments.length σ))
      (mkApps (.const name levels) (realizedCaptures arguments.length τ))
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst σ) demand support := by
  match n, demand, footprint, plan with
  | _ + 1, _, _, .terminal saturated resultShape relevant resultNode resultLocation resultLineage captures resultCode =>
    have fullSource : headerSource = signature.domains.reverse := by
      simpa only [saturated, List.take_length] using sourceEq
    have scheduled : Prod.Lex Nat.lt Nat.lt (callStage, richSchedule .fundamental
        (Closure.close (resultNode.dependencyOrigin ordered)
          ((OriginalRichFrame.header capturedOrdered [] frame).dependencyEnvironment ordered)).cost) (stage, limit) :=
      Prod.Lex.left _ _ stageLess
    rw [saturated, List.drop_length] at code ⊢
    simp only [wrapForalls, List.foldr_nil] at code ⊢
    have frameAmbient : (OriginalRichFrame.header capturedOrdered [] frame).Ambient := by
      change (RawOriginalRichFrame.header capturedOrdered [] frame).Ambient
      rw [RawOriginalRichFrame.Ambient.eq_def]
      exact ⟨headerBelow, capturedBelow⟩
    have terminal := richConstructorTerminalStaged (arguments := arguments) (context := context) resultLocation resultLineage fullSource henv hscoped ordered headerBelow capturedOrdered [] bank callStage headerStage capturedStage
      lookup levelsWF levelCount ⟨notDefinition, notNative, Or.inr notQuotient⟩ resultShape saturated
      captures resultCode formed closed substitutions frame
      frameAmbient
      scheduled resources typed code
    simpa only [saturated] using terminal
  | _ + 1, _, _, .terminalRecord registered projectionLookup constructorName bounded saturated
      resultShape resultNode resultLocation resultLineage captures resultCode origins =>
    have fullSource : headerSource = signature.domains.reverse := by
      simpa only [saturated, List.take_length] using sourceEq
    rw [saturated, List.drop_length] at code ⊢
    simp only [wrapForalls, List.foldr_nil] at code ⊢
    cases constructorName
    have terminal := richRecordTerminalFromOrigins (arguments := arguments) (context := context)
      fullSource resultNode henv hscoped headerBelow registered projectionLookup
      lookup levelsWF levelCount ⟨notDefinition, notNative, Or.inr notQuotient⟩ bounded
      resultShape saturated captures formed substitutions frame
      (fun i need member => resources i need (List.mem_append_left _ member)) origins typed code
    simpa only [saturated] using terminal
  | _ + 1, _, _, .binder origin original location lineage domainCode guard body pack covered =>
    apply RichConstructorPlanSupported.binder henv hscoped headerBelow ordered capturedOrdered
      (fun child formed bound sourceEq closed substitutions frame exactEnvironment resources typed code =>
        child.supportedStaged henv hscoped ordered capturedOrdered headerBelow capturedBelow bank callStage headerStage stageLess capturedStage
          lookup levelsWF levelCount notDefinition notNative notQuotient
          formed bound sourceEq closed substitutions frame exactEnvironment resources typed code)
      origin original location lineage domainCode guard body pack covered formed sourceEq closed
      substitutions frame exactEnvironment resources typed code
  | _, _, _, .view child change =>
    have inverse := change.inverse henv
    have before := child.supportedStaged henv hscoped ordered capturedOrdered headerBelow capturedBelow bank callStage headerStage stageLess capturedStage
      lookup levelsWF levelCount notDefinition notNative notQuotient
      formed bound sourceEq closed substitutions frame exactEnvironment resources
      (inverse.mapType_typed typed) (inverse.codeMap henv hscoped code)
    exact (change.termMap henv hscoped formed before).retag henv typed code
  | _ + 1, _, _, .pad child =>
    have before := child.supportedStaged henv hscoped ordered capturedOrdered headerBelow capturedBelow bank callStage headerStage stageLess capturedStage
      lookup levelsWF levelCount notDefinition notNative notQuotient
      formed bound sourceEq closed substitutions frame exactEnvironment resources typed.pad_inv (code.down henv)
    exact (before.pad henv).retag henv typed code
termination_by (n, sizeOf plan)
decreasing_by all_goals simp_wf; omega

theorem RichConstructorPlan.bareSupportedStaged
    {info : VConstant} {header : EndpointRef headerEnv U [] (info.type.instL levels) (.sort headerLevel)}
    {signature : ConstantTelescope (info.type.instL levels)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (ordered : headerEnv.Ordered) (headerBelow : headerEnv ≤ env)
    (bank : StagedOriginalLowerCallBank env U registry stage limit)
    (callStage : Nat) (headerStage : SourceAtStage callStage headerEnv)
    (stageLess : callStage < stage)
    (lookup : env.constants name = some info)
    (levelsWF : ∀ level ∈ levels, level.WF U) (levelCount : levels.length = info.uvars)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    (typeClosed : info.type.Closed) (formed : OnCtx target (env.IsType U))
    (plan : RichConstructorPlan env U registry target header name levels signature .nil σ [] demand [])
    (typed : demand.HasType support)
    (code : TypeRelated env U registry target (info.type.instL levels) (info.type.instL levels) support) :
    Related env U registry target (.const name levels) (.const name levels) (info.type.instL levels) demand support := by
  have residual : (wrapForalls (signature.domains.drop 0) signature.result).subst σ = info.type.instL levels := by
    rw [List.drop_zero, ← signature.type_eq]
    exact typeClosed.instL.subst_eq .zero
  have emptyClosed : Valuation.AtomClosed (fun _ => []) := by intro _ _ member; cases member
  have result := plan.supportedStaged (field := header) (major := header) henv hscoped ordered ordered
    headerBelow headerBelow bank callStage headerStage stageLess headerStage lookup levelsWF levelCount
    notDefinition notNative notQuotient formed (Nat.zero_le _) rfl emptyClosed
    (τ := σ) .nil (.captured .nil) rfl (by intro _ _ member; cases member) typed
    (by simpa only [List.length_nil, residual] using code)
  simpa only [realizedCaptures, constantCaptureVariables, List.length_nil, List.range_zero,
    List.reverse_nil, List.map_nil, mkApps, List.foldl_nil, residual] using result

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource