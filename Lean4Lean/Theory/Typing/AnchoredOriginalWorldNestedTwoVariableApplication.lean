import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNestedConstantReturn
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeTwoVariableApplication

/-! Consume a returned nested constant function in the two real caller
applications. Canonical openings have already been returned in order; this
assembly preserves their actual annotation and never reopens a flattened leaf. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
open private outputPathControlled from Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeTwoVariableApplication
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem compileReturnedTwoVariableArgumentsWorld
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (inner : RichAppOrigin root env registry target source sourceLocals sourceσ (.const name levels) (.bvar 1))
    (outer : RichAppOrigin root env registry target source sourceLocals sourceσ
      (.app (.const name levels) (.bvar 1)) (.bvar 0))
    {sourceAvailable : Valuation}
    (sourceControls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length))
    (innerAnswer : RetainedApplicationAnswers inner sourceControls frontier sourceτ
      sourceAvailable)
    (outerAnswer : RetainedApplicationAnswers outer sourceControls frontier sourceτ
      sourceAvailable)
    (innerPath : GeneralOutputPath env U registry target inner.output
      (show Atom (outer.rank+1) from .fn outer.key outer.output))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (callerClosed : callerAvailable.AtomClosed)
    {firstDomain : EndpointState callerEnv U callerSource firstA (.sort firstU)}
    {firstBody : EndpointState callerEnv U (firstA :: callerSource) firstB (.sort firstV)}
    {callerConstant : EndpointState callerEnv U callerSource (.const name nextLevels) (.forallE firstA firstB)}
    {callerFirst : EndpointState callerEnv U callerSource (.bvar firstIndex) firstA}
    {firstResult : EndpointState callerEnv U callerSource (firstB.inst (.bvar firstIndex)) (.sort firstV)}
    (firstHU : firstU.WF U) (firstHV : firstV.WF U)
    {secondDomain : EndpointState callerEnv U callerSource secondA (.sort secondU)}
    {secondBody : EndpointState callerEnv U (secondA :: callerSource) secondB (.sort secondV)}
    {callerFunction : EndpointState callerEnv U callerSource (.app (.const name nextLevels) (.bvar firstIndex))
      (.forallE secondA secondB)}
    {callerSecond : EndpointState callerEnv U callerSource (.bvar secondIndex) secondA}
    {secondResult : EndpointState callerEnv U callerSource (secondB.inst (.bvar secondIndex)) (.sort secondV)}
    (secondHU : secondU.WF U) (secondHV : secondV.WF U)
    (functionRoute : PrefixRoute callerEnv U callerSource (.app (.const name nextLevels) (.bvar firstIndex))
      callerFunction (.app firstHU firstHV firstDomain firstBody callerConstant callerFirst firstResult))
    (firstAnchor : sourceτ 1 = callerσ firstIndex)
    (secondAnchor : sourceτ 0 = callerσ secondIndex)
    (controls : OriginalWorldControls strata fundingEnv)
    (constant : RichGradedResult callerEnv env U registry target callerConstant callerLocals callerσ callerAvailable (Profile.fn inner.key inner.output))
    (constantControlled : ControlledStoredQuery controls frontier (.observation constant.observation))
    (first : RichGradedResult callerEnv env U registry target callerFirst callerLocals callerσ callerAvailable inner.rawInput)
    (firstReady : ControlledStoredQuery controls frontier (.observation first.observation))
    (second : RichGradedResult callerEnv env U registry target callerSecond callerLocals callerσ callerAvailable outer.rawInput)
    (secondReady : ControlledStoredQuery controls frontier (.observation second.observation))
    (sorted : (Profile.singleton outer.output).HasType (.sort relevant)) :
    ∃ factor : RichApplicationOperandFactor env registry target callerFunction callerSecond
        callerLocals callerσ callerAvailable outer.output,
    ∃ operandReady : factor.Controlled controls frontier,
    ∃ footprint, ∃ certificate : RichCert callerEnv env U registry target
        (.app secondHU secondHV secondDomain secondBody callerFunction callerSecond secondResult)
        callerLocals callerσ relevant (.singleton outer.output) footprint,
    ∃ ready : ControlledStoredQuery controls frontier (.certificate certificate),
      footprint.Available callerAvailable ∧
      ready.annotation.worlds ⊆
        operandReady.function.annotation.worlds ++ operandReady.argument.annotation.worlds := by
  have firstAdmitted : Admitted env U registry target inner.key (callerσ firstIndex) (callerσ firstIndex) := by
    simpa only [subst_bvar, firstAnchor] using innerAnswer.admitted
  have secondAdmitted : Admitted env U registry target outer.key (callerσ secondIndex) (callerσ secondIndex) := by
    simpa only [subst_bvar, secondAnchor] using outerAnswer.admitted
  obtain ⟨applied, appliedReady, _, _, _⟩ := RichGradedResult.appControlled henv hscoped formed callerClosed
    firstDomain firstBody firstResult firstHU firstHV constant first inner.arguments firstAdmitted
    controls constantControlled firstReady
  obtain ⟨function, ⟨functionReady⟩⟩ := outputPathControlled henv hscoped formed innerPath applied appliedReady
  let restored := function.restoreRoute functionRoute
  let restoredReady : ControlledStoredQuery controls frontier (.observation restored.observation) := {
    annotation := .route functionRoute functionReady.annotation
    within := by
      intro control active
      simpa only [restored, RichGradedResult.restoreRoute, StoredOriginalQuery.headDepth, RichObs.headDepth]
        using functionReady.within control active
    sponsored := functionReady.sponsored }
  obtain ⟨factor, operandReady, _, _, _⟩ := RichGradedResult.appControlledOperands
    henv hscoped formed callerClosed secondDomain secondBody secondResult secondHU secondHV
    restored second outer.arguments secondAdmitted controls restoredReady secondReady
  let applied := factor.graded secondDomain secondBody secondResult secondHU secondHV
  let appliedReady := operandReady.graded secondDomain secondBody secondResult secondHU secondHV
  obtain ⟨footprint, certificate, ready, resources, worlds⟩ :=
    applied.code_controlled henv controls appliedReady sorted
  exact ⟨factor, operandReady, footprint, certificate, ready, resources, worlds⟩

/-- Execute the inner closed equality, restore the outer charge, then consume
that exact returned function in both original caller applications. -/
theorem RichRecipeContext.compileNestedTwoVariableApplicationWorld
    {P : VEnv → Prop}
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target recipeSource recipeLocals recipeSubstitution
      recipeExpression recipeRelevant recipeProfile recipeFootprint}
    (pending : RichRecipeContext input recipe)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (inner : RichAppOrigin root env registry target source sourceLocals sourceσ (.const name levels) (.bvar 1))
    (outer : RichAppOrigin root env registry target source sourceLocals sourceσ
      (.app (.const name levels) (.bvar 1)) (.bvar 0))
    {sourceAvailable : Valuation}
    (sourceControls : OriginalWorldControls input.strata sourceEnv)
    (frontier : List (World input.strata.rules.length))
    (innerAnswer : RetainedApplicationAnswers inner sourceControls frontier sourceτ
      sourceAvailable)
    (outerAnswer : RetainedApplicationAnswers outer sourceControls frontier sourceτ
      sourceAvailable)
    (innerPath : GeneralOutputPath env U registry target inner.output
      (show Atom (outer.rank+1) from .fn outer.key outer.output))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (callerClosed : callerAvailable.AtomClosed)
    {firstDomain : EndpointState callerEnv U callerSource firstA (.sort firstU)}
    {firstBody : EndpointState callerEnv U (firstA :: callerSource) firstB (.sort firstV)}
    {callerConstant : EndpointState callerEnv U callerSource (.const name nextLevels) (.forallE firstA firstB)}
    {callerFirst : EndpointState callerEnv U callerSource (.bvar firstIndex) firstA}
    {firstResult : EndpointState callerEnv U callerSource (firstB.inst (.bvar firstIndex)) (.sort firstV)}
    (firstHU : firstU.WF U) (firstHV : firstV.WF U)
    {secondDomain : EndpointState callerEnv U callerSource secondA (.sort secondU)}
    {secondBody : EndpointState callerEnv U (secondA :: callerSource) secondB (.sort secondV)}
    {callerFunction : EndpointState callerEnv U callerSource (.app (.const name nextLevels) (.bvar firstIndex))
      (.forallE secondA secondB)}
    {callerSecond : EndpointState callerEnv U callerSource (.bvar secondIndex) secondA}
    {secondResult : EndpointState callerEnv U callerSource (secondB.inst (.bvar secondIndex)) (.sort secondV)}
    (secondHU : secondU.WF U) (secondHV : secondV.WF U)
    (functionRoute : PrefixRoute callerEnv U callerSource (.app (.const name nextLevels) (.bvar firstIndex))
      callerFunction (.app firstHU firstHV firstDomain firstBody callerConstant callerFirst firstResult))
    (firstAnchor : sourceτ 1 = callerσ firstIndex)
    (secondAnchor : sourceτ 0 = callerσ secondIndex)
    {caller : EndpointState fundingEnv U recipeSource recipeExpression recipeAssigned}
    (controls : OriginalWorldControls input.strata fundingEnv)
    (baseline : WorldEnvironmentProvenance input.strata U environment)
    (callerReady : ControlledStoredQuery controls frontier
      (.certificate (RichCert.recipe (node := caller) recipe)))
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (sourceCaller : EndpointState input.owner.selected.origin.source U sourceCallerContext
      sourceCallerExpression sourceCallerAssigned)
    (sourceBaseline : WorldEnvironmentProvenance input.strata U sourceEnvironment)
    (packet : CanonicalConstSitePacket env U registry target input.strata name levels (Profile.fn inner.key inner.output))
    (sourceConstant : EndpointState input.owner.selected.origin.source U innerContext (.const name levels) innerAssigned)
    (innerLocals : List Nat) (innerSubstitution : Subst)
    (inputReady : ControlledStoredQuery
      (canonicalQueryControls input.owner.selected
        (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control))
      frontier (.observation (packet.observation sourceConstant innerLocals innerSubstitution)))
    (sourcePaid : Sponsored frontier [originalCallWorld
      (canonicalQueryControls input.owner.selected
        (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control))
      .fundamental sourceCaller sourceBaseline])
    (sourceProperty : P packet.owner.selected.origin.source)
    (sourceBank : WorldBoundedUnaryCallBank env U registry input.strata P
      (frontier ++ [originalCallWorld
        (canonicalQueryControls input.owner.selected
          (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control))
        .fundamental sourceCaller sourceBaseline]))
    (equal : EqUpToLevels U (.const name levels) (.const name nextLevels))
    (first : RichGradedResult callerEnv env U registry target callerFirst callerLocals callerσ callerAvailable inner.rawInput)
    (firstReady : ControlledStoredQuery controls frontier (.observation first.observation))
    (second : RichGradedResult callerEnv env U registry target callerSecond callerLocals callerσ callerAvailable outer.rawInput)
    (secondReady : ControlledStoredQuery controls frontier (.observation second.observation))
    (sorted : (Profile.singleton outer.output).HasType (.sort relevant)) :
    ∃ factor : RichApplicationOperandFactor env registry target callerFunction callerSecond
        callerLocals callerσ callerAvailable outer.output,
    ∃ operandReady : factor.Controlled controls frontier,
    ∃ footprint, ∃ certificate : RichCert callerEnv env U registry target
        (.app secondHU secondHV secondDomain secondBody callerFunction callerSecond secondResult)
        callerLocals callerσ relevant (.singleton outer.output) footprint,
    ∃ ready : ControlledStoredQuery controls frontier (.certificate certificate),
      footprint.Available callerAvailable ∧
      ready.annotation.worlds ⊆
        operandReady.function.annotation.worlds ++ operandReady.argument.annotation.worlds := by
  obtain ⟨constant, ⟨constantReady⟩⟩ := pending.reindexNestedConstantFunctionWorld controls baseline frontier
    callerReady callerPaid sourceCaller sourceBaseline packet sourceConstant innerLocals innerSubstitution
    inputReady sourcePaid sourceProperty sourceBank formed equal callerConstant callerLocals callerσ callerAvailable
  exact compileReturnedTwoVariableArgumentsWorld inner outer sourceControls frontier innerAnswer outerAnswer innerPath
    henv hscoped formed callerClosed firstHU firstHV secondHU secondHV functionRoute firstAnchor secondAnchor
    controls constant constantReady first firstReady second secondReady sorted

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
