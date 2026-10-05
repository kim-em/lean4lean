import Lean4Lean.Theory.Typing.AnchoredOriginalWorldMappedTwoVariableApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationOperandFamilyConsumption

/-! The traced caller map reconstructs both actual parameter observers,
then the same application factor exposes the requested family demands. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem compileMappedTwoVariableFamilyWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (inner : RichAppOrigin root env registry target source sourceLocals sourceσ (.const name levels) (.bvar sourceFirstIndex))
    (outer : RichAppOrigin root env registry target source sourceLocals sourceσ
      (.app (.const name levels) (.bvar sourceFirstIndex)) (.bvar sourceSecondIndex))
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
    (firstAnchor : sourceτ sourceFirstIndex = callerσ firstIndex)
    (secondAnchor : sourceτ sourceSecondIndex = callerσ secondIndex)
    (controls : OriginalWorldControls strata callerEnv)
    (constant : RichGradedResult callerEnv env U registry target callerConstant callerLocals callerσ callerAvailable (Profile.fn inner.key inner.output))
    (constantControlled : ControlledStoredQuery controls frontier (.observation constant.observation))
    (scope : CallerVariableProgramScope env U registry target
      (fun i need => need ∈ callerAvailable i) sourceAvailable)
    (sourceClosed : sourceAvailable.AtomClosed)
    (firstMapped : scope.index sourceFirstIndex = some firstIndex)
    (secondMapped : scope.index sourceSecondIndex = some secondIndex)
    (ordered : callerEnv.Ordered)
    {callerContext : ContextDerivation callerEnv U callerSource}
    (callerFrame : OriginalRichFrame callerEnv env U registry target callerContext
      callerLocals callerσ callerσ callerAvailable)
    {callerRoot : EndpointRef callerEnv U callerSource callerExpression callerAssigned}
    (location : Located callerRoot
      (.app secondHU secondHV secondDomain secondBody callerFunction callerSecond secondResult))
    (below : callerEnv ≤ env)
    (captured : WorldEnvironmentProvenance strata U (callerFrame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier callerFrame captured)
    (substitutions : Ctx.SubstEq env U target callerσ callerσ callerSource)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental (.ref callerRoot) captured])
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref callerRoot) captured]))
    {demand : FamilyData (Profile q)}
    (path : GeneralOutputPath env U registry target outer.output (show Atom (q+1) from .family demand))
    (sorted : (Profile.singleton (show Atom (q+1) from .family demand)).HasType (.sort outputRelevant)) :
    ∃ factor : RichApplicationOperandFactor env registry target callerFunction callerSecond
        callerLocals callerσ callerAvailable outer.output,
    ∃ operandReady : factor.Controlled controls frontier,
    ∃ footprint, ∃ certificate : RichCert callerEnv env U registry target
        (.app secondHU secondHV secondDomain secondBody callerFunction callerSecond secondResult)
        callerLocals callerσ outputRelevant (.singleton (show Atom (q+1) from .family demand)) footprint,
    ∃ ready : ControlledStoredQuery controls frontier (.certificate certificate),
      footprint.Available callerAvailable ∧
      ready.annotation.worlds ⊆
        operandReady.function.annotation.worlds ++ operandReady.argument.annotation.worlds ∧
      WorldFamilyRequestProperty controls frontier callerRoot registry target callerLocals callerσ callerAvailable
        name nextLevels [.bvar firstIndex, .bvar secondIndex] demand := by
  obtain ⟨sourceRelevant, sourceSorted, ⟨change⟩⟩ := GeneralOutputPath.codeAtOutput henv path sorted
  obtain ⟨factor, operandReady, footprint, certificate, ready, resources, worlds⟩ :=
    compileMappedTwoVariableArgumentsWorld inner outer sourceControls frontier innerAnswer outerAnswer innerPath
      henv hscoped formed callerClosed firstHU firstHV secondHU secondHV functionRoute firstAnchor secondAnchor
      controls constant constantControlled scope sourceClosed firstMapped secondMapped ordered callerFrame sourceSorted
  have requests := factor.familyRequestsAlongPathOfBank location henv hscoped callerContext controls below
    callerFrame captured frontier data callerClosed formed substitutions paid notDefinition notNative
    (by rfl) operandReady path bank
  obtain ⟨nextFootprint, next, annotation, supplied, included, depth⟩ :=
    certificate.codeAction_worlds_depth ready.annotation change resources
  let nextReady : ControlledStoredQuery controls frontier (.certificate next) := {
    annotation := annotation
    within := fun control active => Nat.le_trans (depth _) (ready.within control active)
    sponsored := fun world member => ready.sponsored world (included member) }
  exact ⟨factor, operandReady, nextFootprint, next, nextReady, supplied,
    fun world member => worlds (included member), requests⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
