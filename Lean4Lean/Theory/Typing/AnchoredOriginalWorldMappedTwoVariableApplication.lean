import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedCallerScope
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNestedTwoVariableApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeTwoBodyInputs

/-! Rebuild retained variable answers through the actual caller program map.
Source indices are arbitrary: fixed binders and charged resets do not become
assumptions that the two arguments occupy slots one and zero. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
open private outputPathControlled from Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeTwoVariableApplication
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- Each actual leaf of the returned source query is interpreted by the
same traced scope map, then reconstructed at the genuine caller variable. -/
theorem CallerVariableProgramScope.rebuildVariableWorld
    {index : Nat}
    {strata : EquationStratification env}
    (scope : CallerVariableProgramScope env U registry target
      (fun i need => need ∈ callerAvailable i) sourceAvailable)
    {sourceNode : EndpointState sourceEnv U source (.bvar sourceIndex) sourceAssigned}
    (query : RichGradedResult sourceEnv env U registry target sourceNode sourceLocals sourceσ sourceAvailable requested)
    (closed : sourceAvailable.AtomClosed)
    (mapped : scope.index sourceIndex = some index)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : callerEnv.Ordered)
    {context : ContextDerivation callerEnv U callerSource}
    (frame : OriginalRichFrame callerEnv env U registry target context callerLocals callerσ callerτ callerAvailable)
    (node : EndpointState callerEnv U callerSource (.bvar index) assigned)
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length)) :
    ∃ argument : RichGradedResult callerEnv env U registry target node callerLocals callerσ callerAvailable requested,
      Nonempty (ControlledStoredQuery controls frontier (.observation argument.observation)) := by
  obtain ⟨used, ⟨trace⟩, resources⟩ := query.observation.variableDependency closed query.resources
  let supplied (i : Nat) (need : Need) (member : (i, need) ∈ used) :
      VariableDependencyProgram env U registry target (fun i need => need ∈ callerAvailable i) index need.profile := by
    have same := trace.indices member
    subst i
    exact scope.program sourceIndex need (resources sourceIndex need member) index mapped
  let replay := (SortableVariableTrace.replayPrograms henv hscoped formed trace supplied).adaptRequest
    henv hscoped formed query.bound query.adapter
  let dependency : WorldVariableDependency env U registry target callerAvailable index requested := {
    rank := replay.rank, bound := replay.bound, raw := replay.raw, footprint := replay.footprint
    trace := replay.trace, resources := replay.resources, adapter := replay.adapter }
  exact ⟨dependency.atNode henv hscoped formed ordered frame node,
    ⟨dependency.atNode_controlled controls frontier henv hscoped formed ordered frame node⟩⟩

theorem compileMappedTwoVariableArgumentsWorld
    {strata : EquationStratification env}
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
    (controls : OriginalWorldControls strata fundingEnv)
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
      callerLocals callerσ callerτ callerAvailable)
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
  obtain ⟨first, ⟨firstReady⟩⟩ := scope.rebuildVariableWorld innerAnswer.argumentValue.rightQuery
    sourceClosed firstMapped henv hscoped formed ordered callerFrame callerFirst controls frontier
  obtain ⟨second, ⟨secondReady⟩⟩ := scope.rebuildVariableWorld outerAnswer.argumentValue.rightQuery
    sourceClosed secondMapped henv hscoped formed ordered callerFrame callerSecond controls frontier
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


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
