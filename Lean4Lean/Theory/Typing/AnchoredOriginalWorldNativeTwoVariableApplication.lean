import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedApplicationExecution
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeApplicationArgument
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRichConstantApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryOperations

/-! A concrete source-to-caller terminal: `((S #1) #0)`. The source
constant is reopened under its real canonical mask. Actual returned variable
queries are compiled from the two exposed caller Needs, rather than moved
across source frames or assigned the caller's smaller control budget. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
open private variableLeaves from Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyData
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

private theorem variableAtCaller
    {strata : EquationStratification env}
    {sourceNode : EndpointState sourceEnv U source (.bvar sourceIndex) sourceAssigned}
    (query : RichGradedResult sourceEnv env U registry target sourceNode sourceLocals sourceσ sourceAvailable requested)
    (closed : sourceAvailable.AtomClosed)
    (input : Profile n)
    (fits : ∀ need ∈ sourceAvailable sourceIndex, Need.Fits input need)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : callerEnv.Ordered)
    {context : ContextDerivation callerEnv U callerSource}
    (frame : OriginalRichFrame callerEnv env U registry target context callerLocals callerσ callerτ callerAvailable)
    (node : EndpointState callerEnv U callerSource (.bvar index) assigned)
    (exposedInput : Profile n)
    (inputAdapter : GeneralNormalProfileAdapter env U registry target exposedInput input)
    (exposed : Need.mk n exposedInput ∈ callerAvailable index)
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length)) :
    ∃ argument : RichGradedResult callerEnv env U registry target node callerLocals callerσ callerAvailable requested,
    ∃ ready : ControlledStoredQuery controls frontier (.observation argument.observation),
      ready.annotation.worlds = [] ∧ ∀ policy, argument.observation.headDepth policy = 0 := by
  classical
  obtain ⟨used, ⟨trace⟩, resources⟩ := query.observation.variableDependency closed query.resources
  let leaf : VariableDependencyProgram env U registry target
      (fun i need => i = index ∧ need = Need.mk n exposedInput) index exposedInput :=
    .leaf (need := Need.mk n exposedInput) ⟨rfl,rfl⟩
  let supplied (i : Nat) (need : Need) (member : (i,need) ∈ used) :
      VariableDependencyProgram env U registry target
        (fun i need => i = index ∧ need = Need.mk n exposedInput) index need.profile := by
    have same := trace.indices member
    subst i
    have fit := fits need (resources sourceIndex need member)
    exact (leaf.map henv hscoped formed inputAdapter).localDemand need fit.1 fit.2
  let program := (SortableVariableTrace.replayPrograms henv hscoped formed trace supplied).adaptRequest
    henv hscoped formed query.bound query.adapter
  let dependency : WorldVariableDependency env U registry target callerAvailable index requested := {
    rank := program.rank, bound := program.bound, raw := program.raw, footprint := program.footprint
    trace := program.trace, resources := by
      intro i need member
      obtain ⟨rfl,rfl⟩ := program.resources i need member
      exact exposed
    adapter := program.adapter }
  let argument := dependency.atNode henv hscoped formed ordered frame node
  let leaves := variableLeaves (env := env) (U := U) (registry := registry) (target := target)
    callerLocals callerσ index dependency.trace.height dependency.footprint
    (fun i need member => dependency.trace.indices member)
    (fun i need member => dependency.trace.leaf_bound member)
  obtain ⟨annotation, worlds, depth⟩ := neutralObsProvenance (strata := strata) leaves
  let ready : ControlledStoredQuery controls frontier (.observation argument.observation) := {
    annotation := .legacy _ (.legacy _ annotation)
    within := by
      intro control active
      simpa only [argument, WorldVariableDependency.atNode, StoredOriginalQuery.headDepth,
        RichObs.headDepth, SortableObs.headDepth] using
        (show leaves.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control) ≤ controls.fuel control from by
          rw [depth]; exact Nat.zero_le _)
    sponsored := by
      change Sponsored frontier annotation.worlds
      rw [worlds]
      intro world member
      cases member }
  refine ⟨argument,ready,worlds,?_⟩
  intro policy
  simpa only [argument, WorldVariableDependency.atNode, RichObs.headDepth, SortableObs.headDepth] using depth policy

private theorem outputPathControlled
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (path : GeneralOutputPath env U registry target a b)
    (query : RichGradedResult sourceEnv env U registry target node locals σ available (.singleton a))
    (ready : ControlledStoredQuery controls frontier (.observation query.observation)) :
    ∃ next : RichGradedResult sourceEnv env U registry target node locals σ available (.singleton b),
      Nonempty (ControlledStoredQuery controls frontier (.observation next.observation)) := by
  let N := max query.rank path.height
  let bound := Nat.le_max_left query.rank path.height
  let raised := query.raiseTo henv hscoped formed N bound
  have action := (path.normalize N (Nat.le_max_right query.rank path.height)).toGeneralAdapter henv hscoped formed
  let result : RichGradedResult sourceEnv env U registry target node locals σ available (.singleton b) := {
    rank := N, bound := Nat.le_trans path.bounds.2 (Nat.le_max_right _ _)
    raw := raised.raw, footprint := raised.footprint, observation := raised.observation
    adapter := by
      have before := raised.adapter
      rw [raiseProfile_singleton] at before ⊢
      exact before.comp (.cons (List.mem_singleton_self _) action (.nil _))
    resources := raised.resources, live := raised.live }
  exact ⟨result, ready.raise bound⟩

private theorem ownerMetadata
    {strata : EquationStratification env}
    {first : CanonicalCodeOwner env registry strata firstName}
    {second : CanonicalCodeOwner env registry strata secondName}
    (nameEq : firstName = secondName) (same : HEq first second) :
    first.selected.origin.source = second.selected.origin.source ∧
      first.selected.ordinal = second.selected.ordinal := by
  cases nameEq
  cases eq_of_heq same
  exact ⟨rfl,rfl⟩

/-- Two actual source application answers supply both admissions. The
canonical constant and neutral binder demands then construct the caller
applications. No caller query, caller field answer, source-frame cast, or
source/caller control equality is assumed. -/
private theorem compileNativeTwoVariableArgumentsWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    (owner : CanonicalCodeOwner env registry strata ownerName)
    {root : EndpointRef owner.selected.origin.source U rootSource rootExpression rootType}
    (inner : RichAppOrigin root env registry target source sourceLocals sourceσ (.const name levels) (.bvar 1))
    (outer : RichAppOrigin root env registry target source sourceLocals sourceσ
      (.app (.const name levels) (.bvar 1)) (.bvar 0))
    {sourceAvailable : Valuation}
    (sourceControls : OriginalWorldControls strata owner.selected.origin.source)
    (frontier : List (World strata.rules.length))
    (innerAnswer : RetainedApplicationAnswers inner sourceControls frontier sourceτ
      sourceAvailable)
    (outerAnswer : RetainedApplicationAnswers outer sourceControls frontier sourceτ
      sourceAvailable)
    (innerPath : GeneralOutputPath env U registry target inner.output
      (show Atom (outer.rank+1) from .fn outer.key outer.output))
    (constantReady : ControlledStoredQuery sourceControls frontier (.observation inner.function))
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
    (equal : EqUpToLevels U (.const name levels) (.const name nextLevels))
    (caller : EndpointState fundingEnv U fundingSource fundingExpression fundingAssigned)
    (controls : OriginalWorldControls strata fundingEnv)
    (first : RichGradedResult callerEnv env U registry target callerFirst callerLocals callerσ callerAvailable inner.rawInput)
    (firstReady : ControlledStoredQuery controls frontier (.observation first.observation))
    (second : RichGradedResult callerEnv env U registry target callerSecond callerLocals callerσ callerAvailable outer.rawInput)
    (secondReady : ControlledStoredQuery controls frontier (.observation second.observation))
    (baseline : WorldEnvironmentProvenance strata U environment)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (sourceReady : P owner.selected.origin.source)
    (masked : WithinAbove controls.cutoff controls.fuel
      (headDepth owner.selected.ordinal
        (fun control => inner.function.stratifiedDepth (strata.headOrdinal registry) control)))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
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
  obtain ⟨packet, annotation, nameEq, ownerEq, worlds, depth⟩ :=
    canonicalConstSiteOfFunctionAnnotated owner inner.functionNode inner.function constantReady.annotation
  obtain ⟨ownerSource,ownerOrdinal⟩ := ownerMetadata nameEq ownerEq
  have packetBounded : WithinAbove controls.cutoff controls.fuel packet.chargeDepth := by
    intro control active
    have bound := masked control active
    have smaller := depth (stratifiedHeadPolicy (strata.headOrdinal registry) control)
    change headDepth packet.owner.selected.ordinal
      (fun control => packet.query.stratifiedDepth (strata.headOrdinal registry) control) control ≤ _
    rw [ownerOrdinal]
    by_cases lower : control < owner.selected.ordinal
    · simp only [headDepth, if_pos lower]
      exact Nat.zero_le _
    · simp only [headDepth, if_neg lower] at bound ⊢
      exact Nat.le_trans (Nat.add_le_add_right smaller _) bound
  obtain ⟨constant, ⟨constantControlled⟩⟩ := packet.reindexFunctionLevelsWorld equal annotation formed
    caller controls baseline frontier paid (ownerSource.symm ▸ sourceReady)
    (fun world member => constantReady.sponsored world (worlds member)) packetBounded bank
    callerConstant callerLocals callerσ callerAvailable
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

theorem compileNativeTwoVariableApplicationWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    (owner : CanonicalCodeOwner env registry strata ownerName)
    {root : EndpointRef owner.selected.origin.source U rootSource rootExpression rootType}
    (inner : RichAppOrigin root env registry target source sourceLocals sourceσ (.const name levels) (.bvar 1))
    (outer : RichAppOrigin root env registry target source sourceLocals sourceσ
      (.app (.const name levels) (.bvar 1)) (.bvar 0))
    {sourceAvailable : Valuation}
    (sourceControls : OriginalWorldControls strata owner.selected.origin.source)
    (frontier : List (World strata.rules.length))
    (innerAnswer : RetainedApplicationAnswers inner sourceControls frontier sourceτ
      ((sourceAvailable.push (firstFootprint.localNeeds ++ firstFootprint.localNeeds.flatMap Need.singletons)).push
        (secondFootprint.localNeeds ++ secondFootprint.localNeeds.flatMap Need.singletons)))
    (outerAnswer : RetainedApplicationAnswers outer sourceControls frontier sourceτ
      ((sourceAvailable.push (firstFootprint.localNeeds ++ firstFootprint.localNeeds.flatMap Need.singletons)).push
        (secondFootprint.localNeeds ++ secondFootprint.localNeeds.flatMap Need.singletons)))
    (innerPath : GeneralOutputPath env U registry target inner.output
      (show Atom (outer.rank+1) from .fn outer.key outer.output))
    (constantReady : ControlledStoredQuery sourceControls frontier (.observation inner.function))
    (firstPack : BinderPack firstRank firstPacked firstFootprint firstOutside)
    (secondPack : BinderPack secondRank secondPacked secondFootprint secondOutside)
    (firstCoverage : firstPacked.atoms ⊆ (firstInput : Profile firstRank).atoms)
    (secondCoverage : secondPacked.atoms ⊆ (secondInput : Profile secondRank).atoms)
    (sourceClosed : sourceAvailable.AtomClosed)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {callerContext : ContextDerivation callerEnv U callerSource}
    (callerFrame : OriginalRichFrame callerEnv env U registry target callerContext
      callerLocals callerσ callerτ callerAvailable)
    (callerOrdered : callerEnv.Ordered) (callerClosed : callerAvailable.AtomClosed)
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
    (firstExposed : Profile firstRank) (secondExposed : Profile secondRank)
    (firstAdapter : GeneralNormalProfileAdapter env U registry target firstExposed firstInput)
    (secondAdapter : GeneralNormalProfileAdapter env U registry target secondExposed secondInput)
    (firstMember : Need.mk firstRank firstExposed ∈ callerAvailable firstIndex)
    (secondMember : Need.mk secondRank secondExposed ∈ callerAvailable secondIndex)
    (firstAnchor : sourceτ 1 = callerσ firstIndex)
    (secondAnchor : sourceτ 0 = callerσ secondIndex)
    (equal : EqUpToLevels U (.const name levels) (.const name nextLevels))
    (caller : EndpointState fundingEnv U fundingSource fundingExpression fundingAssigned)
    (controls : OriginalWorldControls strata fundingEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (sourceReady : P owner.selected.origin.source)
    (masked : WithinAbove controls.cutoff controls.fuel
      (headDepth owner.selected.ordinal
        (fun control => inner.function.stratifiedDepth (strata.headOrdinal registry) control)))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
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
  have allClosed := Valuation.push_atomized_closed
    (Valuation.push_atomized_closed sourceClosed firstFootprint.localNeeds) secondFootprint.localNeeds
  obtain ⟨first, firstReady, _, _⟩ := variableAtCaller innerAnswer.argumentValue.rightQuery allClosed firstInput
    (fun need member => by
      obtain ⟨bounded, covered⟩ := firstPack.atomized_localNeeds need member
      exact ⟨bounded, fun atom present => firstCoverage (covered atom present)⟩)
    henv hscoped formed callerOrdered callerFrame callerFirst firstExposed firstAdapter firstMember controls frontier
  obtain ⟨second, secondReady, _, _⟩ := variableAtCaller outerAnswer.argumentValue.rightQuery allClosed secondInput
    (fun need member => by
      obtain ⟨bounded, covered⟩ := secondPack.atomized_localNeeds need member
      exact ⟨bounded, fun atom present => secondCoverage (covered atom present)⟩)
    henv hscoped formed callerOrdered callerFrame callerSecond secondExposed secondAdapter secondMember controls frontier
  exact compileNativeTwoVariableArgumentsWorld owner inner outer sourceControls frontier
    innerAnswer outerAnswer innerPath constantReady henv hscoped formed callerClosed
    firstHU firstHV secondHU secondHV functionRoute firstAnchor secondAnchor equal caller controls
    first firstReady second secondReady baseline paid sourceReady masked bank sorted

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
