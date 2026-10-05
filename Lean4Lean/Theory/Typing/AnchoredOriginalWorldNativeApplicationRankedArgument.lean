import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeApplicationArgument
import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeRankedInputReplay

/-! Mixed-grade pending row inputs are executed against the actual caller
Need. The returned argument is reconstructed at its genuine caller variable;
all finite adapters, including the source F answer's adapter, are retained. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private variableLeaves from Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyData
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private theorem replayVariableProgram
    {strata : EquationStratification env}
    {sourceNode : EndpointState sourceEnv U source (.bvar 0) sourceAssigned}
    {sourceAvailable : Valuation} {needs : List Need}
    (query : RichGradedResult sourceEnv env U registry target sourceNode sourceLocals sourceσ
      (sourceAvailable.push needs) requested)
    (closed : (sourceAvailable.push needs).AtomClosed)
    (input : Profile n)
    (fits : ∀ need ∈ needs, Need.Fits input need)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : callerEnv.Ordered)
    {context : ContextDerivation callerEnv U callerSource}
    (frame : OriginalRichFrame callerEnv env U registry target context callerLocals callerσ callerτ callerAvailable)
    (node : EndpointState callerEnv U callerSource (.bvar index) assigned)
    (exposedInput : Profile m)
    (inputProgram : VariableDependencyProgram env U registry target
      (fun i need => i = index ∧ need = Need.mk m exposedInput) index input)
    (exposed : Need.mk m exposedInput ∈ callerAvailable index)
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length)) :
    ∃ argument : RichGradedResult callerEnv env U registry target node callerLocals callerσ callerAvailable requested,
    ∃ ready : ControlledStoredQuery controls frontier (.observation argument.observation),
      ready.annotation.worlds = [] ∧
      (∀ policy, argument.observation.headDepth policy = 0) ∧
      (∀ i need, (i, need) ∈ argument.footprint → i = index ∧ need = Need.mk m exposedInput) := by
  classical
  obtain ⟨used, ⟨trace⟩, resources⟩ := query.observation.variableDependency closed query.resources
  let supplied (i : Nat) (need : Need) (member : (i, need) ∈ used) :
      VariableDependencyProgram env U registry target (fun i need => i = index ∧ need = Need.mk m exposedInput) index need.profile := by
    have same := trace.indices member
    subst i
    have fit := fits need (resources 0 need member)
    exact inputProgram.localDemand need fit.1 fit.2
  let program := (SortableVariableTrace.replayPrograms henv hscoped formed trace supplied).adaptRequest
    henv hscoped formed query.bound query.adapter
  let dependency : WorldVariableDependency env U registry target callerAvailable index requested := {
    rank := program.rank, bound := program.bound, raw := program.raw, footprint := program.footprint
    trace := program.trace, resources := by
      intro i need member
      obtain ⟨rfl, rfl⟩ := program.resources i need member
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
  refine ⟨argument, ready, worlds, ?_, ?_⟩
  · intro policy
    simpa only [argument, WorldVariableDependency.atNode, RichObs.headDepth, SortableObs.headDepth] using depth policy
  · intro i need member
    change (i, need) ∈ program.footprint at member
    exact program.resources i need member

/-- Execute the actual ranked row input program before rebuilding the SAME
returned original argument query. No mixed-grade admission or resource oracle
is supplied. -/
theorem RichGradedResult.replayRankedNativeBinderArgument
    {strata : EquationStratification env}
    {original : List (Key n × Profile n)} {selectedKey : Key m} {selectedResult : Profile m}
    (pending : RankedPendingNativeRow env U registry target original relevant selectedKey selectedResult)
    {sourceNode : EndpointState sourceEnv U source (.bvar 0) sourceAssigned}
    {sourceAvailable : Valuation}
    (query : RichGradedResult sourceEnv env U registry target sourceNode sourceLocals sourceσ
      (sourceAvailable.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)) requested)
    (pack : BinderPack n packed bodyFootprint outside)
    (coverage : packed.atoms ⊆ pending.oldKey.input.atoms)
    (sourceClosed : sourceAvailable.AtomClosed)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : callerEnv.Ordered)
    {context : ContextDerivation callerEnv U callerSource}
    (frame : OriginalRichFrame callerEnv env U registry target context callerLocals callerσ callerτ callerAvailable)
    (node : EndpointState callerEnv U callerSource (.bvar index) assigned)
    (exposed : Need.mk m selectedKey.input ∈ callerAvailable index)
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length)) :
    ∃ argument : RichGradedResult callerEnv env U registry target node callerLocals callerσ callerAvailable requested,
    ∃ ready : ControlledStoredQuery controls frontier (.observation argument.observation),
      ready.annotation.worlds = [] ∧
      (∀ policy, argument.observation.headDepth policy = 0) ∧
      (∀ i need, (i, need) ∈ argument.footprint → i = index ∧ need = Need.mk m selectedKey.input) := by
  let leaf : VariableDependencyProgram env U registry target
      (fun i need => i = index ∧ need = Need.mk m selectedKey.input) index selectedKey.input :=
    .leaf (need := Need.mk m selectedKey.input) ⟨rfl, rfl⟩
  let inputProgram := pending.replayInput henv hscoped formed leaf
  apply replayVariableProgram query (Valuation.push_atomized_closed sourceClosed _) pending.oldKey.input
    (fun need member => ?_) henv hscoped formed ordered frame node selectedKey.input inputProgram
    exposed controls frontier
  obtain ⟨bounded, covered⟩ := pack.atomized_localNeeds need member
  exact ⟨bounded, fun atom present => coverage (covered atom present)⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
