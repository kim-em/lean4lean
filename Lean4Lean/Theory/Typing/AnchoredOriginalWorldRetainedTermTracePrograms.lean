import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermCallerScope
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProjectionProgramTrace

/-! Fold the actual complete source transcript with caller resource programs.
Body edges extend the source table from their actual old-key program, domain
edges preserve it, and charged edges compose their resource transfers before
resetting to the genuine closed root. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

variable {Fits : Nat → Need → Prop}

structure RetainedTermProgramCallerData
    (state : RetainedTermProgramState env U registry target strata P frontier goal goalOutput)
    (Fits : Nat → Need → Prop) where
  scope : CallerVariableProgramScope env U registry target Fits state.available
  inputs : state.demand.InputPrograms Fits

/-- The actual initial literal-term demand has no pending binder programs. Its
source table is the caller table itself, so every leaf is constructed from
its original literal membership. -/
noncomputable def RetainedTermProgramCallerData.ofRichTerm
    {sourceEnv : VEnv} {source : List VExpr} {assigned : VExpr}
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {relevant : Bool} {n : Nat} {profile : Profile n} {footprint : Footprint} {goalOutput : Atom n}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source goal assigned}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint}
    (ready : ControlledStoredQuery controls frontier (.certificate query))
    (provenance : EndpointProvenance context node)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : footprint.Available available) (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (member : goalOutput ∈ profile.atoms) :
    RetainedTermProgramCallerData
      (RetainedTermProgramState.ofRich ready provenance frame captured data closed substitutions resources
        sourceBelow paid bank .terminal member)
      (fun i need => need ∈ available i) :=
  ⟨.initial available, PUnit.unit⟩

private def castTraceDemandPrograms (same : expression = next)
    (demand : RetainedTermDemand env U registry target goal goalOutput expression atom)
    (programs : demand.InputPrograms Fits) : (same ▸ demand).InputPrograms Fits := by
  cases same
  exact programs

noncomputable def RetainedTermBodyTransitionWitness.callerData
    {before after : RetainedTermProgramState env U registry target strata P frontier goal goalOutput}
    (edge : RetainedTermBodyTransitionWitness before after)
    (data : RetainedTermProgramCallerData before Fits)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    RetainedTermProgramCallerData after Fits := by
  cases edge with
  | native expressionEq path selected admitted pending row execution continuation member readback normalized worlds depth =>
    let changed := castTraceDemandPrograms expressionEq before.demand data.inputs
    let current := normalized.inputPrograms changed
    let slot := normalized.nativeInputProgram changed pending henv hscoped formed
    exact ⟨data.scope.push slot _ (fun need member => by
      obtain ⟨bound, covered⟩ := row.pack.atomized_localNeeds need member
      exact ⟨bound, fun atom present => row.covered atom (covered atom present)⟩), current.2⟩
  | legacy expressionEq path selected admitted selection execution sameAnnotation continuation member readback normalized worlds depth =>
    let changed := castTraceDemandPrograms expressionEq before.demand data.inputs
    let current := normalized.inputPrograms changed
    let slot := normalized.nativeInputProgram changed selection.pending henv hscoped formed
    exact ⟨data.scope.push slot _ (fun need member => by
      obtain ⟨bound, covered⟩ := selection.row.pack.atomized_localNeeds need member
      exact ⟨bound, fun atom present => selection.row.covered atom (covered atom present)⟩), current.2⟩

noncomputable def RetainedTermDomainTransitionWitness.callerData
    {before after : RetainedTermProgramState env U registry target strata P frontier goal goalOutput}
    (edge : RetainedTermDomainTransitionWitness before after)
    (data : RetainedTermProgramCallerData before Fits) : RetainedTermProgramCallerData after Fits := by
  cases edge with
  | intro opening smaller =>
    rcases before with ⟨sourceEnv, source, context, expression, assigned, node, provenance, controls,
      locals, left, right, available, frame, captured, originalData, closed, substitutions, sourceBelow,
      originalRelevant, originalRank, originalProfile, originalFootprint, originalProgram, originalAnnotation,
      originalWithin, originalSponsored, originalResources, originalSelected, originalMember, demand, paid, bank⟩
    rcases opening with ⟨A, B, expressionEq, u, v, hu, hv, domainNode, bodyNode, route,
      rank, profile, footprint, program, annotation, within, sponsored, resources, worlds, depth,
      selected, member, nextRank, requested, prototypeDomain, prototypeBody, support, rows, inputPath, domainMember,
      output, continuation, normalized, readback⟩
    cases expressionEq
    exact ⟨data.scope, normalized.inputPrograms data.inputs⟩

noncomputable def RetainedTermChargedTransitionWitness.callerData
    {before after : RetainedTermProgramState env U registry target strata P frontier goal goalOutput}
    (edge : RetainedTermChargedTransitionWitness before after)
    (data : RetainedTermProgramCallerData before Fits)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    RetainedTermProgramCallerData after Fits := by
  cases edge with
  | intro annotation sources resources worlds depth smaller demand member path same opening =>
    cases same
    let context := opening.pending.mappedBinderPrograms henv hscoped formed data.scope.index
      (fun i need member => data.scope.program i need (resources i need member))
    exact ⟨.empty, (Classical.choice opening.pushed).mappedInputPrograms data.scope.index context data.inputs⟩

noncomputable def RetainedTermProgramTransition.callerData
    {before after : RetainedTermProgramState env U registry target strata P frontier goal goalOutput}
    (edge : RetainedTermProgramTransition before after)
    (data : RetainedTermProgramCallerData before Fits)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    RetainedTermProgramCallerData after Fits := by
  cases edge with
  | body witness => exact witness.callerData data henv hscoped formed
  | domain witness => exact witness.callerData data
  | charged witness => exact witness.callerData data henv hscoped formed

/-- Every state and body query used in this fold is the actual retained
witness. In particular nested charged roots compose source-private Needs
through earlier body programs before using the caller resource table. -/
noncomputable def RetainedProjectionProgramTrace.callerData
    {before : RetainedTermProgramState env U registry target strata P frontier goal goalOutput}
    {terminal : RetainedProjectionProgramTerminal env U registry target strata P frontier goal goalOutput}
    (trace : RetainedProjectionProgramTrace env U registry target strata P frontier goal goalOutput before terminal)
    (data : RetainedTermProgramCallerData before Fits)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    RetainedTermProgramCallerData terminal.state Fits := by
  induction trace with
  | terminal witness =>
    cases witness
    exact data
  | step smaller edge rest ih => exact ih (edge.callerData data henv hscoped formed)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
