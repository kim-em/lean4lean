import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedSymbolicIndices
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTracePrograms

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private symbolic_transport symbolicTransportPrograms
  from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedSymbolicIndices
open private castTraceDemandPrograms
  from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTracePrograms
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

variable {Fits : Nat → Need → Prop}

noncomputable def RetainedProgramCallerData.symbolicOperands
    {state : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (data : RetainedProgramCallerData state Fits) : VExpr × VExpr :=
  state.demand.symbolicReadback data.inputs (callerIndexSubst data.scope.index)

theorem RetainedChargedTransitionWitness.callerData_symbolicOperands
    {before after : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (edge : RetainedChargedTransitionWitness before after)
    (data : RetainedProgramCallerData before Fits)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    (edge.callerData data henv hscoped formed).symbolicOperands = data.symbolicOperands := by
  cases edge with
  | intro annotation sources resources worlds depth smaller demand member path same opening =>
    cases same
    exact (Classical.choice opening.pushed).symbolicReadback _ _ _

theorem RetainedDomainTransitionWitness.callerData_symbolicOperands
    {before after : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (edge : RetainedDomainTransitionWitness before after)
    (data : RetainedProgramCallerData before Fits) :
    (edge.callerData data).symbolicOperands = data.symbolicOperands := by
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
    exact normalized.symbolicReadback data.inputs _

theorem RetainedBodyTransitionWitness.callerData_symbolicOperands
    {before after : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (edge : RetainedBodyTransitionWitness before after)
    (data : RetainedProgramCallerData before Fits)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    (edge.callerData data henv hscoped formed).symbolicOperands = data.symbolicOperands := by
  cases edge with
  | native expressionEq path selected admitted pending row execution continuation member readback normalized worlds depth =>
    let changed := castTraceDemandPrograms expressionEq before.demand data.inputs
    have result := normalized.symbolicReadback changed (callerIndexSubst data.scope.index)
    have old := symbolic_transport expressionEq before.demand data.inputs (callerIndexSubst data.scope.index)
    have combined := result.trans old
    change _ = before.demand.symbolicReadback data.inputs (callerIndexSubst data.scope.index)
    apply Eq.trans ?_ combined
    apply congrArg (continuation.symbolicReadback (normalized.inputPrograms changed).2)
    funext i
    cases i with
    | zero =>
      change callerIndexExpression
        ((normalized.nativeInputProgram changed _ henv hscoped formed).map Sigma.fst) = _
      unfold RetainedDemandHeadNormalization.nativeInputProgram
      cases (normalized.inputPrograms changed).1 <;> rfl
    | succ i => rfl
  | legacy expressionEq path selected admitted selection execution sameAnnotation continuation member readback normalized worlds depth =>
    let changed := castTraceDemandPrograms expressionEq before.demand data.inputs
    have result := normalized.symbolicReadback changed (callerIndexSubst data.scope.index)
    have old := symbolic_transport expressionEq before.demand data.inputs (callerIndexSubst data.scope.index)
    have combined := result.trans old
    change _ = before.demand.symbolicReadback data.inputs (callerIndexSubst data.scope.index)
    apply Eq.trans ?_ combined
    apply congrArg (continuation.symbolicReadback (normalized.inputPrograms changed).2)
    funext i
    cases i with
    | zero =>
      change callerIndexExpression
        ((normalized.nativeInputProgram changed _ henv hscoped formed).map Sigma.fst) = _
      unfold RetainedDemandHeadNormalization.nativeInputProgram
      cases (normalized.inputPrograms changed).1 <;> rfl
    | succ i => rfl

theorem RetainedProgramTransition.callerData_symbolicOperands
    {before after : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (edge : RetainedProgramTransition before after) (data : RetainedProgramCallerData before Fits)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    (edge.callerData data henv hscoped formed).symbolicOperands = data.symbolicOperands := by
  cases edge with
  | body witness => exact witness.callerData_symbolicOperands data henv hscoped formed
  | domain witness => exact witness.callerData_symbolicOperands data
  | charged witness => exact witness.callerData_symbolicOperands data henv hscoped formed

/-- The exact trace fold identifies terminal source operands symbolically in
caller coordinates. No equality of whole source and caller substitutions is
assumed or needed. -/
theorem RetainedProgramTrace.callerData_terminalOperands
    {before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    {terminal : RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (trace : RetainedProgramTrace env U registry target strata P frontier goalFunction goalArgument goalOutput before terminal)
    (data : RetainedProgramCallerData before Fits)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    let final := trace.callerData data henv hscoped formed
    (goalFunction.subst (Subst.lift_l terminal.sourceRenaming (callerIndexSubst final.scope.index)),
      goalArgument.subst (Subst.lift_l terminal.sourceRenaming (callerIndexSubst final.scope.index))) =
      data.symbolicOperands := by
  induction trace with
  | terminal witness =>
    cases witness with
    | intro opening =>
      have normalized := opening.normalized.symbolicReadback
        (castTraceDemandPrograms opening.expressionEq _ data.inputs) (callerIndexSubst data.scope.index)
      exact normalized.trans (symbolic_transport opening.expressionEq _ data.inputs _)
  | step smaller edge rest ih =>
    exact (ih (edge.callerData data henv hscoped formed)).trans
      (edge.callerData_symbolicOperands data henv hscoped formed)

/-- A final caller variable cannot come from a skipped private source slot.
This is constructor-level index correspondence, not semantic variable
inversion. The initial equality is a symbolic computation of the demand. -/
theorem RetainedProgramTrace.argumentIndex
    {before : RetainedProgramState env U registry target strata P frontier goalFunction (.bvar caller) goalOutput}
    {terminal : RetainedProgramTerminal env U registry target strata P frontier goalFunction (.bvar caller) goalOutput}
    (trace : RetainedProgramTrace env U registry target strata P frontier goalFunction (.bvar caller) goalOutput before terminal)
    (data : RetainedProgramCallerData before Fits)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (initial : data.symbolicOperands.2 = .bvar caller) :
    (trace.callerData data henv hscoped formed).scope.index (terminal.sourceRenaming.liftVar caller) = some caller := by
  apply callerIndexExpression_eq_bvar.mp
  exact (congrArg Prod.snd (trace.callerData_terminalOperands data henv hscoped formed)).trans initial

/-- The ordinary caller entry computes the identity symbolic operand map. -/
theorem RetainedProgramCallerData.ofRichApplication_symbolicOperands
    {sourceEnv : VEnv} {source : List VExpr} {assigned : VExpr}
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {relevant : Bool} {n : Nat} {profile : Profile n} {footprint : Footprint} {goalOutput : Atom n}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.app goalFunction goalArgument) assigned}
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
    (RetainedProgramCallerData.ofRichApplication ready provenance frame captured data closed substitutions
      resources sourceBelow paid bank member).symbolicOperands = (goalFunction, goalArgument) := by
  change (goalFunction.subst Subst.id, goalArgument.subst Subst.id) = _
  simp

/-- Initial application to physical terminal correspondence for the actual
computed caller table. All binder/resource/charge transitions are internal. -/
theorem RetainedProgramTrace.initialApplicationOperands
    {sourceEnv : VEnv} {source : List VExpr} {assigned : VExpr}
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {relevant : Bool} {n : Nat} {profile : Profile n} {footprint : Footprint} {goalOutput : Atom n}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.app goalFunction goalArgument) assigned}
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
    (member : goalOutput ∈ profile.atoms)
    {terminal : RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (trace : RetainedProgramTrace env U registry target strata P frontier goalFunction goalArgument goalOutput
      (RetainedProgramState.ofRich ready provenance frame captured data closed substitutions resources
        sourceBelow paid bank .application member) terminal)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    let initial := RetainedProgramCallerData.ofRichApplication ready provenance frame captured data closed substitutions
      resources sourceBelow paid bank member
    let final := trace.callerData initial henv hscoped formed
    (goalFunction.subst (Subst.lift_l terminal.sourceRenaming (callerIndexSubst final.scope.index)),
      goalArgument.subst (Subst.lift_l terminal.sourceRenaming (callerIndexSubst final.scope.index))) =
      (goalFunction, goalArgument) := by
  exact (trace.callerData_terminalOperands _ henv hscoped formed).trans
    (RetainedProgramCallerData.ofRichApplication_symbolicOperands ready provenance frame captured data closed substitutions
      resources sourceBelow paid bank member)

/-- The two argument slots of a caller family application keep their actual
caller indices through arbitrary fixed binders and nested charged resets. -/
theorem RetainedProgramTrace.initialTwoVariableIndices
    {sourceEnv : VEnv} {source : List VExpr} {assigned : VExpr}
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {relevant : Bool} {n : Nat} {profile : Profile n} {footprint : Footprint} {goalOutput : Atom n}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.app goalFunction goalArgument) assigned}
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
    (member : goalOutput ∈ profile.atoms)
    {terminal : RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (trace : RetainedProgramTrace env U registry target strata P frontier goalFunction goalArgument goalOutput
      (RetainedProgramState.ofRich ready provenance frame captured data closed substitutions resources
        sourceBelow paid bank .application member) terminal)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (functionVariable : goalFunction = .app functionPrefix (.bvar first))
    (argumentVariable : goalArgument = .bvar second) :
    let initial := RetainedProgramCallerData.ofRichApplication ready provenance frame captured data closed substitutions
      resources sourceBelow paid bank member
    let final := trace.callerData initial henv hscoped formed
    final.scope.index (terminal.sourceRenaming.liftVar first) = some first ∧
      final.scope.index (terminal.sourceRenaming.liftVar second) = some second := by
  have same := trace.initialApplicationOperands ready provenance frame captured data closed substitutions
      resources sourceBelow paid bank member henv hscoped formed
  cases functionVariable
  cases argumentVariable
  constructor
  · apply callerIndexExpression_eq_bvar.mp
    exact (VExpr.app.inj (congrArg Prod.fst same)).2
  · apply callerIndexExpression_eq_bvar.mp
    exact congrArg Prod.snd same

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
