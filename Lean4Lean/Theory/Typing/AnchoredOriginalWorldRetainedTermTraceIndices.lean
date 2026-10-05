import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermSymbolicIndices
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermTracePrograms

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private symbolic_transport symbolicTransportPrograms
  from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermSymbolicIndices
open private castTraceDemandPrograms
  from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermTracePrograms
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

variable {Fits : Nat → Need → Prop}

noncomputable def RetainedTermProgramCallerData.symbolicTerm
    {state : RetainedTermProgramState env U registry target strata P frontier goal goalOutput}
    (data : RetainedTermProgramCallerData state Fits) : VExpr :=
  state.demand.symbolicReadback data.inputs (callerIndexSubst data.scope.index)

theorem RetainedTermChargedTransitionWitness.callerData_symbolicTerm
    {before after : RetainedTermProgramState env U registry target strata P frontier goal goalOutput}
    (edge : RetainedTermChargedTransitionWitness before after)
    (data : RetainedTermProgramCallerData before Fits)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    (edge.callerData data henv hscoped formed).symbolicTerm = data.symbolicTerm := by
  cases edge with
  | intro annotation sources resources worlds depth smaller demand member path same opening =>
    cases same
    exact (Classical.choice opening.pushed).symbolicReadback _ _ _

theorem RetainedTermDomainTransitionWitness.callerData_symbolicTerm
    {before after : RetainedTermProgramState env U registry target strata P frontier goal goalOutput}
    (edge : RetainedTermDomainTransitionWitness before after)
    (data : RetainedTermProgramCallerData before Fits) :
    (edge.callerData data).symbolicTerm = data.symbolicTerm := by
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

theorem RetainedTermBodyTransitionWitness.callerData_symbolicTerm
    {before after : RetainedTermProgramState env U registry target strata P frontier goal goalOutput}
    (edge : RetainedTermBodyTransitionWitness before after)
    (data : RetainedTermProgramCallerData before Fits)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    (edge.callerData data henv hscoped formed).symbolicTerm = data.symbolicTerm := by
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
      unfold RetainedTermHeadNormalization.nativeInputProgram
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
      unfold RetainedTermHeadNormalization.nativeInputProgram
      cases (normalized.inputPrograms changed).1 <;> rfl
    | succ i => rfl

theorem RetainedTermProgramTransition.callerData_symbolicTerm
    {before after : RetainedTermProgramState env U registry target strata P frontier goal goalOutput}
    (edge : RetainedTermProgramTransition before after) (data : RetainedTermProgramCallerData before Fits)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    (edge.callerData data henv hscoped formed).symbolicTerm = data.symbolicTerm := by
  cases edge with
  | body witness => exact witness.callerData_symbolicTerm data henv hscoped formed
  | domain witness => exact witness.callerData_symbolicTerm data
  | charged witness => exact witness.callerData_symbolicTerm data henv hscoped formed

/-- The exact trace fold identifies terminal source operands symbolically in
caller coordinates. No equality of whole source and caller substitutions is
assumed or needed. -/
theorem RetainedProjectionProgramTrace.callerData_terminalTerm
    {before : RetainedTermProgramState env U registry target strata P frontier goal goalOutput}
    {terminal : RetainedProjectionProgramTerminal env U registry target strata P frontier goal goalOutput}
    (trace : RetainedProjectionProgramTrace env U registry target strata P frontier goal goalOutput before terminal)
    (data : RetainedTermProgramCallerData before Fits)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    let final := trace.callerData data henv hscoped formed
    goal.subst (Subst.lift_l terminal.opening.sourceRenaming (callerIndexSubst final.scope.index)) =
      data.symbolicTerm := by
  induction trace with
  | terminal witness =>
    cases witness with
    | intro opening =>
      have normalized := opening.normalized.symbolicReadback
        (castTraceDemandPrograms opening.expressionEq _ data.inputs) (callerIndexSubst data.scope.index)
      exact normalized.trans (symbolic_transport opening.expressionEq _ data.inputs _)
  | step smaller edge rest ih =>
    exact (ih (edge.callerData data henv hscoped formed)).trans
      (edge.callerData_symbolicTerm data henv hscoped formed)

/-- A visible caller variable cannot originate in a skipped private slot.
The hypothesis is the computed symbolic initial term, not semantic equality. -/
theorem RetainedProjectionProgramTrace.majorIndex
    {before : RetainedTermProgramState env U registry target strata P frontier
      (.proj name index (.bvar caller)) goalOutput}
    {terminal : RetainedProjectionProgramTerminal env U registry target strata P frontier
      (.proj name index (.bvar caller)) goalOutput}
    (trace : RetainedProjectionProgramTrace env U registry target strata P frontier
      (.proj name index (.bvar caller)) goalOutput before terminal)
    (data : RetainedTermProgramCallerData before Fits)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (initial : data.symbolicTerm = .proj name index (.bvar caller)) :
    (trace.callerData data henv hscoped formed).scope.index
      (terminal.opening.sourceRenaming.liftVar caller) = some caller := by
  apply callerIndexExpression_eq_bvar.mp
  have same := (trace.callerData_terminalTerm data henv hscoped formed).trans initial
  exact (VExpr.proj.inj same).2.2

noncomputable def RetainedTermProgramCallerData.ofRichTermOutput
    {sourceEnv : VEnv} {source : List VExpr} {assigned : VExpr}
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {relevant : Bool} {n : Nat} {profile : Profile n} {footprint : Footprint} {goalRank : Nat} {goalOutput : Atom goalRank} {selected : Atom n}
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
    (member : selected ∈ profile.atoms)
    (path : GeneralOutputPath env U registry target selected goalOutput) :
    RetainedTermProgramCallerData
      (RetainedTermProgramState.ofRich ready provenance frame captured data closed substitutions resources
        sourceBelow paid bank (.output path .terminal) member)
      (fun i need => need ∈ available i) :=
  ⟨.initial available, PUnit.unit⟩


theorem RetainedTermProgramCallerData.ofRichTermOutput_symbolicTerm
    {sourceEnv : VEnv} {source : List VExpr} {assigned : VExpr}
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {relevant : Bool} {n : Nat} {profile : Profile n} {footprint : Footprint} {goalRank : Nat} {goalOutput : Atom goalRank} {selected : Atom n}
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
    (member : selected ∈ profile.atoms)
    (path : GeneralOutputPath env U registry target selected goalOutput) :
    (RetainedTermProgramCallerData.ofRichTermOutput ready provenance frame captured data closed substitutions
      resources sourceBelow paid bank member path).symbolicTerm = goal := by
  change goal.subst Subst.id = goal
  simp

/-- Initial literal projection goals retain their actual caller slot through
arbitrary body, domain, resource/action and nested charged transitions. -/
theorem RetainedProjectionProgramTrace.initialProjectionMajorIndex
    {sourceEnv : VEnv} {source : List VExpr} {assigned : VExpr}
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {relevant : Bool} {n : Nat} {profile : Profile n} {footprint : Footprint} {goalRank : Nat} {goalOutput : Atom goalRank} {selected : Atom n}
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
    (member : selected ∈ profile.atoms)
    (path : GeneralOutputPath env U registry target selected goalOutput)
    {terminal : RetainedProjectionProgramTerminal env U registry target strata P frontier goal goalOutput}
    (trace : RetainedProjectionProgramTrace env U registry target strata P frontier goal goalOutput
      (RetainedTermProgramState.ofRich ready provenance frame captured data closed substitutions resources
        sourceBelow paid bank (.output path .terminal) member) terminal)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (projection : goal = .proj name index (.bvar caller)) :
    let initial := RetainedTermProgramCallerData.ofRichTermOutput ready provenance frame captured data closed substitutions
      resources sourceBelow paid bank member path
    (trace.callerData initial henv hscoped formed).scope.index
      (terminal.opening.sourceRenaming.liftVar caller) = some caller := by
  cases projection
  exact trace.majorIndex _ henv hscoped formed
    (RetainedTermProgramCallerData.ofRichTermOutput_symbolicTerm ready provenance frame captured data closed substitutions
      resources sourceBelow paid bank member path)

/-- Plain terminal entry has the same computed identity scope. -/
theorem RetainedTermProgramCallerData.ofRichTerm_symbolicTerm
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
    (RetainedTermProgramCallerData.ofRichTerm ready provenance frame captured data closed substitutions
      resources sourceBelow paid bank member).symbolicTerm = goal := by
  change goal.subst Subst.id = goal
  simp

/-- Plain-terminal specialization; no output action needs to be inserted. -/
theorem RetainedProjectionProgramTrace.initialProjectionMajorIndexPlain
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
    (member : goalOutput ∈ profile.atoms)
    {terminal : RetainedProjectionProgramTerminal env U registry target strata P frontier goal goalOutput}
    (trace : RetainedProjectionProgramTrace env U registry target strata P frontier goal goalOutput
      (RetainedTermProgramState.ofRich ready provenance frame captured data closed substitutions resources
        sourceBelow paid bank .terminal member) terminal)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (projection : goal = .proj name index (.bvar caller)) :
    let initial := RetainedTermProgramCallerData.ofRichTerm ready provenance frame captured data closed substitutions
      resources sourceBelow paid bank member
    (trace.callerData initial henv hscoped formed).scope.index
      (terminal.opening.sourceRenaming.liftVar caller) = some caller := by
  cases projection
  exact trace.majorIndex _ henv hscoped formed
    (RetainedTermProgramCallerData.ofRichTerm_symbolicTerm ready provenance frame captured data closed substitutions
      resources sourceBelow paid bank member)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
