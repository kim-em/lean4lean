import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTraceIndices
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTwoVariableOpening
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPrefix

/-! Initialize a real caller query and retain the same terminal opening,
caller resource map, and runtime anchors. The frame is explicitly diagonal;
no equality between independent left and right substitutions is inferred. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem RetainedProgramTrace.terminalOpening
    {terminal : RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (trace : RetainedProgramTrace env U registry target strata P frontier goalFunction goalArgument goalOutput before terminal) :
    ∃ opening : RetainedApplicationOpening terminal.state, opening.terminal = terminal := by
  induction trace with
  | terminal witness =>
    cases witness with
    | intro opening => exact ⟨opening, rfl⟩
  | step smaller edge rest ih => exact ih

/-- Actual total source execution computes both variable index links and
both semantic anchors for the SAME terminal. All pending body/resource and
charged steps are internal to the trace. -/
theorem EndpointRef.prepareTwoVariableWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    (root : EndpointRef sourceEnv U source
      (.app (.app (.const name levels) (.bvar firstIndex)) (.bvar secondIndex)) assigned)
    (context : ContextDerivation sourceEnv U source)
    (controls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length))
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (substitutions : Ctx.SubstEq env U target σ σ source)
    {query : RichCert sourceEnv env U registry target (.ref root) locals σ relevant profile footprint}
    (ready : ControlledStoredQuery controls frontier (.certificate query))
    (resources : footprint.Available available) (below : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental (.ref root) captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref root) captured]))
    (member : output ∈ profile.atoms)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceClosed : ∀ next ≤ env, P next) :
    let provenance : EndpointProvenance context (.ref root) := .ofLocation .here context
    let initial := RetainedProgramState.ofRich ready provenance frame captured data closed substitutions
      resources below paid bank .application member
    let initialData := RetainedProgramCallerData.ofRichApplication ready provenance frame captured data closed substitutions
      resources below paid bank member
    ∃ terminal : RetainedProgramTerminal env U registry target strata P frontier
        (.app (.const name levels) (.bvar firstIndex)) (.bvar secondIndex) output,
    ∃ trace : RetainedProgramTrace env U registry target strata P frontier
        (.app (.const name levels) (.bvar firstIndex)) (.bvar secondIndex) output initial terminal,
    ∃ opening : RetainedApplicationOpening terminal.state,
      opening.terminal = terminal ∧
      (trace.callerData initialData henv hscoped formed).scope.index
        (opening.sourceRenaming.liftVar firstIndex) = some firstIndex ∧
      (trace.callerData initialData henv hscoped formed).scope.index
        (opening.sourceRenaming.liftVar secondIndex) = some secondIndex ∧
      terminal.state.right (opening.sourceRenaming.liftVar firstIndex) = σ firstIndex ∧
      terminal.state.right (opening.sourceRenaming.liftVar secondIndex) = σ secondIndex := by
  dsimp only
  let provenance : EndpointProvenance context (.ref root) := .ofLocation .here context
  let initial := RetainedProgramState.ofRich ready provenance frame captured data closed substitutions
    resources below paid bank .application member
  obtain ⟨terminal, ⟨trace⟩⟩ := initial.normalizeWithTrace henv hscoped formed sourceClosed
  obtain ⟨opening, same⟩ := trace.terminalOpening
  have rhoEq : opening.sourceRenaming = terminal.sourceRenaming :=
    congrArg RetainedProgramTerminal.sourceRenaming same
  have indices := trace.initialTwoVariableIndices ready provenance frame captured data closed substitutions
    resources below paid bank member henv hscoped formed rfl rfl
  have readback := trace.readback
  change (VExpr.app (.const name levels) (terminal.state.right (terminal.sourceRenaming.liftVar firstIndex)),
    terminal.state.right (terminal.sourceRenaming.liftVar secondIndex)) =
      (VExpr.app (.const name levels) (σ firstIndex), σ secondIndex) at readback
  refine ⟨terminal, trace, opening, same, ?_, ?_, ?_, ?_⟩
  · simpa only [rhoEq] using indices.1
  · simpa only [rhoEq] using indices.2
  · simpa only [rhoEq] using (VExpr.app.inj (congrArg Prod.fst readback)).2
  · simpa only [rhoEq] using congrArg Prod.snd readback

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
