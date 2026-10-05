import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedReadbackOpening
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramLegacyApplication

/-! Application execution preserves the operand readback on the SAME selected
physical answer or smaller charged program. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
open private appendTerminalPath from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramApplication
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

noncomputable def RetainedProgramTerminal.readback
    (terminal : RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput) :
    VExpr × VExpr :=
  (goalFunction.subst (Subst.lift_l terminal.sourceRenaming terminal.state.right),
   goalArgument.subst (Subst.lift_l terminal.sourceRenaming terminal.state.right))

theorem richApplicationProgramStepReadback
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint}
    (ready : ControlledStoredQuery controls frontier (.certificate query))
    (provenance : EndpointProvenance context node)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : footprint.Available available)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (sourceClosed : ∀ next ≤ env, P next)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput (.app f a) atom)
    (selected : atom ∈ profile.atoms)
    (ρ : Lift) (functionLevels : EqUpToLevels U f (goalFunction.lift' ρ))
    (argumentLevels : EqUpToLevels U a (goalArgument.lift' ρ))
    (finalPath : GeneralOutputPath env U registry target atom goalOutput)
    (sameReadback : (goalFunction.subst (Subst.lift_l ρ τ), goalArgument.subst (Subst.lift_l ρ τ)) =
      demand.readback τ) :
    (∃ terminal : RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput,
      terminal.readback = demand.readback τ) ∨
      ∃ next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput,
        next.programSize < sizeOf (show WorldCertProvenance strata query from ready.annotation) ∧
        next.demand.readback next.right = demand.readback τ := by
  let state := RetainedProgramState.ofRich ready provenance frame captured data closed substitutions
    resources sourceBelow paid bank demand selected
  obtain ⟨origin, children, ⟨path⟩, supplied, worlds, rooted, smaller, depth, ⟨step⟩⟩ :=
    ready.executeRetainedApplicationSized provenance frame captured data closed formed substitutions
      resources henv hscoped sourceBelow paid bank selected
  cases step with
  | @executed actual answer =>
    obtain ⟨route⟩ := rooted
    exact .inl ⟨{
      state := state, function := f, argument := a, expressionEq := rfl
      origin := actual, rooted := route, answer := answer
      sourceRenaming := ρ, functionLevels := functionLevels, argumentLevels := argumentLevels
      output := appendTerminalPath path finalPath }, sameReadback⟩
  | pending actual =>
    cases children with
    | charged annotation =>
      obtain ⟨next, nextSmaller, readback⟩ := state.openChargedReadback annotation
        (annotation.sourcesBelow sourceClosed) supplied worlds depth smaller
        (.output path demand) actual.selected henv hscoped formed
      exact .inr ⟨next, nextSmaller, readback⟩

theorem legacyApplicationProgramStepReadback
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {query : LegacyRowBody env U registry target locals σ (.app f a) relevant profile footprint}
    (annotation : WorldLegacyRowBodyProvenance strata query)
    (within : WithinAbove controls.cutoff controls.fuel
      (fun control => query.certificate.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier annotation.certificate.worlds)
    (provenance : EndpointProvenance context node)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : footprint.Available available)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput (.app f a) atom)
    (selected : atom ∈ profile.atoms)
    (ρ : Lift) (functionLevels : EqUpToLevels U f (goalFunction.lift' ρ))
    (argumentLevels : EqUpToLevels U a (goalArgument.lift' ρ))
    (finalPath : GeneralOutputPath env U registry target atom goalOutput)
    (sameReadback : (goalFunction.subst (Subst.lift_l ρ τ), goalArgument.subst (Subst.lift_l ρ τ)) =
      demand.readback τ) :
    ∃ terminal : RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput,
      terminal.readback = demand.readback τ := by
  let ready : ControlledStoredQuery controls frontier
      (.certificate (RichCert.legacy (node := node) query.certificate)) := {
    annotation := .legacy query.certificate annotation.certificate
    within := by simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using within
    sponsored := sponsored }
  let state := RetainedProgramState.ofRich ready provenance frame captured data closed substitutions
    resources sourceBelow paid bank demand selected
  obtain ⟨origin, ⟨route⟩, ⟨path⟩, ⟨answer⟩⟩ := annotation.executeApplicationWorld within sponsored
    provenance frame captured data closed formed substitutions resources henv hscoped sourceBelow paid bank selected
  exact ⟨{
    state := state, function := f, argument := a, expressionEq := rfl
    origin := origin, rooted := route, answer := answer
    sourceRenaming := ρ, functionLevels := functionLevels, argumentLevels := argumentLevels
    output := appendTerminalPath path finalPath }, sameReadback⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
