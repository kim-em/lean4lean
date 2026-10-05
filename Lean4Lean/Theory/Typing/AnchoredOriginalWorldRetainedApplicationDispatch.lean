import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedApplicationWitness

/-! Application dispatch returns the exact physical witness or the exact
charged transition. Both preserve the actual incoming request and queries. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem richApplicationProgramStepWitness
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
      demand.readback τ)
    (normalized : RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
      demand (.application ρ functionLevels argumentLevels finalPath)) :
    let state := RetainedProgramState.ofRich ready provenance frame captured data closed substitutions
      resources sourceBelow paid bank demand selected
    (∃ terminal : RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput,
      terminal.readback = demand.readback τ ∧
        Nonempty (RetainedApplicationTerminalWitness state terminal)) ∨
      ∃ next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput,
        next.programSize < sizeOf (show WorldCertProvenance strata query from ready.annotation) ∧
        Nonempty (RetainedChargedTransitionWitness state next) := by
  let state := RetainedProgramState.ofRich ready provenance frame captured data closed substitutions
    resources sourceBelow paid bank demand selected
  obtain ⟨origin, children, ⟨path⟩, supplied, worlds, rooted, smaller, depth, ⟨step⟩⟩ :=
    ready.executeRetainedApplicationSized provenance frame captured data closed formed substitutions
      resources henv hscoped sourceBelow paid bank selected
  cases step with
  | @executed actual answer =>
    obtain ⟨route⟩ := rooted
    cases children with
    | original annotation =>
      let opening : RetainedApplicationOpening state := {
        function := f, argument := a, expressionEq := rfl
        origin := actual, rooted := route, children := annotation
        worlds := worlds, depth := depth, resources := supplied, answer := answer
        sourceRenaming := ρ, functionLevels := functionLevels, argumentLevels := argumentLevels
        selectedPath := path, finalPath := finalPath, normalized := normalized, readback := sameReadback }
      exact .inl ⟨opening.terminal, sameReadback, ⟨.intro opening⟩⟩
  | pending actual =>
    cases children with
    | charged annotation =>
      obtain ⟨next, nextSmaller, readback, witness⟩ := state.openChargedWithWitness annotation
        (annotation.sourcesBelow sourceClosed) supplied worlds depth smaller
        (.output path demand) actual.selected path rfl henv hscoped formed
      exact .inr ⟨next, nextSmaller, witness⟩

theorem legacyApplicationProgramStepWitness
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
      demand.readback τ)
    (normalized : RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
      demand (.application ρ functionLevels argumentLevels finalPath)) :
    let state := RetainedProgramState.ofLegacy annotation within sponsored provenance frame captured data closed
      substitutions resources sourceBelow paid bank demand selected
    ∃ terminal : RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput,
      terminal.readback = demand.readback τ ∧
      Nonempty (RetainedApplicationTerminalWitness state terminal) := by
  let state := RetainedProgramState.ofLegacy annotation within sponsored provenance frame captured data closed
    substitutions resources sourceBelow paid bank demand selected
  obtain ⟨original, children, path, included, worlds, depth⟩ :=
    annotation.certificate.applicationOrigin selected
  let origin := RichAppOrigin.ofSortablePrefix (applicationPrefix provenance.location) original
  have functionReady : ControlledStoredQuery controls frontier (.observation origin.function) := {
    annotation := .legacy original.function children.function
    within := by
      intro control active
      simpa only [StoredOriginalQuery.headDepth, origin, RichAppOrigin.ofSortablePrefix, RichObs.headDepth] using
        Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (depth _) (within control active))
    sponsored := fun world member => sponsored world
      (worlds (List.mem_append_left _ member)) }
  have argumentReady : ControlledStoredQuery controls frontier (.observation origin.argument) := {
    annotation := .legacy original.argument children.argument
    within := by
      intro control active
      simpa only [StoredOriginalQuery.headDepth, origin, RichAppOrigin.ofSortablePrefix, RichObs.headDepth] using
        Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (depth _) (within control active))
    sponsored := fun world member => sponsored world
      (worlds (List.mem_append_right _ member)) }
  have supplied : (origin.functionFootprint ++ origin.argumentFootprint).Available available :=
    fun index need member => resources index need (included member)
  obtain ⟨answer⟩ := origin.executeWorld (applicationPrefix provenance.location).route
    provenance controls frame captured frontier data closed formed substitutions supplied
    functionReady argumentReady henv hscoped sourceBelow paid bank
  obtain ⟨path⟩ := path
  let opening : RetainedApplicationOpening state := {
    function := f, argument := a, expressionEq := rfl
    origin := origin, rooted := (applicationPrefix provenance.location).route
    children := ⟨.legacy original.function children.function, .legacy original.argument children.argument⟩
    worlds := worlds
    depth := by
      intro policy
      simpa only [state, RetainedProgramState.ofLegacy, RetainedTypedProgram.certificate,
        RichCert.headDepth, origin, RichAppOrigin.ofSortablePrefix, RichObs.headDepth] using depth policy
    resources := supplied, answer := answer
    sourceRenaming := ρ, functionLevels := functionLevels, argumentLevels := argumentLevels
    selectedPath := path, finalPath := finalPath, normalized := normalized, readback := sameReadback }
  exact ⟨opening.terminal, sameReadback, ⟨.intro opening⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
