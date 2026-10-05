import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProjectionProgramTrace

/-! A selected charged projection observation enters the compiler through
its own literal recipe. The ambient observation need not have a sortable
profile: only the selected recipe supplies the certificate constructor. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- Build and normalize the literal recipe selected from an actual incoming
projection query. All caller data are unchanged; the trace begins with the
selected finite output path, not with an assumed physical projection. -/
theorem WorldCodeRecipeProvenance.projectionProgramFromQueryWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {recipe : RichCodeRecipe env U registry target source locals σ (.proj name index value)
      relevant profile footprint}
    (annotation : WorldCodeRecipeProvenance strata recipe)
    {incoming : StoredOriginalQuery env U registry target}
    (ready : ControlledStoredQuery controls frontier incoming)
    (worlds : annotation.worlds ⊆ ready.annotation.worlds)
    (depth : ∀ policy, recipe.headDepth policy ≤ incoming.headDepth policy)
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
    (selected : atom ∈ profile.atoms)
    (path : GeneralOutputPath env U registry target atom goalOutput) :
    ∃ recipeReady : ControlledStoredQuery controls frontier
        (.certificate (RichCert.recipe (node := node) recipe)),
      recipeReady.annotation = .recipe annotation ∧
      ∃ terminal : RetainedProjectionProgramTerminal env U registry target strata P frontier
          (.proj name index value) goalOutput,
        Nonempty (RetainedProjectionProgramTrace env U registry target strata P frontier
          (.proj name index value) goalOutput
          (RetainedTermProgramState.ofRich recipeReady provenance frame captured data closed substitutions
            resources sourceBelow paid bank (.output path .terminal) selected) terminal) ∧
        terminal.readback = (VExpr.proj name index value).subst τ := by
  let recipeReady : ControlledStoredQuery controls frontier
      (.certificate (RichCert.recipe (node := node) recipe)) := {
    annotation := .recipe annotation
    within := by
      intro control active
      simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using
        Nat.le_trans (depth (stratifiedHeadPolicy (strata.headOrdinal registry) control)) (ready.within control active)
    sponsored := fun world member => ready.sponsored world (worlds member) }
  let state := RetainedTermProgramState.ofRich recipeReady provenance frame captured data closed substitutions
    resources sourceBelow paid bank (.output path .terminal) selected
  obtain ⟨terminal, ⟨trace⟩⟩ := state.normalizeProjectionWithTrace henv hscoped formed sourceClosed
  exact ⟨recipeReady, rfl, terminal, ⟨trace⟩, trace.readback⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
