import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProjectionRecipeEntry
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermTraceIndices
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldProjectionDemandReturn

/-! Compile the actual retained projection program back to a caller variable
major. The terminal, finite scope and source index correspondence are computed
from the initial query. The result retains the terminal's exact record and
request; it does not assert a caller field certificate. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private appendPath from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermDemandHead
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

section
variable
  {strata : EquationStratification env} {P : VEnv → Prop}
  {context : ContextDerivation callerEnv U callerSource}
  {callerNode : EndpointState callerEnv U callerSource (.proj name index (.bvar caller)) callerAssigned}
  (callerHead : ProjectionHead callerNode)
  (controls : OriginalWorldControls strata callerEnv)
  (frontier : List (World strata.rules.length))
  {m : Nat} (output : Atom m)
  (terminal : RetainedProjectionProgramTerminal env U registry target strata P frontier
    (.proj name index (.bvar caller)) output)

/-- Exact output of the terminal's caller-major call, indexed by the SAME
terminal record/request selected in the actual source trace. -/
structure RetainedProjectionDemandResult
    (locals : List Nat) (σ τ : Subst) (available : Valuation) where
  nameEq : terminal.opening.origin.record.family.name = name
  member : (index, terminal.opening.origin.request) ∈ terminal.opening.origin.record.fields
  query : RichGradedResult callerEnv env U registry target (.ref (.right callerHead.major))
    locals σ available (Profile.singleton (n := terminal.opening.origin.rank+1)
      (.record terminal.opening.origin.record))
  queryReady : ControlledStoredQuery controls frontier (.observation query.observation)
  value : RichComputationalValue callerEnv env U registry target (.ref (.right callerHead.major))
    locals σ τ available (Profile.singleton (n := terminal.opening.origin.rank+1)
      (.record terminal.opening.origin.record))
  certificateReady : ControlledStoredQuery controls frontier (.certificate value.certificate)
  valueReady : ControlledStoredQuery controls frontier (.observation value.rightQuery.observation)
  admitted : RankedData.RequestAdmission env U (relations env U registry terminal.opening.origin.rank)
    target terminal.opening.origin.request (.proj name index (σ caller)) (.proj name index (τ caller))
  outputAdmitted : Admitted env U registry target
    (show Key m from ⟨terminal.opening.origin.request.domain, terminal.opening.origin.request.anchor,
      Profile.singleton output⟩) (.proj name index (σ caller)) (.proj name index (τ caller))

private theorem returnTerminal
    (scope : CallerVariableProgramScope env U registry target
      (fun i need => need ∈ available i) terminal.state.available)
    (mapped : scope.index (terminal.opening.sourceRenaming.liftVar caller) = some caller)
    (provenance : EndpointProvenance context callerNode)
    (frame : OriginalRichFrame callerEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (substitutions : Ctx.SubstEq env U target σ τ callerSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (paid : Sponsored frontier [originalCallWorld controls .fundamental callerNode captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental callerNode captured])) :
    Nonempty (RetainedProjectionDemandResult callerHead controls frontier output terminal locals σ τ available) := by
  rcases terminal with ⟨state, opening⟩
  rcases opening with ⟨sourceName, sourceIndex, sourceMajor, expressionEq, origin, rooted,
    children, worlds, depth, resources, answer, ρ, levels, selectedPath, finalPath, normalized, readback⟩
  change EqUpToLevels U (.proj sourceName sourceIndex sourceMajor)
    (.proj name index (.bvar (ρ.liftVar caller))) at levels
  cases levels with
  | proj majorLevels =>
    cases majorLevels
    obtain ⟨query, queryReady, value, ⟨certificateReady⟩, ⟨valueReady⟩, admitted, outputAdmitted⟩ :=
      origin.returnVariableDemandWorld scope resources state.closed mapped callerHead provenance controls
        frame captured frontier data closed substitutions henv hscoped formed paid bank
        (appendPath selectedPath finalPath)
    exact ⟨⟨origin.nameEq,origin.member,query,queryReady,value,certificateReady,valueReady,admitted,outputAdmitted⟩⟩

/-- Normalize an actual caller certificate, compute its complete finite caller
scope, and execute the terminal request at the proper original caller major. -/
theorem ControlledStoredQuery.compileProjectionVariableDemandWorld
    {query : RichCert callerEnv env U registry target callerNode locals σ relevant profile footprint}
    (ready : ControlledStoredQuery controls frontier (.certificate query))
    (provenance : EndpointProvenance context callerNode)
    (frame : OriginalRichFrame callerEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (substitutions : Ctx.SubstEq env U target σ τ callerSource)
    (resources : footprint.Available available)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceBelow : callerEnv ≤ env) (sourceClosed : ∀ next ≤ env, P next)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental callerNode captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental callerNode captured]))
    (selected : atom ∈ profile.atoms)
    (path : GeneralOutputPath env U registry target atom output) :
    ∃ terminal : RetainedProjectionProgramTerminal env U registry target strata P frontier
        (.proj name index (.bvar caller)) output,
      Nonempty (RetainedProjectionProgramTrace env U registry target strata P frontier
        (.proj name index (.bvar caller)) output
        (RetainedTermProgramState.ofRich ready provenance frame captured data closed substitutions
          resources sourceBelow paid bank (.output path .terminal) selected) terminal) ∧
      Nonempty (RetainedProjectionDemandResult callerHead controls frontier output terminal locals σ τ available) := by
  let state := RetainedTermProgramState.ofRich ready provenance frame captured data closed substitutions
    resources sourceBelow paid bank (.output path .terminal) selected
  obtain ⟨terminal, ⟨trace⟩⟩ := state.normalizeProjectionWithTrace henv hscoped formed sourceClosed
  let initial := RetainedTermProgramCallerData.ofRichTermOutput ready provenance frame captured data closed substitutions
    resources sourceBelow paid bank selected path
  let final := trace.callerData initial henv hscoped formed
  have mapped := trace.initialProjectionMajorIndex ready provenance frame captured data closed substitutions
    resources sourceBelow paid bank selected path henv hscoped formed rfl
  exact ⟨terminal, ⟨trace⟩, returnTerminal callerHead controls frontier output terminal final.scope mapped
    provenance frame captured data closed substitutions henv hscoped formed paid bank⟩

/-- Start from the exact selected charged recipe of a caller projection query.
The actual trace, scope, renamed source index and caller-major F are all
constructed internally from its inherited readiness and lower bank. -/
theorem WorldCodeRecipeProvenance.compileProjectionVariableDemandWorld
    {recipe : RichCodeRecipe env U registry target callerSource locals σ
      (.proj name index (.bvar caller)) relevant profile footprint}
    (annotation : WorldCodeRecipeProvenance strata recipe)
    {incoming : StoredOriginalQuery env U registry target}
    (ready : ControlledStoredQuery controls frontier incoming)
    (worlds : annotation.worlds ⊆ ready.annotation.worlds)
    (depth : ∀ policy, recipe.headDepth policy ≤ incoming.headDepth policy)
    (provenance : EndpointProvenance context callerNode)
    (frame : OriginalRichFrame callerEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (substitutions : Ctx.SubstEq env U target σ τ callerSource)
    (resources : footprint.Available available)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceBelow : callerEnv ≤ env) (sourceClosed : ∀ next ≤ env, P next)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental callerNode captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental callerNode captured]))
    (selected : atom ∈ profile.atoms)
    (path : GeneralOutputPath env U registry target atom output) :
    ∃ recipeReady : ControlledStoredQuery controls frontier
        (.certificate (RichCert.recipe (node := callerNode) recipe)),
      recipeReady.annotation = .recipe annotation ∧
      ∃ terminal : RetainedProjectionProgramTerminal env U registry target strata P frontier
          (.proj name index (.bvar caller)) output,
        Nonempty (RetainedProjectionProgramTrace env U registry target strata P frontier
          (.proj name index (.bvar caller)) output
          (RetainedTermProgramState.ofRich recipeReady provenance frame captured data closed substitutions
            resources sourceBelow paid bank (.output path .terminal) selected) terminal) ∧
        Nonempty (RetainedProjectionDemandResult callerHead controls frontier output terminal locals σ τ available) := by
  obtain ⟨recipeReady, same, terminal, ⟨trace⟩, readback⟩ := annotation.projectionProgramFromQueryWorld ready
    worlds depth provenance frame captured data closed formed substitutions resources henv hscoped sourceBelow
    sourceClosed paid bank selected path
  let initial := RetainedTermProgramCallerData.ofRichTermOutput recipeReady provenance frame captured data closed substitutions
    resources sourceBelow paid bank selected path
  let final := trace.callerData initial henv hscoped formed
  have mapped := trace.initialProjectionMajorIndex recipeReady provenance frame captured data closed substitutions
    resources sourceBelow paid bank selected path henv hscoped formed rfl
  exact ⟨recipeReady,same,terminal,⟨trace⟩,
    returnTerminal callerHead controls frontier output terminal final.scope mapped provenance frame captured data
      closed substitutions henv hscoped formed paid bank⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
