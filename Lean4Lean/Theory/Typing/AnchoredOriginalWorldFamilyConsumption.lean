import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyConsumptionOperations
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilySourceParsing
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeHeadDepth

/-! Consumption preserves annotations on the actual stored argument
observers. Grade changes retain the SAME query's opening sites; finite
variable programs change only the adapter around that observer. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem RetainedRichFamilySpine.ControlledArguments.consume
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    {spine : RetainedRichFamilySpine root env registry target locals σ name levels expression atom footprint}
    (controlled : spine.ControlledArguments controls frontier)
    (resources : footprint.Available available) (live : spine.ArgumentsLive) :
    ∃ result : RetainedRichFamilyConsumption root env registry target locals σ available
      name levels expression.getAppFnArgs.2 atom,
      result.seed = spine.seed ∧ result.cursor.observed.Queries (ControlledFamilyQuery controls frontier) := by
  induction controlled with
  | constant seed path =>
    refine ⟨seed.initial.outputPath henv hscoped formed path, rfl, ?_⟩
    exact seed.initial.cursor.outputPath_queries henv hscoped formed path _ trivial
  | app origin path included prior argumentReady ih =>
    have all : (origin.functionFootprint ++ origin.argumentFootprint).Available available :=
      fun i need member => resources i need (included member)
    obtain ⟨result, same, controlled⟩ := ih hscoped formed
      (fun i need member => all i need (List.mem_append_left _ member)) live.1
    obtain ⟨next, nextControlled⟩ := result.cursor.appOriginPreserving henv hscoped
      (result.seed.origin.sourceBelow.trans below) formed origin all live.2 path
      (property := ControlledFamilyQuery controls frontier)
      (fun _ bound ready => ready.elim (fun value => value.raise bound)) controlled ⟨argumentReady⟩
    have argumentsEq := origin.sourceArguments
    refine ⟨{ seed := result.seed, cursor := argumentsEq.symm ▸ next }, same, ?_⟩
    exact next.castArguments_queries argumentsEq.symm _ nextControlled

/-- The source parser now returns a cursor whose actual stored observers
carry the inherited controls. All liveness comes from proper original F. -/
theorem RichObs.consumeRetainedFamilyWorld
    {strata : EquationStratification env}
    {frontier : List (World strata.rules.length)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (controls : OriginalWorldControls strata sourceEnv) (below : sourceEnv ≤ env)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned} {demand : Profile n}
    (query : RichObs sourceEnv env U registry target node locals σ demand footprint)
    (location : Located root node) (head : expression.getAppFnArgs.1 = .const name levels)
    (member : atom ∈ demand.atoms) (ends : FamilyEndDemand atom)
    (resources : footprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.observation query))
    (calls : WorldFamilySourceArgumentCalls (root := root) env controls captured phase frontier
      registry target locals σ available) :
    ∃ result : RetainedRichFamilyConsumption root env registry target locals σ available
      name levels expression.getAppFnArgs.2 atom,
      result.cursor.observed.Queries (ControlledFamilyQuery controls frontier) := by
  obtain ⟨spine, ⟨controlled⟩⟩ := query.familySourceSpineControlled henv hscoped formed controls.ordered
    below notDefinition notNative location head member ends ready
  obtain ⟨result, _, preserved⟩ := controlled.consume henv hscoped below formed resources
    (controlled.liveOfCalls henv hscoped formed controls captured phase resources calls)
  exact ⟨result, preserved⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
