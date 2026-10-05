import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryOperations
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilySeedConsumption
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

/-- Output actions retain the precise original slot spine. The definition
of `.code` chooses only its adapter, never a whole replacement cursor. -/
theorem RichFamilyPlanConsumption.outputPath_queries
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (result : RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments a)
    (path : GeneralOutputPath env U registry target a b)
    (property : RichFamilyQueryPredicate sourceEnv env U registry target source locals σ)
    (ready : result.observed.Queries property) :
    (result.outputPath henv hscoped formed path).observed.Queries property := by
  induction path with
  | refl => exact ready
  | action path action ih => exact ih
  | code path action sorted ih => exact ih
  | pad path ih => exact ih
  | unpad path ih => exact ih

theorem RichFamilyPlanConsumption.appOriginPreserving
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (origin : RichAppOrigin root env registry target source locals σ f a)
    (result : RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments (n := origin.rank + 1) (.fn origin.key origin.output))
    (resources : (origin.functionFootprint ++ origin.argumentFootprint).Available available)
    (live : Profile.Live env U registry target origin.rawInput)
    (path : GeneralOutputPath env U registry target origin.output requested)
    {property : RichFamilyQueryPredicate sourceEnv env U registry target source locals σ}
    (raises : ∀ {expression assigned : VExpr} {node : EndpointState sourceEnv U source expression assigned}
      {n N : Nat} {profile : Profile n} {footprint : Footprint}
      (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
      (bound : n ≤ N), property query → property (query.raise bound))
    (prior : result.observed.Queries property) (argument : property origin.argument) :
    ∃ next : RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature (arguments ++ [a]) requested, next.observed.Queries property := by
  obtain ⟨next, controlled⟩ := result.appPreserving henv hscoped below formed
    (.appArgument origin.location) origin.argument
    (fun i need member => resources i need (List.mem_append_right _ member))
    live origin.arguments origin.admitted raises prior argument
  exact ⟨next.outputPath henv hscoped formed path,
    next.outputPath_queries henv hscoped formed path property controlled⟩

/-- The property used below includes the positive annotation, fuel bound,
and the SAME inherited sponsor frontier. -/
abbrev ControlledFamilyQuery
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length)) :
    RichFamilyQueryPredicate sourceEnv env U registry target source locals σ :=
  fun query => Nonempty (ControlledStoredQuery controls frontier (.observation query))

theorem RichAppOrigin.sourceArguments
    (_origin : RichAppOrigin root env registry target source locals σ f a) :
    (VExpr.app f a).getAppFnArgs.2 = f.getAppFnArgs.2 ++ [a] := by
  simp only [getAppFnArgs_app]

theorem RichFamilyPlanConsumption.castArguments_queries
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    (same : arguments = nextArguments)
    (result : RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments requested)
    (property : RichFamilyQueryPredicate sourceEnv env U registry target source locals σ)
    (ready : result.observed.Queries property) :
    (same ▸ result : RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature nextArguments requested).observed.Queries property := by
  cases same
  exact ready


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
