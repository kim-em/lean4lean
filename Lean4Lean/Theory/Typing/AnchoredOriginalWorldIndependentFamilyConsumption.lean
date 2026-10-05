import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyProgramConsumption
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyValueArguments
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilySourceRequests

/-! Consume the actual caller's family prefix against its jointly selected
independent header. The header and all canonical owners stay together; every
stored caller argument retains its original annotation and inherited controls. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- This consumes the retained header directly, without identifying its
original proof with the caller's constant proof. Every header call is proved strictly below the same actual caller; canonical
openings recompute their controls before selecting the next header. -/
theorem WorldFamilyValueSpine.consumeFunded
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (below : sourceEnv ≤ env)
    (captured : WorldEnvironmentProvenance strata U environment)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    (spine : WorldFamilyValueSpine root env registry target locals σ controls frontier
      name levels expression atom footprint)
    (resources : footprint.Available available) (live : spine.ArgumentsLive) :
    Nonempty (WorldFamilyProgramConsumption controls frontier
      (originalCallWorld controls .fundamental (.ref root) captured)
      root registry target locals σ available name levels expression.getAppFnArgs.2 atom) := by
  induction spine with
  | constant query location selected ends nonsortable ready =>
    obtain ⟨seed, ⟨path⟩⟩ := ready.annotation.fundedFamilyProgram
      henv hscoped formed controls below (.ref root) captured .fundamental
      notDefinition notNative selected ends nonsortable ready.within ready.sponsored
    exact ⟨seed.consume henv hscoped formed path⟩
  | app origin function path included argumentReady ih =>
    have all : (origin.functionFootprint ++ origin.argumentFootprint).Available available :=
      fun i need member => resources i need (included member)
    obtain ⟨cursor⟩ := ih (fun i need member => all i need (List.mem_append_left _ member)) live.1
    obtain ⟨next⟩ := cursor.appOrigin henv hscoped formed origin all live.2 path argumentReady
    exact ⟨origin.sourceArguments.symm ▸ next⟩

/-- The full nonsortable function-prefix consumer. Both parsing and the
argument F calls are internal; no retained seed, parsed spine or liveness
certificate is a caller obligation. -/
theorem RichObs.consumeIndependentFamilyFunctionOfBank
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    {n : Nat} {key : Key n} {output : Atom n}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (controls : OriginalWorldControls strata sourceEnv) (below : sourceEnv ≤ env)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental (.ref root) captured])
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    (query : RichObs sourceEnv env U registry target node locals σ (Profile.fn key output) footprint)
    (location : Located root node) (head : expression.getAppFnArgs.1 = .const name levels)
    (ends : FamilyEndDemand output) (resources : footprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.observation query))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref root) captured])) :
    Nonempty (WorldFamilyProgramConsumption controls frontier
      (originalCallWorld controls .fundamental (.ref root) captured)
      root registry target locals σ available name levels expression.getAppFnArgs.2
      (n := n+1) (.fn key output)) := by
  obtain ⟨spine, live⟩ := query.familyFunctionSpineOfBank henv hscoped context controls frame captured
    frontier data closed formed substitutions callerPaid location head ends resources ready bank
  exact spine.consumeFunded henv hscoped formed below captured notDefinition notNative resources live

/-- The actual application branch may end in a sortable family atom. Its
function prefix remains nonsortable, and the final argument is interpreted at
the genuine proper original descendant using the same enclosing bank. -/
theorem RichAppOrigin.consumeIndependentFamilyOfBank
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (origin : RichAppOrigin root env registry target source locals σ f a)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (controls : OriginalWorldControls strata sourceEnv) (below : sourceEnv ≤ env)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental (.ref root) captured])
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    (head : f.getAppFnArgs.1 = .const name levels)
    {requested : Atom n} (ends : FamilyEndDemand requested)
    (path : GeneralOutputPath env U registry target origin.output requested)
    (resources : (origin.functionFootprint ++ origin.argumentFootprint).Available available)
    (functionReady : ControlledStoredQuery controls frontier (.observation origin.function))
    (argumentReady : ControlledStoredQuery controls frontier (.observation origin.argument))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref root) captured])) :
    Nonempty (WorldFamilyProgramConsumption controls frontier
      (originalCallWorld controls .fundamental (.ref root) captured)
      root registry target locals σ available name levels (VExpr.app f a).getAppFnArgs.2 requested) := by
  obtain ⟨function, live⟩ := origin.function.familyFunctionSpineOfBank henv hscoped context controls
    frame captured frontier data closed formed substitutions callerPaid (.appFunction origin.location)
    head (ends.outputBack henv hscoped formed path)
    (fun i need member => resources i need (List.mem_append_left _ member)) functionReady bank
  obtain ⟨argument, _, _⟩ := origin.interpretArgumentWorld context controls frame captured frontier data
    closed formed substitutions callerPaid
    (fun i need member => resources i need (List.mem_append_right _ member)) argumentReady bank
  let spine := WorldFamilyValueSpine.app origin function path (List.Subset.refl _) argumentReady
  exact spine.consumeFunded henv hscoped formed below captured notDefinition notNative
    resources ⟨live, argument.related.live henv hscoped formed⟩

/-- The completed family application yields the actual controlled source request
for every demanded parameter, at the caller's universe instance. -/
theorem RichAppOrigin.fundedFamilyRequestsOfBank
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (origin : RichAppOrigin root env registry target source locals σ f a)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (controls : OriginalWorldControls strata sourceEnv) (below : sourceEnv ≤ env)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental (.ref root) captured])
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    (head : f.getAppFnArgs.1 = .const name levels)
    {demand : FamilyData (Profile n)}
    (path : GeneralOutputPath env U registry target origin.output (show Atom (n+1) from .family demand))
    (resources : (origin.functionFootprint ++ origin.argumentFootprint).Available available)
    (functionReady : ControlledStoredQuery controls frontier (.observation origin.function))
    (argumentReady : ControlledStoredQuery controls frontier (.observation origin.argument))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref root) captured])) :
    WorldFamilyRequestProperty controls frontier root registry target locals σ available
      name levels (VExpr.app f a).getAppFnArgs.2 demand := by
  obtain ⟨cursor⟩ := origin.consumeIndependentFamilyOfBank henv hscoped context controls below
    frame captured frontier data closed formed substitutions callerPaid notDefinition notNative head
    (by trivial) path resources functionReady argumentReady bank
  exact cursor.familyRequests henv hscoped formed

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
