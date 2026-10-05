import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationOrigins
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilySourceParsing

/-! The finite source parser keeps the actual argument queries' controls
and sponsors. Argument F calls lower their original endpoint while the
inherited sponsor frontier stays fixed; no copied sponsor is reintroduced
as a new measured token. This result does not identify a legacy query's
header annotation with the independently computed original header seed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- Each application stores control evidence for its actual retained
argument observer, including foreign query-owned opening sites. -/
inductive RetainedRichFamilySpine.ControlledArguments
    {env : VEnv} {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length))
    {root : EndpointRef sourceEnv U source rootExpression rootType} :
    {expression : VExpr} → {n : Nat} → {atom : Atom n} → {footprint : Footprint} →
    RetainedRichFamilySpine root env registry target locals σ name levels expression atom footprint → Type where
  | constant (seed : RetainedRichFamilySeed root env registry target name levels)
      (path : GeneralOutputPath env U registry target seed.atom atom) :
      ControlledArguments controls frontier (.constant (footprint := footprint) seed path)
  | app (origin : RichAppOrigin root env registry target source locals σ f a)
      {function : RetainedRichFamilySpine root env registry target locals σ name levels
        f (n := origin.rank + 1) (.fn origin.key origin.output) origin.functionFootprint}
      (path : GeneralOutputPath env U registry target origin.output atom)
      (included : List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint)
      (prior : ControlledArguments controls frontier function)
      (argument : ControlledStoredQuery controls frontier (.observation origin.argument)) :
      ControlledArguments controls frontier (.app origin function path included)

/-- Parse the same original query while retaining controls on each exact
argument observer. The constant leaf uses the existing genuine original
header selector, not an assumed normalized family telescope. -/
theorem RichObs.familySourceSpineControlled
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    {demand : Profile n}
    (query : RichObs sourceEnv env U registry target node locals σ demand footprint)
    (location : Located root node)
    (head : expression.getAppFnArgs.1 = .const name levels)
    (member : atom ∈ demand.atoms) (ends : FamilyEndDemand atom)
    (ready : ControlledStoredQuery controls frontier (.observation query)) :
    ∃ spine : RetainedRichFamilySpine root env registry target locals σ name levels expression atom footprint,
      Nonempty (spine.ControlledArguments controls frontier) := by
  match expression with
  | .const found foundLevels =>
    simp only [getAppFnArgs_const] at head
    cases head
    obtain ⟨seed, ⟨path⟩⟩ := query.familyConstantOrigin henv hscoped formed ordered below
      notDefinition notNative location member ends
    exact ⟨.constant seed path, ⟨.constant seed path⟩⟩
  | .app f a =>
    obtain ⟨origin, children, ⟨path⟩, included, sponsored, depth⟩ :=
      ready.annotation.applicationOrigin location member
    have functionReady : ControlledStoredQuery controls frontier (.observation origin.function) :=
      ⟨children.function,
        fun control active => Nat.le_trans
          (Nat.le_trans (Nat.le_max_left _ _) (depth _)) (ready.within control active),
        fun world selected => ready.sponsored world (sponsored (List.mem_append_left _ selected))⟩
    have argumentReady : ControlledStoredQuery controls frontier (.observation origin.argument) :=
      ⟨children.argument,
        fun control active => Nat.le_trans
          (Nat.le_trans (Nat.le_max_right _ _) (depth _)) (ready.within control active),
        fun world selected => ready.sponsored world (sponsored (List.mem_append_right _ selected))⟩
    have outputEnds : FamilyEndDemand origin.output := ends.outputBack henv hscoped formed path
    obtain ⟨function, ⟨controlled⟩⟩ := origin.function.familySourceSpineControlled
      henv hscoped formed ordered below notDefinition notNative (.appFunction origin.location)
      (by simpa only [getAppFnArgs_app] using head) (List.mem_singleton_self _) outputEnds functionReady
    exact ⟨.app origin function path included,
      ⟨.app origin path included controlled argumentReady⟩⟩
  | .bvar _ | .sort _ | .lam _ _ | .forallE _ _ | .proj _ _ _ | .elim _ _ _ =>
    simp [getAppFnArgs, getAppFnArgs.go] at head
termination_by sizeOf expression

/-- Inherited sponsors remain in place while the actual argument call
strictly lowers the final original endpoint. -/
theorem RichAppOrigin.argumentWorldBelowWithSponsors
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (origin : RichAppOrigin root env registry target source locals σ f a)
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase)
    (frontier : List (World strata.rules.length)) :
    CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental origin.argumentNode captured])
      (frontier ++ [originalCallWorld controls phase (.ref root) captured]) := by
  induction frontier with
  | nil => exact origin.argumentWorldBelow controls captured phase
  | cons sponsor rest ih => exact ih.cons sponsor

/-- A genuine qualified original F clause, at the exact retained argument
query. It asks for no family answer, alignment, liveness, or header plan. -/
def WorldFamilySourceArgumentCalls
    (env : VEnv) {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase)
    (frontier : List (World strata.rules.length))
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation) : Prop :=
  ∀ {f a} (origin : RichAppOrigin root env registry target source locals σ f a),
    CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental origin.argumentNode captured])
      (frontier ++ [originalCallWorld controls phase (.ref root) captured]) →
    origin.argumentFootprint.Available available →
    ControlledStoredQuery controls frontier (.observation origin.argument) →
    Nonempty (RichComputationalValue sourceEnv env U registry target origin.argumentNode
      locals σ σ available origin.rawInput)

theorem RetainedRichFamilySpine.ControlledArguments.liveOfCalls
    {strata : EquationStratification env}
    {frontier : List (World strata.rules.length)}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase)
    {spine : RetainedRichFamilySpine root env registry target locals σ name levels expression atom footprint}
    (controlled : spine.ControlledArguments controls frontier)
    (resources : footprint.Available available)
    (calls : WorldFamilySourceArgumentCalls (root := root) env controls captured phase frontier
      registry target locals σ available) : spine.ArgumentsLive := by
  induction controlled with
  | constant => trivial
  | app origin path included prior argumentReady ih =>
    have all : (origin.functionFootprint ++ origin.argumentFootprint).Available available :=
      fun i need member => resources i need (included member)
    obtain ⟨answer⟩ := calls origin (origin.argumentWorldBelowWithSponsors controls captured phase frontier)
      (fun i need member => all i need (List.mem_append_right _ member)) argumentReady
    exact ⟨ih hscoped formed (fun i need member => all i need (List.mem_append_left _ member)) calls,
      answer.related.live henv hscoped formed⟩

/-- The full parser/consumer obtains liveness from properly decreasing,
sponsored original argument F calls. The returned consumption retains the
same seed and argument source queries as its controlled finite trace. -/
theorem RichObs.consumeRetainedFamilyControlled
    {strata : EquationStratification env}
    {frontier : List (World strata.rules.length)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (controls : OriginalWorldControls strata sourceEnv) (below : sourceEnv ≤ env)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    {demand : Profile n}
    (query : RichObs sourceEnv env U registry target node locals σ demand footprint)
    (location : Located root node)
    (head : expression.getAppFnArgs.1 = .const name levels)
    (member : atom ∈ demand.atoms) (ends : FamilyEndDemand atom)
    (resources : footprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.observation query))
    (calls : WorldFamilySourceArgumentCalls (root := root) env controls captured phase frontier
      registry target locals σ available) :
    ∃ spine : RetainedRichFamilySpine root env registry target locals σ name levels expression atom footprint,
      Nonempty (spine.ControlledArguments controls frontier) ∧
      ∃ result : RetainedRichFamilyConsumption root env registry target locals σ available
        name levels expression.getAppFnArgs.2 atom, result.seed = spine.seed := by
  obtain ⟨spine, ⟨controlled⟩⟩ := query.familySourceSpineControlled henv hscoped formed controls.ordered
    below notDefinition notNative location head member ends ready
  obtain ⟨result, same⟩ := spine.consume henv hscoped below formed resources
    (controlled.liveOfCalls henv hscoped formed controls captured phase resources calls)
  exact ⟨spine, ⟨controlled⟩, result, same⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
