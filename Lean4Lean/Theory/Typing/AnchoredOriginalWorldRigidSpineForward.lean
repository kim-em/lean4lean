import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidSpineInitialization
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldGradedApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalRichComputationalPrefix

/-! Forward reconstruction of the exact finite backward initializer. The
only leaf input is one concrete query at the trace's actual primitive
constant. Every application uses the retained argument query and request,
and every conversion uses its retained original route. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000

private theorem moveQueryFrame
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    (query : RichGradedResult sourceEnv env U registry target node firstLocals σ firstAvailable profile)
    (ready : ControlledStoredQuery controls frontier (.observation query.observation))
    (localsEq : firstLocals = nextLocals)
    (included : ∀ index need, need ∈ firstAvailable index → need ∈ nextAvailable index) :
    ∃ next : RichGradedResult sourceEnv env U registry target node nextLocals σ nextAvailable profile,
      Nonempty (ControlledStoredQuery controls frontier (.observation next.observation)) := by
  cases localsEq
  exact ⟨query.availableMono included, ⟨ready⟩⟩

private theorem restoreQueryRoute
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    (route : PrefixRoute sourceEnv U source expression first last)
    (query : RichGradedResult sourceEnv env U registry target last locals σ available profile)
    (ready : ControlledStoredQuery controls frontier (.observation query.observation)) :
    Nonempty (ControlledStoredQuery controls frontier
      (.observation (query.restoreRoute route).observation)) := by
  refine ⟨⟨.route route ready.annotation, ?_, ready.sponsored⟩⟩
  intro control active
  simpa only [RichGradedResult.restoreRoute, StoredOriginalQuery.headDepth, RichObs.headDepth]
    using ready.within control active

private theorem castQueryProfile
    {strata : EquationStratification env} {profile nextProfile : Profile n}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    (query : RichGradedResult sourceEnv env U registry target node locals σ available profile)
    (ready : ControlledStoredQuery controls frontier (.observation query.observation))
    (equal : profile = nextProfile) :
    ∃ next : RichGradedResult sourceEnv env U registry target node locals σ available nextProfile,
      Nonempty (ControlledStoredQuery controls frontier (.observation next.observation)) := by
  cases equal
  exact ⟨query, ⟨ready⟩⟩

/-- The finite trace is executed forwards on its exact retained frames. The
primitive query is a single syntactic input, not a supplier for recursive
answers. The result returns to the original input's SAME resource table and
inherits the original finite world frontier throughout. -/
theorem WorldRigidBackwardTrace.forward
    {registry : CanonicalHead.Registry} {target source : List VExpr}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {initial : ContextDerivation sourceEnv U rootSource}
    {controls : OriginalWorldControls strata sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
    {frontier : List (World strata.rules.length)}
    {node : EndpointState sourceEnv U source expression assigned} {location : Located root node}
    {prepared : RigidFamilySpine.Prepared env U registry target name levels (profile : Profile n)}
    {input : WorldAssignedQuery (registry := registry) (target := target)
      (context := location.contextDerivation initial) P controls baseline frontier node σ τ relevant profile}
    (trace : WorldRigidBackwardTrace (source := source) (P := P) initial controls baseline frontier
      σ τ name levels node location prepared input)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (leaf : RichGradedResult sourceEnv env U registry target (.ref trace.primitiveSeed.reference)
      trace.primitiveSeed.input.locals σ trace.primitiveSeed.input.available
      (.singleton (trace.primitiveSeed.prepared.plan.atom name levels [])))
    (leafReady : ControlledStoredQuery controls frontier (.observation leaf.observation)) :
    ∃ past : List RigidFamilyArgument,
    ∃ query : RichGradedResult sourceEnv env U registry target node input.locals σ input.available
        (.singleton (prepared.plan.atom name levels past)),
      Nonempty (ControlledStoredQuery controls frontier (.observation query.observation)) := by
  induction trace with
  | constant head primitive funded sameLocals included =>
    obtain ⟨leafAtInput, ⟨readyAtInput⟩⟩ := moveQueryFrame leaf leafReady sameLocals included
    obtain ⟨restoredReady⟩ := restoreQueryRoute head.route leafAtInput readyAtInput
    exact ⟨[], leafAtInput.restoreRoute head.route, ⟨restoredReady⟩⟩
  | application domain body function argument result hu hv route natural sameLocals included step tail ih =>
    rename_i node location prepared input
    obtain ⟨past, fn, ⟨fnReady⟩⟩ := ih leaf leafReady
    obtain ⟨fnAtInput, ⟨fnAtInputReady⟩⟩ :=
      moveQueryFrame fn fnReady step.nextLocals step.nextAvailable
    have functionProfile :
        Profile.singleton (step.nextPrepared.plan.atom name levels past) =
          Profile.fn step.packed.request.key
            (raiseAtom step.packed.request.rank step.packed.request.bound
              (prepared.plan.atom name levels
                (past ++ [⟨step.packed.request.key.domain, step.packed.request.key.anchor⟩]))) := by
      rw [step.plan_eq]
      simp only [RigidFamilySpine.atom, RigidFamilySpine.atom_raise]
      rfl
    obtain ⟨actualFn, ⟨actualFnReady⟩⟩ := castQueryProfile fnAtInput fnAtInputReady functionProfile
    obtain ⟨applied, appliedReady, _worlds, _footprint, _depth⟩ :=
      RichGradedResult.appControlled henv hscoped formed natural.closed (.ref domain) body result hu hv
        actualFn step.packed.argumentQuery (.refl _) step.packed.request.admitted controls
        actualFnReady step.packedReady.argument
    let nextPast := past ++ [⟨step.packed.request.key.domain, step.packed.request.key.anchor⟩]
    have outputProfile : Profile.singleton
        (raiseAtom step.packed.request.rank step.packed.request.bound (prepared.plan.atom name levels nextPast)) =
        raiseProfile step.packed.request.rank step.packed.request.bound
          (Profile.singleton (prepared.plan.atom name levels nextPast)) :=
      (raiseProfile_singleton _ _).symm
    obtain ⟨raised, ⟨raisedReady⟩⟩ := castQueryProfile applied appliedReady outputProfile
    let lowered := raised.adaptRequest henv hscoped formed step.packed.request.bound (.refl _)
    have loweredReady : ControlledStoredQuery controls frontier (.observation lowered.observation) := raisedReady
    obtain ⟨restoredReady⟩ := restoreQueryRoute route lowered loweredReady
    obtain ⟨final, ⟨finalReady⟩⟩ :=
      moveQueryFrame (lowered.restoreRoute route) restoredReady sameLocals included
    exact ⟨nextPast, final, ⟨finalReady⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
