import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyValueSpine
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedUnaryCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalQueryCompatibility
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPrefixMeasure
import Lean4Lean.Theory.Typing.AnchoredOriginalPiPrefix

/-! Every parsed family-prefix argument is interpreted at its actual proper
original descendant, using the same frame, ancestry, and inherited sponsors. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

private theorem suffix_length
    {initial : ContextDerivation env U source} {next : ContextDerivation env U target}
    (suffix : ContextDerivation.Suffix initial next) : source.length ≤ target.length := by
  induction suffix with
  | refl => exact Nat.le_refl _
  | cons previous ih => exact Nat.le_trans ih (Nat.le_succ _)

private theorem suffix_same
    {initial next : ContextDerivation env U source}
    (suffix : ContextDerivation.Suffix initial next) : next = initial := by
  cases suffix with
  | refl => rfl
  | cons previous =>
    have impossible := suffix_length previous
    simp only [List.length_cons] at impossible
    omega

private theorem location_same_context
    {root : EndpointRef env U source expression assigned}
    {node : EndpointState env U source nextExpression nextAssigned}
    (location : Located root node) (initial : ContextDerivation env U source) :
    location.contextDerivation initial = initial :=
  suffix_same (Classical.choice (location.contextDerivation_suffix initial))

private theorem location_same_environment
    {root : EndpointRef env U source expression assigned}
    {node : EndpointState env U source nextExpression nextAssigned}
    (location : Located root node) (ordered : env.Ordered) (initial : List Closure) :
    location.dependencyEnvironment ordered initial = initial := by
  have lengths := congrArg List.length location.context_eq
  simp only [List.length_append] at lengths
  have empty : location.binderPrefix = [] := by
    cases h : location.binderPrefix with
    | nil => rfl
    | cons a rest => simp only [h, List.length_cons] at lengths; omega
  have unchanged {context : List VExpr} {e t : VExpr} {next : EndpointState env U context e t}
      (path : Located root next) (none : path.binderPrefix = []) :
      path.dependencyEnvironment ordered initial = initial := by
    induction path <;> simp_all only [Located.binderPrefix, Located.dependencyEnvironment, List.cons_ne_nil]
  exact unchanged location empty

theorem RichAppOrigin.interpretArgumentWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (origin : RichAppOrigin root env registry target source locals σ f a)
    (context : ContextDerivation sourceEnv U source)
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental (.ref root) captured])
    (resources : origin.argumentFootprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.observation origin.argument))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref root) captured])) :
    ∃ answer : RichComputationalValue sourceEnv env U registry target origin.argumentNode
        locals σ σ available origin.rawInput,
      Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)) ∧
      Nonempty (ControlledStoredQuery controls frontier (.observation answer.rightQuery.observation)) := by
  have child : (Closure.close (origin.argumentNode.dependencyOrigin controls.ordered)
      (frame.dependencyEnvironment controls.ordered)).cost <
      (Closure.close ((EndpointState.app origin.hu origin.hv origin.domain origin.codomain
        origin.functionNode origin.argumentNode origin.result).dependencyOrigin controls.ordered)
        (frame.dependencyEnvironment controls.ordered)).cost := by
    apply Nat.lt_of_lt_of_le _ (application_cost_le_captured _ _ _ _ _ _)
    exact binder_other_cost (by simp) _
  have parent := origin.location.dependency_cost_le controls.ordered (frame.dependencyEnvironment controls.ordered)
  rw [location_same_environment origin.location] at parent
  have lower : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental origin.argumentNode captured)
      (originalCallWorld controls .fundamental (.ref root) captured) :=
    original_child (richSchedule_strict (Nat.lt_of_lt_of_le child parent) _ _) _ _ _ _ _
  have funded : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental origin.argumentNode captured])
      (frontier ++ [originalCallWorld controls .fundamental (.ref root) captured]) := by
    have step := split_call (calls := [originalCallWorld controls .fundamental origin.argumentNode captured])
      (fun world member => by cases List.mem_singleton.mp member; exact lower)
    have prefixed : ∀ sponsors : List (World strata.rules.length),
        CallBelow strata.rules.length
          (sponsors ++ [originalCallWorld controls .fundamental origin.argumentNode captured])
          (sponsors ++ [originalCallWorld controls .fundamental (.ref root) captured]) := by
      intro sponsors
      induction sponsors with
      | nil => exact step
      | cons world rest ih => exact ih.cons world
    exact prefixed frontier
  have paid : Sponsored frontier [originalCallWorld controls .fundamental origin.argumentNode captured] := by
    intro world member
    cases List.mem_singleton.mp member
    obtain ⟨sponsor, present, below⟩ := callerPaid _ (List.mem_singleton_self _)
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans lower below⟩
  have provenance : EndpointProvenance context origin.argumentNode := {
    rootSource := source, rootExpression := rootExpression, rootType := rootType
    root := root, initial := context, location := .appArgument origin.location
    context_eq := (location_same_context (.appArgument origin.location) context).symm }
  exact (bank _ funded).computational origin.argumentNode provenance controls frame captured captured frontier
    (Nat.le_refl _) (Covered.refl _) rfl paid data closed formed substitutions origin.argument resources ready

/-- The actual caller function is a proper original child too. Its F answer
contains the assigned Pi certificate at that caller, even when the function
query retains independent canonical sources. This is the entry to caller Pi
row extraction; it does not move a foreign frame to the caller. -/
theorem RichAppOrigin.interpretFunctionWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (origin : RichAppOrigin root env registry target source locals σ f a)
    (context : ContextDerivation sourceEnv U source)
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental (.ref root) captured])
    (resources : origin.functionFootprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.observation origin.function))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref root) captured])) :
    ∃ answer : RichComputationalValue sourceEnv env U registry target origin.functionNode
        locals σ σ available (Profile.fn origin.key origin.output),
      Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)) ∧
      Nonempty (ControlledStoredQuery controls frontier (.observation answer.rightQuery.observation)) := by
  have child : (Closure.close (origin.functionNode.dependencyOrigin controls.ordered)
      (frame.dependencyEnvironment controls.ordered)).cost <
      (Closure.close ((EndpointState.app origin.hu origin.hv origin.domain origin.codomain
        origin.functionNode origin.argumentNode origin.result).dependencyOrigin controls.ordered)
        (frame.dependencyEnvironment controls.ordered)).cost := by
    apply Nat.lt_of_lt_of_le _ (application_cost_le_captured _ _ _ _ _ _)
    exact binder_other_cost (by simp) _
  have parent := origin.location.dependency_cost_le controls.ordered (frame.dependencyEnvironment controls.ordered)
  rw [location_same_environment origin.location] at parent
  have lower : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental origin.functionNode captured)
      (originalCallWorld controls .fundamental (.ref root) captured) :=
    original_child (richSchedule_strict (Nat.lt_of_lt_of_le child parent) _ _) _ _ _ _ _
  have funded : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental origin.functionNode captured])
      (frontier ++ [originalCallWorld controls .fundamental (.ref root) captured]) := by
    have step := split_call (calls := [originalCallWorld controls .fundamental origin.functionNode captured])
      (fun world member => by cases List.mem_singleton.mp member; exact lower)
    have prefixed : ∀ sponsors : List (World strata.rules.length),
        CallBelow strata.rules.length
          (sponsors ++ [originalCallWorld controls .fundamental origin.functionNode captured])
          (sponsors ++ [originalCallWorld controls .fundamental (.ref root) captured]) := by
      intro sponsors
      induction sponsors with
      | nil => exact step
      | cons world rest ih => exact ih.cons world
    exact prefixed frontier
  have paid : Sponsored frontier [originalCallWorld controls .fundamental origin.functionNode captured] := by
    intro world member
    cases List.mem_singleton.mp member
    obtain ⟨sponsor, present, below⟩ := callerPaid _ (List.mem_singleton_self _)
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans lower below⟩
  have provenance : EndpointProvenance context origin.functionNode := {
    rootSource := source, rootExpression := rootExpression, rootType := rootType
    root := root, initial := context, location := .appFunction origin.location
    context_eq := (location_same_context (.appFunction origin.location) context).symm }
  exact (bank _ funded).computational origin.functionNode provenance controls frame captured captured frontier
    (Nat.le_refl _) (Covered.refl _) rfl paid data closed formed substitutions origin.function resources ready

/-- The selected Pi in the actual caller function's assigned formation remains
strictly below the caller application. Its bank and sponsorship are derived
from the enclosing caller; neither is an extra premise of row execution. -/
theorem RichAppOrigin.functionPiBank
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (origin : RichAppOrigin root env registry target source locals σ f a)
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U environment)
    (frontier : List (World strata.rules.length))
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental (.ref root) captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref root) captured])) :
    let selected := piPrefix (.assignedFormation (.appFunction origin.location))
    let node := EndpointState.pi selected.view.domainWF selected.view.bodyWF
      selected.view.domain selected.view.body
    WorldBelow strata.rules.length (originalCallWorld controls .fundamental node captured)
      (originalCallWorld controls .fundamental (.ref root) captured) ∧
    Sponsored frontier [originalCallWorld controls .fundamental node captured] ∧
    WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]) := by
  dsimp only
  let selected := piPrefix (.assignedFormation (.appFunction origin.location))
  let node := EndpointState.pi selected.view.domainWF selected.view.bodyWF
    selected.view.domain selected.view.body
  have child : (Closure.close (origin.functionNode.dependencyOrigin controls.ordered) environment).cost <
      (Closure.close ((EndpointState.app origin.hu origin.hv origin.domain origin.codomain
        origin.functionNode origin.argumentNode origin.result).dependencyOrigin controls.ordered)
        environment).cost := by
    apply Nat.lt_of_lt_of_le _ (application_cost_le_captured _ _ _ _ _ _)
    exact binder_other_cost (by simp) _
  have parent := origin.location.dependency_cost_le controls.ordered environment
  rw [location_same_environment origin.location] at parent
  have formation := origin.functionNode.typeFormation_dependency_cost_le controls.ordered environment
  have head := selected.route.dependency_cost_le controls.ordered environment
  have lower : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental node captured)
      (originalCallWorld controls .fundamental (.ref root) captured) :=
    original_child (richSchedule_strict
      (Nat.lt_of_le_of_lt (Nat.le_trans head formation) (Nat.lt_of_lt_of_le child parent)) _ _) _ _ _ _ _
  have funded : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental node captured])
      (frontier ++ [originalCallWorld controls .fundamental (.ref root) captured]) := by
    have step := split_call (calls := [originalCallWorld controls .fundamental node captured])
      (fun world member => by cases List.mem_singleton.mp member; exact lower)
    have prefixed : ∀ sponsors : List (World strata.rules.length),
        CallBelow strata.rules.length
          (sponsors ++ [originalCallWorld controls .fundamental node captured])
          (sponsors ++ [originalCallWorld controls .fundamental (.ref root) captured]) := by
      intro sponsors
      induction sponsors with
      | nil => exact step
      | cons world rest ih => exact ih.cons world
    exact prefixed frontier
  refine ⟨lower, ?_, ?_⟩
  · intro world member
    cases List.mem_singleton.mp member
    obtain ⟨sponsor, present, below⟩ := callerPaid _ (List.mem_singleton_self _)
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans lower below⟩
  · intro retained below
    exact bank retained (Relation.TransGen.trans below funded)

def WorldFamilyValueSpine.ArgumentsLive
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (spine : WorldFamilyValueSpine root env registry target locals σ controls frontier
      name levels expression atom footprint) : Prop :=
  match spine with
  | .constant .. => True
  | .app origin function _ _ _ => function.ArgumentsLive ∧ Profile.Live env U registry target origin.rawInput

theorem WorldFamilyValueSpine.argumentsLiveOfBank
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental (.ref root) captured])
    (spine : WorldFamilyValueSpine root env registry target locals σ controls frontier
      name levels expression atom footprint)
    (resources : footprint.Available available)
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref root) captured])) :
    spine.ArgumentsLive := by
  induction spine with
  | constant => trivial
  | app origin function path included ready ih =>
    have all : (origin.functionFootprint ++ origin.argumentFootprint).Available available :=
      fun index need present => resources index need (included present)
    obtain ⟨answer, _, _⟩ := origin.interpretArgumentWorld context controls frame captured frontier data
      closed formed substitutions callerPaid (fun i need member => all i need (List.mem_append_right _ member))
      ready bank
    exact ⟨ih (fun i need member => all i need (List.mem_append_left _ member)),
      answer.related.live henv hscoped formed⟩

/-- The caller supplies its actual function query and original induction
bank. Parsing and all finite argument calls are performed internally. -/
theorem RichObs.familyFunctionSpineOfBank
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    {n : Nat} {key : Key n} {output : Atom n}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental (.ref root) captured])
    (query : RichObs sourceEnv env U registry target node locals σ (Profile.fn key output) footprint)
    (location : Located root node)
    (head : expression.getAppFnArgs.1 = .const name levels)
    (ends : FamilyEndDemand output)
    (resources : footprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.observation query))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref root) captured])) :
    ∃ spine : WorldFamilyValueSpine root env registry target locals σ controls frontier
        name levels expression (n := n+1) (.fn key output) footprint,
      spine.ArgumentsLive := by
  have nonsortable : ∀ flag, ¬ (Profile.fn key output).HasType (.sort flag) := by
    intro flag sorted
    obtain ⟨cover, member, impossible⟩ := sorted.2.2 _ (List.mem_singleton_self _)
    cases List.mem_singleton.mp member
    contradiction
  obtain ⟨spine⟩ := query.familyValueSpineControlled henv hscoped formed location head
    (List.mem_singleton_self _) ends nonsortable ready
  exact ⟨spine, spine.argumentsLiveOfBank henv hscoped context controls frame captured frontier data
    closed formed substitutions callerPaid resources bank⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
