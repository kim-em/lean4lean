import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedApplicationWitness

/-! Execute the original function observation of a retained application.
This selects and executes an inner application from its actual original query;
an outer F answer does not replace that input. Charged residuals stay explicit. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem ControlledStoredQuery.executeRetainedObservationApplicationSized
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {query : RichObs sourceEnv env U registry target node locals σ profile footprint}
    (ready : ControlledStoredQuery controls frontier (.observation query))
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
    (selected : atom ∈ profile.atoms) :
    ∃ origin : RetainedApplicationOrigin provenance.root env registry target source locals σ f a,
    ∃ children : RetainedApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      origin.footprint.Available available ∧ children.worlds ⊆ ready.annotation.worlds ∧
      origin.RootedAt node ∧ children.retainedSize < sizeOf (show WorldObsProvenance strata query from ready.annotation) ∧ (∀ policy, origin.headDepth policy ≤ query.headDepth policy) ∧
      Nonempty (RetainedApplicationStep controls frontier τ available origin) := by
  obtain ⟨origin, children, path, included, worlds, rooted, smaller, depth⟩ :=
    ready.annotation.retainedApplicationOriginSized provenance.location selected (budget := sizeOf (show WorldObsProvenance strata query from ready.annotation)) (Nat.le_refl _)
  have supplied : origin.footprint.Available
      available :=
    fun index need member => resources index need (included member)
  refine ⟨origin, children, path, supplied, worlds, rooted, smaller, depth, ?_⟩
  cases origin with
  | charged actual => exact ⟨.pending actual⟩
  | original actual =>
    cases children with
    | original annotation =>
      obtain ⟨route⟩ := rooted
      have functionReady : ControlledStoredQuery controls frontier (.observation actual.function) := {
        annotation := annotation.function
        within := fun control active => Nat.le_trans (Nat.le_max_left _ _)
          (Nat.le_trans (depth _) (ready.within control active))
        sponsored := fun world member => ready.sponsored world
          (worlds (List.mem_append_left _ member)) }
      have argumentReady : ControlledStoredQuery controls frontier (.observation actual.argument) := {
        annotation := annotation.argument
        within := fun control active => Nat.le_trans (Nat.le_max_right _ _)
          (Nat.le_trans (depth _) (ready.within control active))
        sponsored := fun world member => ready.sponsored world
          (worlds (List.mem_append_right _ member)) }
      obtain ⟨answer⟩ := actual.executeWorld route provenance controls frame captured
        frontier data closed formed substitutions supplied
        functionReady argumentReady henv hscoped sourceBelow paid bank
      exact ⟨.executed answer⟩


theorem RichAppOrigin.executeFunctionApplicationWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (origin : RichAppOrigin root env registry target source locals σ (.app f a) b)
    {node : EndpointState sourceEnv U source (.app (.app f a) b) assigned}
    {context : ContextDerivation sourceEnv U source}
    (route : PrefixRoute sourceEnv U source (.app (.app f a) b) node origin.node)
    (provenance : EndpointProvenance context node)
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : (origin.functionFootprint ++ origin.argumentFootprint).Available available)
    (functionReady : ControlledStoredQuery controls frontier (.observation origin.function))
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured])) :
    ∃ inner : RetainedApplicationOrigin provenance.root env registry target source locals σ f a,
    ∃ children : RetainedApplicationWorlds strata inner,
      Nonempty (GeneralOutputPath env U registry target inner.output
        (show Atom (origin.rank + 1) from .fn origin.key origin.output)) ∧
      inner.footprint.Available available ∧ children.worlds ⊆ functionReady.annotation.worlds ∧
      inner.RootedAt origin.functionNode ∧
      children.retainedSize < sizeOf (show WorldObsProvenance strata origin.function from functionReady.annotation) ∧
      (∀ policy, inner.headDepth policy ≤ origin.function.headDepth policy) ∧
      Nonempty (RetainedApplicationStep controls frontier τ available inner) := by
  have enlarged := application_cost_le_captured (origin.domain.dependencyOrigin controls.ordered)
    (origin.codomain.dependencyOrigin controls.ordered) (origin.functionNode.dependencyOrigin controls.ordered)
    (origin.argumentNode.dependencyOrigin controls.ordered) (origin.result.dependencyOrigin controls.ordered)
    (frame.dependencyEnvironment controls.ordered)
  have lower {expression assigned} (child : EndpointState sourceEnv U source expression assigned)
      (member : child.dependencyOrigin controls.ordered ∈
        [origin.functionNode.dependencyOrigin controls.ordered,
         origin.argumentNode.dependencyOrigin controls.ordered, origin.result.dependencyOrigin controls.ordered]) :
      WorldBelow strata.rules.length (originalCallWorld controls .fundamental child captured)
        (originalCallWorld controls .fundamental node captured) := by
    have cost := Nat.lt_of_lt_of_le (binder_other_cost (domain := origin.domain.dependencyOrigin controls.ordered)
      (bodies := [origin.codomain.dependencyOrigin controls.ordered]) member
      (frame.dependencyEnvironment controls.ordered)) enlarged
    have cost' := Nat.lt_of_lt_of_le cost (route.dependency_cost_le controls.ordered _)
    exact original_child (richSchedule_strict cost' _ _) _ _ _ _ captured.worlds
  have fnBelow := lower origin.functionNode (by simp)
  have fund {child : World strata.rules.length}
      (smaller : WorldBelow strata.rules.length child (originalCallWorld controls .fundamental node captured)) :
      CallBelow strata.rules.length (frontier ++ [child])
        (frontier ++ [originalCallWorld controls .fundamental node captured]) := by
    have first := split_call (calls := [child]) (fun value member => by
      cases List.mem_singleton.mp member
      exact smaller)
    have appendFirst : ∀ inherited : List (World strata.rules.length),
        CallBelow strata.rules.length (inherited ++ [child])
          (inherited ++ [originalCallWorld controls .fundamental node captured]) := by
      intro inherited
      induction inherited with
      | nil => exact first
      | cons world tail ih => exact ih.cons world
    exact appendFirst frontier
  have contextEq : context = (route.locate provenance.location).contextDerivation provenance.initial := by
    rw [PrefixRoute.locate_contextDerivation]
    exact provenance.context_eq
  let fnProvenance : EndpointProvenance context origin.functionNode := {
    rootSource := provenance.rootSource, rootExpression := provenance.rootExpression, rootType := provenance.rootType
    root := provenance.root, initial := provenance.initial
    location := .appFunction (route.locate provenance.location)
    context_eq := contextEq }
  have functionBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental origin.functionNode captured]) :=
    fun calls smaller => bank calls (smaller.trans (fund fnBelow))
  exact functionReady.executeRetainedObservationApplicationSized fnProvenance frame captured data closed
    formed substitutions (fun index need member => resources index need (List.mem_append_left _ member))
    henv hscoped sourceBelow (singletonSponsoredBelow paid fnBelow) functionBank (List.mem_singleton_self _)

/-- Readiness of the original function input comes from the literal selected
children. The function F answer is not involved. -/
noncomputable def RetainedApplicationOpening.functionReady
    {before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (opening : RetainedApplicationOpening before) :
    ControlledStoredQuery before.controls frontier (.observation opening.origin.function) := {
  annotation := opening.children.function
  within := fun control active => Nat.le_trans (Nat.le_max_left _ _)
    (Nat.le_trans (opening.depth _) (before.within control active))
  sponsored := fun world member => before.sponsored world
    (opening.worlds (List.mem_append_left _ member)) }

/-- Execute the inner application from the exact outer terminal packet.
All child funding, input readiness and resource inclusion are derived here.
An inner charged program remains an explicit executable residual. -/
theorem RetainedApplicationOpening.executeFunctionApplicationWorld
    {before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (opening : RetainedApplicationOpening before)
    (functionEq : opening.function = .app f a)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    ∃ inner : RetainedApplicationOrigin before.provenance.root env registry target
        before.source before.locals before.left f a,
    ∃ children : RetainedApplicationWorlds strata inner,
      Nonempty (GeneralOutputPath env U registry target inner.output
        (show Atom (opening.origin.rank + 1) from .fn opening.origin.key opening.origin.output)) ∧
      inner.footprint.Available before.available ∧ children.worlds ⊆ opening.children.function.worlds ∧
      inner.RootedAt (opening.origin.functionNode.cast functionEq rfl) ∧
      children.retainedSize < sizeOf (show WorldObsProvenance strata opening.origin.function from opening.children.function) ∧
      (∀ policy, inner.headDepth policy ≤ opening.origin.function.headDepth policy) ∧
      Nonempty (RetainedApplicationStep before.controls frontier before.right before.available inner) := by
  let ready := opening.functionReady
  rcases before with ⟨sourceEnv, source, context, expression, assigned, node, provenance, controls,
    locals, left, right, available, frame, captured, data, closed, substitutions, sourceBelow,
    relevant, rank, profile, footprint, program, annotation, within, sponsored, resources,
    selected, member, demand, paid, bank⟩
  rcases opening with ⟨function, argument, expressionEq, origin, rooted, children, worlds, depth,
    supplied, answer, ρ, functionLevels, argumentLevels, selectedPath, finalPath, normalized, readback⟩
  cases expressionEq
  cases functionEq
  exact origin.executeFunctionApplicationWorld rooted provenance controls frame captured frontier data
    closed formed substitutions supplied ready henv hscoped sourceBelow paid bank

/-- A function request cannot select a charged code leaf: code paths retain
sortability, whereas a function atom is not sortable. Consequently the
original outer function query always supplies real inner operand answers. -/
theorem RetainedApplicationOpening.physicalFunctionApplicationWorld
    {before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (opening : RetainedApplicationOpening before)
    (functionEq : opening.function = .app f a)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    ∃ inner : RichAppOrigin before.provenance.root env registry target
        before.source before.locals before.left f a,
    ∃ children : RichAppWorlds strata inner,
    ∃ answer : RetainedApplicationAnswers inner before.controls frontier before.right before.available,
      Nonempty (GeneralOutputPath env U registry target inner.output
        (show Atom (opening.origin.rank + 1) from .fn opening.origin.key opening.origin.output)) ∧
      (inner.functionFootprint ++ inner.argumentFootprint).Available before.available ∧
      children.worlds ⊆ opening.children.function.worlds ∧
      inner.RootedAt (opening.origin.functionNode.cast functionEq rfl) ∧
      (∀ policy, max (inner.function.headDepth policy) (inner.argument.headDepth policy) ≤
        opening.origin.function.headDepth policy) ∧
      Nonempty (ControlledStoredQuery before.controls frontier (.observation inner.function)) ∧
      Nonempty (ControlledStoredQuery before.controls frontier (.observation inner.argument)) := by
  obtain ⟨inner, children, ⟨path⟩, resources, worlds, rooted, smaller, depth, ⟨step⟩⟩ :=
    opening.executeFunctionApplicationWorld functionEq henv hscoped formed
  cases step with
  | @executed actual answer =>
    cases children with
    | original annotations =>
      let functionReady : ControlledStoredQuery before.controls frontier (.observation actual.function) := {
        annotation := annotations.function
        within := fun control active => Nat.le_trans (Nat.le_max_left _ _)
          (Nat.le_trans (depth _) (opening.functionReady.within control active))
        sponsored := fun world member => opening.functionReady.sponsored world
          (worlds (List.mem_append_left _ member)) }
      let argumentReady : ControlledStoredQuery before.controls frontier (.observation actual.argument) := {
        annotation := annotations.argument
        within := fun control active => Nat.le_trans (Nat.le_max_right _ _)
          (Nat.le_trans (depth _) (opening.functionReady.within control active))
        sponsored := fun world member => opening.functionReady.sponsored world
          (worlds (List.mem_append_right _ member)) }
      exact ⟨actual, annotations, answer, ⟨path⟩, resources, worlds, rooted, depth,
        ⟨functionReady⟩, ⟨argumentReady⟩⟩
  | pending actual =>
    have sorted := actual.recipe.formed.singleton_of_mem actual.selected
    have impossible := (GeneralOutputPath.codeAtInput path sorted).preservesSort sorted
    obtain ⟨cover, member, impossible⟩ := impossible.2.2 _ (List.mem_singleton_self _)
    cases List.mem_singleton.mp member
    contradiction

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
