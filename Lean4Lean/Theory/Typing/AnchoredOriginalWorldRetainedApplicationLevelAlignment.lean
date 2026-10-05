import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCanonicalLevelAlignment
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedApplicationExecution

/-! Align both actual operands of a retained application at its preserved
canonical opening. The same lower equality answers construct the right
argument admission; a controlled query alone would not supply that premise. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

theorem RichAppOrigin.alignLevelsWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    (owner : CanonicalCodeOwner env registry strata name)
    (fuel : Nat → Nat)
    {root : EndpointRef owner.selected.origin.source U rootSource rootExpression rootType}
    (origin : RichAppOrigin root env registry target source locals σ f a)
    {node : EndpointState owner.selected.origin.source U source (.app f a) assigned}
    {context : ContextDerivation owner.selected.origin.source U source}
    (route : PrefixRoute owner.selected.origin.source U source (.app f a) node origin.node)
    (provenance : EndpointProvenance context node)
    (functionLevels : EqUpToLevels U f nextFunction)
    (argumentLevels : EqUpToLevels U a nextArgument)
    (frame : OriginalRichFrame owner.selected.origin.source env U registry target
      context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U
      (frame.dependencyEnvironment owner.selected.origin.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P (canonicalQueryControls owner.selected fuel) frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : (origin.functionFootprint ++ origin.argumentFootprint).Available available)
    (functionReady : ControlledStoredQuery (canonicalQueryControls owner.selected fuel)
      frontier (.observation origin.function))
    (argumentReady : ControlledStoredQuery (canonicalQueryControls owner.selected fuel)
      frontier (.observation origin.argument))
    (caller : EndpointState callerEnv U callerSource callerExpression callerAssigned)
    (controls : OriginalWorldControls strata callerEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (nodeBelow : WorldBelow strata.rules.length
      (originalCallWorld (canonicalQueryControls owner.selected fuel) .fundamental node captured)
      (originalCallWorld controls .fundamental caller baseline))
    (masked : WithinAbove controls.cutoff controls.fuel (headDepth owner.selected.ordinal fuel))
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
    (henv : env.Ordered) (hscoped : registry.Scoped) :
    let fnOriginal := EndpointState.levelAlignment owner.selected.origin.ordered context
      origin.functionNode functionLevels
    let argOriginal := EndpointState.levelAlignment owner.selected.origin.ordered context
      origin.argumentNode argumentLevels
    ∃ functionAnswer : OriginalDirectionalEqualityResult fnOriginal true env registry target
        locals σ τ available (Profile.fn origin.key origin.output),
    ∃ argumentAnswer : OriginalDirectionalEqualityResult argOriginal true env registry target
        locals σ τ available origin.rawInput,
      Nonempty (ControlledStoredQuery (canonicalQueryControls owner.selected fuel)
        frontier (.observation functionAnswer.rightQuery.observation)) ∧
      Nonempty (ControlledStoredQuery (canonicalQueryControls owner.selected fuel)
        frontier (.observation argumentAnswer.rightQuery.observation)) ∧
      Admitted env U registry target origin.key (a.subst σ) (nextArgument.subst τ) ∧
      Admitted env U registry target origin.key (nextArgument.subst τ) (nextArgument.subst τ) := by
  dsimp only
  let childControls := canonicalQueryControls owner.selected fuel
  have enlarged := application_cost_le_captured (origin.domain.dependencyOrigin childControls.ordered)
    (origin.codomain.dependencyOrigin childControls.ordered) (origin.functionNode.dependencyOrigin childControls.ordered)
    (origin.argumentNode.dependencyOrigin childControls.ordered) (origin.result.dependencyOrigin childControls.ordered)
    (frame.dependencyEnvironment childControls.ordered)
  have lower {expression assigned} (child : EndpointState owner.selected.origin.source U source expression assigned)
      (member : child.dependencyOrigin childControls.ordered ∈
        [origin.functionNode.dependencyOrigin childControls.ordered,
         origin.argumentNode.dependencyOrigin childControls.ordered, origin.result.dependencyOrigin childControls.ordered]) :
      WorldBelow strata.rules.length (originalCallWorld childControls .fundamental child captured)
        (originalCallWorld controls .fundamental caller baseline) := by
    have cost := Nat.lt_of_lt_of_le (binder_other_cost (domain := origin.domain.dependencyOrigin childControls.ordered)
      (bodies := [origin.codomain.dependencyOrigin childControls.ordered]) member
      (frame.dependencyEnvironment childControls.ordered)) enlarged
    have cost' := Nat.lt_of_lt_of_le cost (route.dependency_cost_le childControls.ordered _)
    have localBelow : WorldBelow strata.rules.length
        (originalCallWorld childControls .fundamental child captured)
        (originalCallWorld childControls .fundamental node captured) :=
      original_child (richSchedule_strict cost' _ _) _ _ _ _ captured.worlds
    exact EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans localBelow nodeBelow
  have contextEq : context = (route.locate provenance.location).contextDerivation provenance.initial := by
    rw [PrefixRoute.locate_contextDerivation]
    exact provenance.context_eq
  let fnProvenance : EndpointProvenance context origin.functionNode := {
    rootSource := provenance.rootSource, rootExpression := provenance.rootExpression, rootType := provenance.rootType
    root := provenance.root, initial := provenance.initial
    location := .appFunction (route.locate provenance.location)
    context_eq := contextEq }
  let argProvenance : EndpointProvenance context origin.argumentNode := {
    rootSource := provenance.rootSource, rootExpression := provenance.rootExpression, rootType := provenance.rootType
    root := provenance.root, initial := provenance.initial
    location := .appArgument (route.locate provenance.location)
    context_eq := contextEq }
  obtain ⟨fnAnswer, fnReady⟩ := alignLevelsAtCanonicalOpening owner fuel origin.functionNode
    fnProvenance functionLevels frame captured frontier data closed substitutions origin.function
    (fun index need member => resources index need (List.mem_append_left _ member)) functionReady
    caller controls baseline paid (lower _ (by simp)) masked bank unary henv hscoped formed
  obtain ⟨argAnswer, argReady⟩ := alignLevelsAtCanonicalOpening owner fuel origin.argumentNode
    argProvenance argumentLevels frame captured frontier data closed substitutions origin.argument
    (fun index need member => resources index need (List.mem_append_right _ member)) argumentReady
    caller controls baseline paid (lower _ (by simp)) masked bank unary henv hscoped formed
  have functionValue : Related env U registry target (f.subst σ) (nextFunction.subst τ)
      (.forallE (origin.A.subst σ) (origin.B.subst σ.lift))
      (Profile.fn origin.key origin.output) fnAnswer.support := by
    simpa only [Bool.not_true, Bool.false_eq_true, reduceIte, subst] using fnAnswer.related
  have argumentValue : Related env U registry target (a.subst σ) (nextArgument.subst τ)
      (origin.A.subst σ) origin.rawInput argAnswer.support := by
    simpa only [Bool.not_true, Bool.false_eq_true, reduceIte] using argAnswer.related
  obtain ⟨support, inputTyped, supportFormed, path, bridge⟩ :=
    functionValue.fn_domain_alignment henv hscoped formed
  have adapted := origin.arguments.termMap henv hscoped formed inputTyped
    (bridge.symm henv inputTyped.wf_type).left_diagonal argumentValue
  have converted := Related.convert henv inputTyped (bridge.symm henv inputTyped.wf_type) adapted
  let argOriginal := EndpointState.levelAlignment owner.selected.origin.ordered context
    origin.argumentNode argumentLevels
  have rawAtDomain := (argOriginal.forget.defeq.mono owner.selected.origin.sourceBelow).substDF
    henv substitutions.wf formed substitutions
  have raw := path.symm.cast rawAtDomain
  obtain ⟨anchorRaw, _, _, _, _, _, oldRelated, _⟩ := origin.admitted
  have old := Related.retag henv inputTyped bridge.left_diagonal oldRelated
  have paired : Admitted env U registry target origin.key (a.subst σ) (nextArgument.subst τ) :=
    ⟨anchorRaw, raw, support, inputTyped, supportFormed, bridge.left_diagonal, old, converted⟩
  have next := Related.trans henv hscoped old converted
  have admitted : Admitted env U registry target origin.key (nextArgument.subst τ) (nextArgument.subst τ) :=
    ⟨anchorRaw.trans raw, raw.hasType.2, support, inputTyped, supportFormed,
      bridge.left_diagonal, next, (next.symm henv).left_diagonal⟩
  exact ⟨fnAnswer, argAnswer, fnReady, argReady, paired, admitted⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
