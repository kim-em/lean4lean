import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeBodyExecution
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeApplicationAdmission
import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationSeeding
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldGradedApplication

/-! Execute retained application operands in the actual paired source frame.
The original queries remain the inputs of two proper-child calls. Neither a
body F answer nor a destination field comparison is an input. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

structure RetainedApplicationAnswers
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (origin : RichAppOrigin root env registry target source locals σ f a)
    (controls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length)) (τ : Subst) (available : Valuation) where
  functionValue : RichComputationalValue sourceEnv env U registry target origin.functionNode
    locals σ τ available (Profile.fn origin.key origin.output)
  argumentValue : RichComputationalValue sourceEnv env U registry target origin.argumentNode
    locals σ τ available origin.rawInput
  functionCertificate : ControlledStoredQuery controls frontier (.certificate functionValue.certificate)
  functionQuery : ControlledStoredQuery controls frontier (.observation functionValue.rightQuery.observation)
  argumentCertificate : ControlledStoredQuery controls frontier (.certificate argumentValue.certificate)
  argumentQuery : ControlledStoredQuery controls frontier (.observation argumentValue.rightQuery.observation)
  paired : Admitted env U registry target origin.key (a.subst σ) (a.subst τ)
  admitted : Admitted env U registry target origin.key (a.subst τ) (a.subst τ)

theorem RichAppOrigin.executeWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (origin : RichAppOrigin root env registry target source locals σ f a)
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    {context : ContextDerivation sourceEnv U source}
    (route : PrefixRoute sourceEnv U source (.app f a) node origin.node)
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
    (argumentReady : ControlledStoredQuery controls frontier (.observation origin.argument))
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured])) :
    Nonempty (RetainedApplicationAnswers origin controls frontier τ available) := by
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
  have argBelow := lower origin.argumentNode (by simp)
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
  let argProvenance : EndpointProvenance context origin.argumentNode := {
    rootSource := provenance.rootSource, rootExpression := provenance.rootExpression, rootType := provenance.rootType
    root := provenance.root, initial := provenance.initial
    location := .appArgument (route.locate provenance.location)
    context_eq := contextEq }
  obtain ⟨fnAnswer, ⟨fnCodeReady⟩, ⟨fnQueryReady⟩⟩ :=
    (bank _ (fund fnBelow)).computational origin.functionNode fnProvenance controls frame captured captured
      frontier (Nat.le_refl _) (Covered.refl _) rfl (singletonSponsoredBelow paid fnBelow)
      data closed formed substitutions origin.function
      (fun index need member => resources index need (List.mem_append_left _ member)) functionReady
  obtain ⟨argAnswer, ⟨argCodeReady⟩, ⟨argQueryReady⟩⟩ :=
    (bank _ (fund argBelow)).computational origin.argumentNode argProvenance controls frame captured captured
      frontier (Nat.le_refl _) (Covered.refl _) rfl (singletonSponsoredBelow paid argBelow)
      data closed formed substitutions origin.argument
      (fun index need member => resources index need (List.mem_append_right _ member)) argumentReady
  have functionValue : Related env U registry target (f.subst σ) (f.subst τ)
      (.forallE (origin.A.subst σ) (origin.B.subst σ.lift))
      (Profile.fn origin.key origin.output) fnAnswer.support := by
    simpa only [subst] using fnAnswer.related
  obtain ⟨support, inputTyped, supportFormed, path, bridge⟩ :=
    functionValue.fn_domain_alignment henv hscoped formed
  have adapted := origin.arguments.termMap henv hscoped formed inputTyped
    (bridge.symm henv inputTyped.wf_type).left_diagonal argAnswer.related
  have converted := Related.convert henv inputTyped (bridge.symm henv inputTyped.wf_type) adapted
  have raw := path.symm.cast
    ((origin.argumentNode.sound.defeq.mono sourceBelow).substDF henv substitutions.wf formed substitutions)
  obtain ⟨anchorRaw, _, _, _, _, _, oldRelated, _⟩ := origin.admitted
  have old := Related.retag henv inputTyped bridge.left_diagonal oldRelated
  have paired : Admitted env U registry target origin.key (a.subst σ) (a.subst τ) :=
    ⟨anchorRaw, raw, support, inputTyped, supportFormed, bridge.left_diagonal, old, converted⟩
  have next := Related.trans henv hscoped old converted
  have admitted : Admitted env U registry target origin.key (a.subst τ) (a.subst τ) :=
    ⟨anchorRaw.trans raw, raw.hasType.2, support, inputTyped, supportFormed,
      bridge.left_diagonal, next, (next.symm henv).left_diagonal⟩
  exact ⟨⟨fnAnswer, argAnswer, fnCodeReady, fnQueryReady, argCodeReady, argQueryReady, paired, admitted⟩⟩

/-- The actual child replies reconstruct an ordinary application code query
at the paired right substitution. No charged application answer is assumed. -/
theorem RetainedApplicationAnswers.codeWorld
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {origin : RichAppOrigin root env registry target source locals σ f a}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    (answer : RetainedApplicationAnswers origin controls frontier τ available)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (sorted : (Profile.singleton origin.output).HasType (.sort relevant)) :
    ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target origin.node
        locals τ relevant (.singleton origin.output) footprint,
    ∃ ready : ControlledStoredQuery controls frontier (.certificate certificate),
      footprint.Available available ∧
      ready.annotation.worlds ⊆ answer.functionQuery.annotation.worlds ++ answer.argumentQuery.annotation.worlds ∧
      TypeRelated env U registry target ((.app f a : VExpr).subst σ)
        ((.app f a : VExpr).subst τ) (.singleton origin.output) := by
  obtain ⟨footprint, certificate, ready, resources, worlds⟩ :=
    RichGradedResult.appCodeControlled henv hscoped formed closed origin.domain origin.codomain
      origin.result origin.hu origin.hv answer.functionValue.rightQuery answer.argumentValue.rightQuery
      origin.arguments answer.admitted sorted controls answer.functionQuery answer.argumentQuery
  have functionValue : Related env U registry target (f.subst σ) (f.subst τ)
      (.forallE (origin.A.subst σ) (origin.B.subst σ.lift))
      (Profile.fn origin.key origin.output) answer.functionValue.support := by
    simpa only [subst] using answer.functionValue.related
  refine ⟨footprint, certificate, ready, resources, worlds, ?_⟩
  simpa only [subst] using Related.applicationCode henv hscoped formed sorted functionValue answer.paired

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
