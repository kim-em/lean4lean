import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeCursor
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalRichRecipeNativeCursor
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeConstantOpening

/-! Operational entry for a nested charged recipe. Focusing retains the
literal input certificate and the complete pending elimination context. The
next bank is derived at that original closed input; an F result is never used
as replacement syntax for recursive cursor descent. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private theorem WorldCodeRecipeProvenance.focusExecutableInput
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {strata : EquationStratification env}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (annotation : WorldCodeRecipeProvenance strata recipe)
    (sources : annotation.Sources P) :
    ∃ input : RichRecipeRootInput env U registry target,
      Nonempty (RichRecipeContext input recipe) ∧
      sizeOf input.certificate < sizeOf recipe ∧ input.strata = strata ∧
      P input.owner.selected.origin.source ∧
      ∃ child : WorldCertProvenance strata input.certificate,
      ∃ controls : OriginalWorldControls strata input.owner.selected.origin.source,
      ∃ provenance : EndpointProvenance (.nil : ContextDerivation input.owner.selected.origin.source U []) input.node,
        List.Subset ((WorldQuerySite.empty (registry := registry) (target := target)
          controls provenance input.realization).worlds ++ child.worlds) annotation.worlds := by
  match annotation with
  | .root source locals σ owner node closed expressionEq realization certificate supplied child controls provenance =>
    refine ⟨⟨_, _, owner, _, _, _, node, closed, expressionEq, source, locals, σ,
      realization, _, _, _, _, certificate, supplied⟩, ⟨.root⟩, ?_, rfl, sources,
      child, controls, provenance, ?_⟩
    · simp_wf
      omega
    · exact List.Subset.refl _
  | .domain child =>
    obtain ⟨input, ⟨pending⟩, smaller, strataEq, sourceReady, cert, controls, provenance, included⟩ := child.focusExecutableInput sources
    refine ⟨input, ⟨.domain pending⟩, Nat.lt_trans smaller ?_, strataEq, sourceReady,
      cert, controls, provenance, included⟩
    simp_wf
    omega
  | .body child selected anchor =>
    obtain ⟨input, ⟨pending⟩, smaller, strataEq, sourceReady, cert, controls, provenance, included⟩ := child.focusExecutableInput sources
    refine ⟨input, ⟨.body pending selected anchor⟩, Nat.lt_trans smaller ?_, strataEq, sourceReady,
      cert, controls, provenance, included⟩
    simp_wf
    omega
  | .fixedBody child selected admitted =>
    obtain ⟨input, ⟨pending⟩, smaller, strataEq, sourceReady, cert, controls, provenance, included⟩ := child.focusExecutableInput sources
    refine ⟨input, ⟨.fixedBody pending selected admitted⟩, Nat.lt_trans smaller ?_, strataEq, sourceReady,
      cert, controls, provenance, included⟩
    simp_wf
    omega
  | .resources child transfer =>
    obtain ⟨input, ⟨pending⟩, smaller, strataEq, sourceReady, cert, controls, provenance, included⟩ := child.focusExecutableInput sources
    refine ⟨input, ⟨.resources pending _⟩, Nat.lt_trans smaller ?_, strataEq, sourceReady,
      cert, controls, provenance, ?_⟩
    · simp_wf
      omega
    · intro world member
      exact List.mem_append_left _ (included member)
  | .action change child =>
    obtain ⟨input, ⟨pending⟩, smaller, strataEq, sourceReady, cert, controls, provenance, included⟩ := child.focusExecutableInput sources
    refine ⟨input, ⟨.action pending change⟩, Nat.lt_trans smaller ?_, strataEq, sourceReady,
      cert, controls, provenance, included⟩
    simp_wf
    omega

termination_by sizeOf annotation
decreasing_by all_goals simp_wf; omega


/-- Every retained recipe root gives a concrete strictly lower original call,
its exact child query controls, and the bank for further original calls there.
All intermediate body/domain/resource/action operations remain in `pending`.
The caller's frame and sponsor frontier are unchanged. -/
theorem WorldCodeRecipeProvenance.openFocusedFromBank
    {strata : EquationStratification env} {P : VEnv → Prop}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (annotation : WorldCodeRecipeProvenance strata recipe)
    (formed : OnCtx target (env.IsType U))
    (caller : EndpointState callerEnv U callerSource callerExpression callerAssigned)
    (controls : OriginalWorldControls strata callerEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (frontier : List (World strata.rules.length))
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (sources : annotation.Sources P)
    (sponsored : Sponsored frontier annotation.worlds)
    (bounded : WithinAbove controls.cutoff controls.fuel
      (fun control => recipe.stratifiedDepth (strata.headOrdinal registry) control))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline])) :
    ∃ input : RichRecipeRootInput env U registry target,
    ∃ pending : RichRecipeContext input recipe,
      sizeOf input.certificate < sizeOf recipe ∧ input.strata = strata ∧
      ∃ child : WorldCertProvenance strata input.certificate,
      ∃ childControls : OriginalWorldControls strata input.owner.selected.origin.source,
      ∃ provenance : EndpointProvenance (.nil : ContextDerivation input.owner.selected.origin.source U []) input.node,
      let frame : OriginalRichFrame input.owner.selected.origin.source env U registry target .nil
        [] input.realization input.realization (fun _ => []) := .nil
      child.worlds ⊆ annotation.worlds ∧
      childControls.cutoff = input.owner.selected.ordinal - 1 ∧
      childControls.fuel = (fun control => input.certificate.stratifiedDepth (strata.headOrdinal registry) control) ∧
      WorldBelow strata.rules.length (originalCallWorld childControls .fundamental input.node .nil)
        (originalCallWorld controls .fundamental caller baseline) ∧
      ∃ data : WorldUnaryFrameData P childControls frontier frame .nil,
      ∃ ready : ControlledStoredQuery childControls frontier (.certificate input.certificate),
      Sponsored frontier [originalCallWorld childControls .fundamental input.node .nil] ∧
      WorldBoundedUnaryCallBank env U registry strata P
        (frontier ++ [originalCallWorld childControls .fundamental input.node .nil]) ∧
      ∃ answer : RichComputationalValue input.owner.selected.origin.source env U registry target input.node
          [] input.realization input.realization (fun _ => []) input.profile,
        Nonempty (ControlledStoredQuery childControls frontier (.certificate answer.certificate)) ∧
        Nonempty (ControlledStoredQuery childControls frontier (.observation answer.rightQuery.observation)) := by
  obtain ⟨input, ⟨pending⟩, smaller, same, sourceReady, child, oldControls, provenance, included⟩ :=
    annotation.focusExecutableInput sources
  cases same
  have children : child.worlds ⊆ annotation.worlds :=
    fun world member => included (List.mem_append_right _ member)
  have rootBound : WithinAbove controls.cutoff controls.fuel
      (headDepth input.owner.selected.ordinal
        (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control)) := by
    intro control active
    have rootDepth := pending.rootDepth (stratifiedHeadPolicy (input.strata.headOrdinal registry) control)
    have bound := Nat.le_trans rootDepth (bounded control active)
    simpa only [RichRecipeRootInput.recipe, RichCodeRecipe.headDepth, stratifiedHeadPolicy,
      input.owner.headOrdinal_eq, RichCert.stratifiedDepth, headDepth] using bound
  let fuel := fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control
  let childControls := canonicalQueryControls input.owner.selected fuel
  obtain ⟨data, childPaid, childBank⟩ := canonicalNilOpeningBank (registry := registry) (target := target)
    input.owner input.node input.realization fuel caller controls baseline frontier callerPaid sourceReady rootBound bank
  have lower : WorldBelow input.strata.rules.length
      (originalCallWorld childControls .fundamental input.node .nil)
      (originalCallWorld controls .fundamental caller baseline) := by
    apply Below.root (pending.openingDecrease controls.cutoffBound bounded
      controls.ordered.constantCount
      (richSchedule .fundamental (Closure.close (caller.dependencyOrigin controls.ordered) environment).cost))
    intro value member
    cases member
  let childReady : ControlledStoredQuery childControls frontier (.certificate input.certificate) := {
    annotation := child
    within := fun _ _ => Nat.le_refl _
    sponsored := fun world member => sponsored world (children member) }
  have funded : CallBelow input.strata.rules.length
      (frontier ++ [originalCallWorld childControls .fundamental input.node .nil])
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]) := by
    have step := split_call (calls := [originalCallWorld childControls .fundamental input.node .nil])
      (fun world member => by cases List.mem_singleton.mp member; exact lower)
    have prefixed : ∀ sponsors : List (World input.strata.rules.length),
        CallBelow input.strata.rules.length
          (sponsors ++ [originalCallWorld childControls .fundamental input.node .nil])
          (sponsors ++ [originalCallWorld controls .fundamental caller baseline]) := by
      intro sponsors
      induction sponsors with
      | nil => exact step
      | cons world rest ih => exact ih.cons world
    exact prefixed frontier
  let queryReady : ControlledStoredQuery childControls frontier (.observation (.code input.certificate)) := {
    annotation := .code child
    within := by
      intro control active
      simpa only [StoredOriginalQuery.headDepth, RichObs.headDepth] using childReady.within control active
    sponsored := fun world member => sponsored world (children member) }
  have closed : Valuation.AtomClosed (fun _ => []) := by
    intro index need member
    cases member
  let childFrame : OriginalRichFrame input.owner.selected.origin.source env U registry target .nil
      [] input.realization input.realization (fun _ => []) := .nil
  let childEnvironment : WorldEnvironmentProvenance input.strata U
      (childFrame.dependencyEnvironment childControls.ordered) := .nil
  obtain ⟨answer, certificateReady, observationReady⟩ := (bank _ funded).computational input.node provenance
    childControls childFrame childEnvironment childEnvironment frontier (Nat.le_refl _) (Covered.refl _) rfl childPaid data closed
    formed .nil (.code input.certificate) input.resources queryReady
  exact ⟨input, pending, smaller, rfl, child, childControls, provenance,
    children, rfl, rfl, lower, data, childReady, childPaid, childBank,
    answer, certificateReady, observationReady⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
