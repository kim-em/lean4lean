import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeInterpretation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedUnaryCallBank

/-! The shared recipe interpreter obtains each canonical opening from the
actual world induction bank. Its operational controls use the supplied exact
child-depth budget; arbitrary retained annotation controls are not coerced.
The caller's inherited frontier stays unchanged. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

def WorldCodeRecipeProvenance.Sources
    (annotation : WorldCodeRecipeProvenance strata recipe) (P : VEnv → Prop) : Prop :=
  match annotation with
  | .root _ _ _ owner _ _ _ _ _ _ _ _ _ => P owner.selected.origin.source
  | .domain child | .body child _ _ | .fixedBody child _ _ |
    .resources child _ | .action _ child => child.Sources P

theorem WorldCodeRecipeProvenance.sourcesBelow
    {strata : EquationStratification env}
    (annotation : WorldCodeRecipeProvenance strata recipe)
    (sourceClosed : ∀ source, source ≤ env → P source) : annotation.Sources P := by
  match annotation with
  | .root _ _ _ owner _ _ _ _ _ _ _ _ _ => exact sourceClosed _ owner.selected.origin.sourceBelow
  | .domain child | .body child _ _ | .fixedBody child _ _ |
    .resources child _ | .action _ child => exact child.sourcesBelow sourceClosed
termination_by sizeOf annotation

/-- Only the root performs a recursive call. Its source, original formation,
query, empty frame, strict key and inherited sponsors are all concrete. -/
theorem WorldCodeRecipeProvenance.callsOfBank
    {strata : EquationStratification env}
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
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline])) :
    annotation.Calls (EquationControlMeasure.key strata.rules.length controls.cutoff controls.fuel
      controls.ordered.constantCount
      (richSchedule .fundamental (Closure.close (caller.dependencyOrigin controls.ordered) environment).cost)) := by
  match annotation with
  | .root source locals σ owner node closed expressionEq realization certificate available child oldControls provenance =>
    intro childFuel within sourceCutoff smaller
    let childControls : OriginalWorldControls strata owner.selected.origin.source := {
      ordered := owner.selected.origin.ordered
      cutoff := owner.selected.ordinal - 1
      cutoffBound := Nat.le_trans (Nat.sub_le _ _) owner.selected.ordinal_le
      sourceCutoff := sourceCutoff
      fuel := childFuel }
    let childFrame : OriginalRichFrame owner.selected.origin.source env U registry target .nil
        [] realization realization (fun _ => []) := .nil
    let childEnvironment : WorldEnvironmentProvenance strata U
        (childFrame.dependencyEnvironment childControls.ordered) := .nil
    let childWorld := originalCallWorld childControls .fundamental node childEnvironment
    have lower : WorldBelow strata.rules.length childWorld
        (originalCallWorld controls .fundamental caller baseline) := by
      apply Below.root smaller
      intro value member
      cases member
    have childPaid : Sponsored frontier [childWorld] := by
      intro value member
      cases List.mem_singleton.mp member
      obtain ⟨sponsor, member, paid⟩ := callerPaid _ (List.mem_singleton_self _)
      exact ⟨sponsor, member,
        EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
          EquationControlMeasure.less_trans lower paid⟩
    have funded : CallBelow strata.rules.length (frontier ++ [childWorld])
        (frontier ++ [originalCallWorld controls .fundamental caller baseline]) := by
      have step : CallBelow strata.rules.length [childWorld]
          [originalCallWorld controls .fundamental caller baseline] :=
        split_call (by intro value member; cases List.mem_singleton.mp member; exact lower)
      have appendLower : ∀ sponsors : List (World strata.rules.length),
          CallBelow strata.rules.length (sponsors ++ [childWorld])
            (sponsors ++ [originalCallWorld controls .fundamental caller baseline]) := by
        intro sponsors
        induction sponsors with
        | nil => exact step
        | cons world rest ih => exact ih.cons world
      exact appendLower frontier
    have frameData : WorldUnaryFrameData P childControls frontier childFrame childEnvironment := by
      refine ⟨?_, ?_, ?_, .nil childControls, ?_⟩
      · simpa only [childFrame, OriginalRichFrame.Ambient, OriginalRichFrame.nil,
          RawOriginalRichFrame.Ambient, and_true] using owner.selected.origin.sourceBelow
      · simpa only [childFrame, OriginalRichFrame.nil,
          RawOriginalRichFrame.AllSources, and_true, WorldCodeRecipeProvenance.Sources] using sources
      · intro query member
        simp only [childFrame, OriginalRichFrame.nil, RawOriginalRichFrame.storedQueries,
          List.not_mem_nil] at member
      · exact ⟨(fun _ _ member => nomatch member), rfl, rfl⟩
    have atomClosed : Valuation.AtomClosed (fun _ => []) := by
      intro index need member
      cases member
    let queryReady : ControlledStoredQuery childControls frontier (.observation (.code certificate)) := {
      annotation := .code child
      within := by
        simpa only [StoredOriginalQuery.headDepth, RichObs.headDepth,
          RichCert.stratifiedDepth, childControls] using within
      sponsored := fun value member => sponsored value (List.mem_append_right _ member) }
    obtain ⟨answer, _, _⟩ := (bank _ funded).computational node provenance childControls
      childFrame childEnvironment childEnvironment frontier (Nat.le_refl _) (Covered.refl _)
      rfl childPaid frameData atomClosed formed .nil (.code certificate) available queryReady
    exact ⟨answer.toRichSupportedValue⟩
  | .domain child | .body child _ _ | .fixedBody child _ _ | .action _ child =>
    exact child.callsOfBank formed caller controls baseline frontier callerPaid sources sponsored bank
  | .resources child transfer =>
    exact child.callsOfBank formed caller controls baseline frontier callerPaid sources
      (fun value member => sponsored value (List.mem_append_left _ member)) bank
termination_by sizeOf annotation

/-- Operative code interpretation consumes the actual unary induction bank,
not a supplied root replay answer. Its chosen right certificate retains the
same sponsors and every caller control bound. -/
theorem WorldCodeRecipeProvenance.rebuildFromBank
    {strata : EquationStratification env}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (annotation : WorldCodeRecipeProvenance strata recipe)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {context : ContextDerivation sourceEnv U source}
    (caller : EndpointState sourceEnv U source expression assigned)
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (frontier : List (World strata.rules.length))
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (sources : annotation.Sources P)
    (sponsored : Sponsored frontier annotation.worlds)
    (bounded : WithinAbove controls.cutoff controls.fuel
      (fun control => recipe.stratifiedDepth (strata.headOrdinal registry) control))
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : footprint.Available available)
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline])) :
    ∃ certificate : RichCert sourceEnv env U registry target caller locals τ relevant profile footprint,
      ∃ ready : ControlledStoredQuery controls frontier (.certificate certificate),
      ready.annotation.worlds = annotation.worlds ∧
      (∀ policy, certificate.headDepth policy = recipe.headDepth policy) ∧
      TypeRelated env U registry target (expression.subst σ) (expression.subst τ) profile := by
  have calls := annotation.callsOfBank formed caller controls baseline frontier callerPaid
    sources sponsored bank
  obtain ⟨certificate, nextAnnotation, worlds, depth, related, within⟩ :=
    annotation.rebuildCertificate henv hscoped formed controls.cutoff controls.cutoffBound
      controls.fuel controls.ordered.constantCount
      (richSchedule .fundamental (Closure.close (caller.dependencyOrigin controls.ordered) environment).cost)
      calls bounded frame substitutions resources caller
  let ready : ControlledStoredQuery controls frontier (.certificate certificate) := {
    annotation := nextAnnotation
    within := within
    sponsored := by
      change Sponsored frontier nextAnnotation.worlds
      rw [worlds]
      exact sponsored }
  exact ⟨certificate, ready, worlds, depth, related⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
