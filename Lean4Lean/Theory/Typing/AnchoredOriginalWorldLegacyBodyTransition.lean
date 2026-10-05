import Lean4Lean.Theory.Typing.AnchoredOriginalWorldLegacyPiSizedSelection
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeBodyTransition

/-! Execute a selected legacy row at genuine original Pi children. The binder
frame comes from the proper domain F call. Its recursive input remains the
literal tagged legacy body program and annotation, before Rich attachment. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
open private prefixCalls from Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeBodyTransition
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

noncomputable def WorldLegacyPiSizedSelection.attachedReady
    {strata : EquationStratification env} {budget : WorldPiDomainBudget strata}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (selection : WorldLegacyPiSizedSelection env budget U registry target locals σ A B available
      sizeBudget annotationBudget key result)
    (within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => budget.depth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier budget.worlds) :
    (selection.row.attach (domainNode := domainNode) (bodyNode := bodyNode)).Controlled controls frontier := by
  have domainReady : ControlledStoredQuery controls frontier
      (.certificate (RichCert.legacy (node := domainNode) selection.row.domain)) := by
    rw [← selection.domain_eq]
    exact {
      annotation := .legacy selection.domainInput.certificate selection.domainAnnotation.certificate
      within := by
        intro control active
        simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using
          Nat.le_trans (selection.domainDepth _) (within control active)
      sponsored := fun world member => sponsored world (selection.domainWorlds member) }
  exact ⟨domainReady, {
    annotation := .legacy selection.row.body.certificate selection.bodyAnnotation.certificate
    within := by
      intro control active
      simpa only [StoredOriginalQuery.headDepth, LegacyStoredPiRow.attach, RichCert.headDepth] using
        Nat.le_trans (selection.bodyDepth _) (within control active)
    sponsored := fun world member => sponsored world (selection.bodyWorlds member) }⟩

/-- The only semantic call is the real domain child. The selected raw body
and its exact annotation remain the machine's next program; the attachment
wrapper is recorded by equality and is not used for recursion descent. -/
theorem WorldLegacyPiSizedSelection.enterOriginalBodyWorldExact
    {strata : EquationStratification env} {P : VEnv → Prop}
    {budget : WorldPiDomainBudget strata}
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    (selection : WorldLegacyPiSizedSelection env budget U registry target locals σ A B available
      sizeBudget annotationBudget key result)
    (provenance : EndpointProvenance context (.pi hu hv (.ref domain) body))
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => budget.depth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier budget.worlds)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured]))
    (admitted : Admitted env U registry target key anchor anchor) :
    ∃ execution : RichPiRowBodyExecution (P := P) (context := context)
      controls frontier domain body selection.row.attach τ anchor hu hv captured,
      (show WorldCertProvenance strata selection.row.attach.body from execution.ready.annotation) =
        .legacy selection.row.body.certificate selection.bodyAnnotation.certificate ∧
      selection.bodyAnnotation.programSize < annotationBudget ∧
      selection.bodyAnnotation.certificate.worlds ⊆ budget.worlds ∧
      (∀ policy, selection.row.body.certificate.headDepth policy ≤ budget.depth policy) ∧
      selection.row.bodyFootprint.Available
        (Valuation.push (selection.row.bodyFootprint.localNeeds ++
          selection.row.bodyFootprint.localNeeds.flatMap Need.singletons) available) := by
  let ready := selection.attachedReady (domainNode := EndpointState.ref domain) (bodyNode := body) within sponsored
  obtain ⟨execution, sameReady⟩ := selection.row.attach.enterOriginalBodyWorldExact provenance frame captured data
    closed formed substitutions henv hscoped sourceBelow paid bank ready
    (selection.pending.oldAdmission henv hscoped formed selection.row.guard.anchor admitted)
  refine ⟨execution, ?_, selection.bodySmaller, selection.bodyWorlds, selection.bodyDepth, execution.resources⟩
  rw [sameReady]
  rfl

/-- The caller's actual prefix supplies both the Pi provenance and its lower
bank. Domain/body originals are never reconstructed from legacy raw syntax. -/
theorem WorldLegacyPiSizedSelection.enterPrefixBodyWorldExact
    {strata : EquationStratification env} {P : VEnv → Prop}
    {budget : WorldPiDomainBudget strata}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    (selection : WorldLegacyPiSizedSelection env budget U registry target locals σ A B available
      sizeBudget annotationBudget key result)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv (.ref domain) body))
    (provenance : EndpointProvenance context node)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => budget.depth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier budget.worlds)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (admitted : Admitted env U registry target key anchor anchor) :
    ∃ execution : RichPiRowBodyExecution (P := P) (context := context)
      controls frontier domain body selection.row.attach τ anchor hu hv captured,
      (show WorldCertProvenance strata selection.row.attach.body from execution.ready.annotation) =
        .legacy selection.row.body.certificate selection.bodyAnnotation.certificate ∧
      selection.bodyAnnotation.programSize < annotationBudget ∧
      selection.bodyAnnotation.certificate.worlds ⊆ budget.worlds ∧
      (∀ policy, selection.row.body.certificate.headDepth policy ≤ budget.depth policy) ∧
      selection.row.bodyFootprint.Available
        (Valuation.push (selection.row.bodyFootprint.localNeeds ++
          selection.row.bodyFootprint.localNeeds.flatMap Need.singletons) available) := by
  let piProvenance : EndpointProvenance context (.pi hu hv (.ref domain) body) := {
    provenance with
    location := route.locate provenance.location
    context_eq := provenance.context_eq.trans
      (route.locate_contextDerivation provenance.location provenance.initial).symm }
  have cost := route.dependency_cost_le controls.ordered (frame.dependencyEnvironment controls.ordered)
  have parentRelation : originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured =
      originalCallWorld controls .fundamental node captured ∨
      WorldBelow strata.rules.length (originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured)
        (originalCallWorld controls .fundamental node captured) := by
    rcases Nat.eq_or_lt_of_le cost with same | smaller
    · left
      simp only [originalCallWorld, same]
    · exact .inr (original_child (richSchedule_strict smaller _ _) _ _ _ _ _)
  have piPaid : Sponsored frontier [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured] := by
    rcases parentRelation with same | smaller
    · simpa only [same] using paid
    · exact singletonSponsoredBelow paid smaller
  have piBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured]) := by
    intro calls lower
    apply bank calls
    rcases parentRelation with same | smaller
    · simpa only [same] using lower
    · exact lower.trans (prefixCalls frontier smaller)
  exact selection.enterOriginalBodyWorldExact piProvenance frame captured data within sponsored
    closed formed substitutions henv hscoped sourceBelow piPaid piBank admitted

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
