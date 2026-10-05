import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramState
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldLegacyPiLeafSelection
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiProgramDomain
import Lean4Lean.Theory.Typing.AnchoredOriginalRecipePendingNativeDomains
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandReadback

/-! Legacy domain transition, including literal Pi leaves with no rows. The
recursive state retains the original plain or sortable domain annotation and
the actual caller frame; pending output operations only change its demand. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

private theorem domainPrefixedCall
    (frontier : List (World count)) (lower : WorldBelow count child parent) :
    CallBelow count (frontier ++ [child]) (frontier ++ [parent]) := by
  induction frontier with
  | nil => exact split_call (by intro world member; cases List.mem_singleton.mp member; exact lower)
  | cons world rest ih => exact ih.cons world

private theorem enterLegacyDomainInput
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {k n : Nat} {ambient : Profile k} {support : Profile n} {atom : Atom n}
    (input : LegacyRowBody env U registry target locals σ A true ambient footprint)
    (annotation : WorldLegacyRowBodyProvenance strata input)
    (resources : footprint.Available available)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domainNode bodyNode))
    (provenance : EndpointProvenance context node)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (within : WithinAbove controls.cutoff controls.fuel
      (fun control => input.certificate.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier annotation.certificate.worlds)
    (annotationBudget : Nat) (smaller : annotation.programSize < annotationBudget)
    (closed : available.AtomClosed)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (pending : PendingDomain env U registry target ambient support)
    (member : atom ∈ support.atoms)
    (continuation : RetainedApplicationDemand env U registry target
      goalFunction goalArgument goalOutput A atom) :
    ∃ next : RetainedProgramState env U registry target strata P frontier
        goalFunction goalArgument goalOutput,
      next.programSize < annotationBudget ∧
      next.demand.readback next.right = continuation.readback τ := by
  obtain ⟨original, present, ⟨output⟩⟩ := pending.selectOriginal input.certificate.formed member
  have cost := Nat.lt_of_lt_of_le
    (binder_domain_cost (domainNode.dependencyOrigin controls.ordered)
      [bodyNode.dependencyOrigin controls.ordered] [] (frame.dependencyEnvironment controls.ordered))
    (route.dependency_cost_le controls.ordered (frame.dependencyEnvironment controls.ordered))
  have lower : WorldBelow strata.rules.length (originalCallWorld controls .fundamental domainNode captured)
      (originalCallWorld controls .fundamental node captured) :=
    original_child (richSchedule_strict cost _ _) _ _ _ _ _
  have domainPaid := singletonSponsoredBelow paid lower
  have domainBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental domainNode captured]) :=
    fun calls smaller => bank calls (smaller.trans (domainPrefixedCall frontier lower))
  let next : RetainedProgramState env U registry target strata P frontier
      goalFunction goalArgument goalOutput := {
    sourceEnv := sourceEnv, source := source, context := context
    expression := A, assigned := .sort u, node := domainNode
    provenance := PrefixRoute.piDomainProvenance route provenance
    controls := controls, locals := locals, left := σ, right := τ
    available := available, frame := frame, captured := captured, data := data
    closed := closed, substitutions := substitutions, sourceBelow := sourceBelow
    relevant := true, rank := k, profile := ambient, footprint := footprint
    program := .legacy input, annotation := .legacy annotation
    within := by simpa only [RetainedTypedProgram.certificate, RichCert.stratifiedDepth, RichCert.headDepth] using within
    sponsored := sponsored, resources := resources
    selected := original, member := present, demand := .output output continuation
    paid := domainPaid, bank := domainBank }
  exact ⟨next, smaller, rfl⟩

/-- Select the actual legacy domain from the same annotated Pi leaf. No row
membership is needed, and both plain and sortable legacy inputs are covered. -/
theorem WorldLegacyPiLeafSelection.enterDomainProgramState
    {strata : EquationStratification env} {P : VEnv → Prop}
    {budget : WorldPiDomainBudget strata}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {n : Nat} {support : Profile n} {rows : List (Key n × Profile n)} {atom : Atom n}
    (selection : WorldLegacyPiLeafSelection env budget U registry target locals σ A B available
      sizeBudget annotationBudget (show Atom (n+1) from .pi nextDomain nextBody support rows))
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domainNode bodyNode))
    (provenance : EndpointProvenance context node)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (within : WithinAbove controls.cutoff controls.fuel
      (fun control => budget.depth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier budget.worlds)
    (closed : available.AtomClosed)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (member : atom ∈ support.atoms)
    (continuation : RetainedApplicationDemand env U registry target
      goalFunction goalArgument goalOutput A atom) :
    ∃ next : RetainedProgramState env U registry target strata P frontier
        goalFunction goalArgument goalOutput,
      next.programSize < annotationBudget ∧
      next.demand.readback next.right = continuation.readback τ := by
  rcases selection with ⟨⟨rank, original, leaf, path, syntaxBound⟩, annotation, included, smaller, depth⟩
  dsimp only at annotation included smaller depth
  cases leaf with
  | plain domain guard rows resources =>
    cases annotation with
    | plain domainAnnotation rowsAnnotation =>
      obtain ⟨pending⟩ := GeneralOutputPath.pendingNativeDomain path
      apply enterLegacyDomainInput (.plain domain) (.plain domainAnnotation)
        (fun i need member => resources i need (List.mem_append_left _ member))
        route provenance frame captured data
        (by
          intro control active
          apply Nat.le_trans _ (within control active)
          simpa only [LegacyRowBody.certificate, SortableCert.headDepth, LegacyPiLeaf.headDepth] using
            Nat.le_trans (Nat.le_max_left _ _)
              (depth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
        (fun world member => sponsored world (included (List.mem_append_left _ member)))
        annotationBudget (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) smaller)
        closed substitutions sourceBelow paid bank pending member continuation
  | sortable domain guard rows resources =>
    cases annotation with
    | sortable domainAnnotation rowsAnnotation =>
      obtain ⟨pending⟩ := GeneralOutputPath.pendingNativeDomain path
      apply enterLegacyDomainInput (.sortable domain) (.sortable domainAnnotation)
        (fun i need member => resources i need (List.mem_append_left _ member))
        route provenance frame captured data
        (by
          intro control active
          apply Nat.le_trans _ (within control active)
          simpa only [LegacyRowBody.certificate, SortableCert.headDepth, LegacyPiLeaf.headDepth] using
            Nat.le_trans (Nat.le_max_left _ _)
              (depth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
        (fun world member => sponsored world (included (List.mem_append_left _ member)))
        annotationBudget (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) smaller)
        closed substitutions sourceBelow paid bank pending member continuation

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
