import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramState
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiProgramDomain
import Lean4Lean.Theory.Typing.AnchoredOriginalRecipePendingNativeDomains
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandReadback

/-! Native domain machine transition. The output state owns the SAME literal
domain program/annotation and unchanged original frame. Only the finite demand
path changes; both the original call and annotation budgets strictly decrease. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private theorem domainPrefixedCall
    (frontier : List (World count)) (lower : WorldBelow count child parent) :
    CallBelow count (frontier ++ [child]) (frontier ++ [parent]) := by
  induction frontier with
  | nil => exact split_call (by intro world member; cases List.mem_singleton.mp member; exact lower)
  | cons world rest ih => exact ih.cons world

theorem enterNativeDomainProgramStateExact
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {n m : Nat} {ambient : Profile n} {table : List (Key n × Profile n)}
    {support : Profile m} {nextRows : List (Key m × Profile m)} {atom : Atom m}
    {domain : RichCert sourceEnv env U registry target domainNode locals σ true ambient domainFootprint}
    {rows : RichRows sourceEnv env U registry target domainNode bodyNode locals σ relevant ambient table rowFootprint}
    {guard : PiGuard env U target σ A B prototypeDomain prototypeBody}
    (domainAnnotation : WorldCertProvenance strata domain)
    (rowsAnnotation : WorldRowsProvenance strata rows)
    (resources : (domainFootprint ++ rowFootprint).Available available)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domainNode bodyNode))
    (provenance : EndpointProvenance context node)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    {incoming : StoredOriginalQuery env U registry target}
    (ready : ControlledStoredQuery controls frontier incoming)
    (included : (WorldPiProgramLeafProvenance.native (hu := hu) (hv := hv)
      (guard := guard) (resources := resources) domainAnnotation rowsAnnotation).worlds ⊆ ready.annotation.worlds)
    (depth : ∀ policy, (RichPiProgramLeaf.native hu hv domain guard rows resources).headDepth policy ≤
      incoming.headDepth policy)
    (budget : Nat)
    (smaller : (WorldPiProgramLeafProvenance.native (hu := hu) (hv := hv)
      (guard := guard) (resources := resources) domainAnnotation rowsAnnotation).retainedSize < budget)
    (closed : available.AtomClosed)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (path : GeneralOutputPath env U registry target (r := n + 1) (n := m + 1)
      (AtomData.pi prototypeDomain prototypeBody ambient table)
      (AtomData.pi nextDomain nextBody support nextRows))
    (member : atom ∈ support.atoms)
    (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput A atom) :
    ∃ next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput,
      next.programSize < budget ∧
      next.demand.readback next.right = continuation.readback τ := by
  obtain ⟨pending⟩ := GeneralOutputPath.pendingNativeDomain path
  obtain ⟨original, present, ⟨output⟩⟩ := pending.selectOriginal domain.formed member
  let domainReady := WorldPiProgramLeafProvenance.nativeDomainReady
    domainAnnotation rowsAnnotation ready included depth
  have domainSize := WorldPiProgramLeafProvenance.nativeDomainSize domainAnnotation rowsAnnotation smaller
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
  let next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput := {
    sourceEnv := sourceEnv, source := source, context := context
    expression := A, assigned := .sort u, node := domainNode
    provenance := PrefixRoute.piDomainProvenance route provenance
    controls := controls, locals := locals, left := σ, right := τ
    available := available, frame := frame, captured := captured, data := data
    closed := closed, substitutions := substitutions, sourceBelow := sourceBelow
    relevant := true, rank := n, profile := ambient, footprint := domainFootprint
    program := .rich domain, annotation := .rich domainAnnotation
    within := domainReady.within, sponsored := domainReady.sponsored
    resources := fun i need member => resources i need (List.mem_append_left _ member)
    selected := original, member := present, demand := .output output continuation
    paid := domainPaid, bank := domainBank }
  exact ⟨next, domainSize, rfl⟩


theorem enterNativeDomainProgramState
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {n m : Nat} {ambient : Profile n} {table : List (Key n × Profile n)}
    {support : Profile m} {nextRows : List (Key m × Profile m)} {atom : Atom m}
    {domain : RichCert sourceEnv env U registry target domainNode locals σ true ambient domainFootprint}
    {rows : RichRows sourceEnv env U registry target domainNode bodyNode locals σ relevant ambient table rowFootprint}
    {guard : PiGuard env U target σ A B prototypeDomain prototypeBody}
    (domainAnnotation : WorldCertProvenance strata domain)
    (rowsAnnotation : WorldRowsProvenance strata rows)
    (resources : (domainFootprint ++ rowFootprint).Available available)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domainNode bodyNode))
    (provenance : EndpointProvenance context node)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    {incoming : StoredOriginalQuery env U registry target}
    (ready : ControlledStoredQuery controls frontier incoming)
    (included : (WorldPiProgramLeafProvenance.native (hu := hu) (hv := hv)
      (guard := guard) (resources := resources) domainAnnotation rowsAnnotation).worlds ⊆ ready.annotation.worlds)
    (depth : ∀ policy, (RichPiProgramLeaf.native hu hv domain guard rows resources).headDepth policy ≤
      incoming.headDepth policy)
    (budget : Nat)
    (smaller : (WorldPiProgramLeafProvenance.native (hu := hu) (hv := hv)
      (guard := guard) (resources := resources) domainAnnotation rowsAnnotation).retainedSize < budget)
    (closed : available.AtomClosed)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (path : GeneralOutputPath env U registry target (r := n + 1) (n := m + 1)
      (AtomData.pi prototypeDomain prototypeBody ambient table)
      (AtomData.pi nextDomain nextBody support nextRows))
    (member : atom ∈ support.atoms)
    (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput A atom) :
    ∃ next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput,
      next.programSize < budget := by
  obtain ⟨next, smaller, _⟩ := enterNativeDomainProgramStateExact domainAnnotation rowsAnnotation
    resources route provenance frame captured data ready included depth budget smaller closed substitutions
    sourceBelow paid bank path member continuation
  exact ⟨next, smaller⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
