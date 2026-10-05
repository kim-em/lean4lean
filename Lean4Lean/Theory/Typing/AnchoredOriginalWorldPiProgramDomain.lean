import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiProgramSelection
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCapturePreservation

/-! Enter the literal domain selected by the joint Pi visitor. Pending domain
actions remain a separate continuation; the recursive certificate and its
annotation are exactly those stored at the original native Pi. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

noncomputable def WorldPiProgramLeafProvenance.nativeDomainReady
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {domain : RichCert sourceEnv env U registry target domainNode locals σ true ambient domainFootprint}
    {rows : RichRows sourceEnv env U registry target domainNode bodyNode locals σ relevant ambient table rowFootprint}
    {guard : PiGuard env U target σ A B prototypeDomain prototypeBody}
    (domainAnnotation : WorldCertProvenance strata domain)
    (rowsAnnotation : WorldRowsProvenance strata rows)
    {incoming : StoredOriginalQuery env U registry target}
    (ready : ControlledStoredQuery controls frontier incoming)
    (included : (WorldPiProgramLeafProvenance.native (hu := hu) (hv := hv)
      (guard := guard) (resources := resources) domainAnnotation rowsAnnotation).worlds ⊆ ready.annotation.worlds)
    (depth : ∀ policy, (RichPiProgramLeaf.native hu hv domain guard rows resources).headDepth policy ≤
      incoming.headDepth policy) : ControlledStoredQuery controls frontier (.certificate domain) where
  annotation := domainAnnotation
  within := by
    intro control active
    change domain.headDepth _ ≤ _
    exact Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (by simpa only [RichPiProgramLeaf.headDepth] using depth _) (ready.within control active))
  sponsored := by
    intro world member
    change world ∈ domainAnnotation.worlds at member
    apply ready.sponsored world
    apply included
    simpa only [WorldPiProgramLeafProvenance.worlds] using List.mem_append_left rowsAnnotation.worlds member

theorem WorldPiProgramLeafProvenance.nativeDomainSize
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {domain : RichCert sourceEnv env U registry target domainNode locals σ true ambient domainFootprint}
    {rows : RichRows sourceEnv env U registry target domainNode bodyNode locals σ relevant ambient table rowFootprint}
    {guard : PiGuard env U target σ A B prototypeDomain prototypeBody}
    (domainAnnotation : WorldCertProvenance strata domain)
    (rowsAnnotation : WorldRowsProvenance strata rows)
    (smaller : (WorldPiProgramLeafProvenance.native (hu := hu) (hv := hv)
      (guard := guard) (resources := resources) domainAnnotation rowsAnnotation).retainedSize < budget) :
    sizeOf domainAnnotation < budget := by
  simp only [WorldPiProgramLeafProvenance.retainedSize] at smaller
  exact Nat.lt_of_le_of_lt (Nat.le_max_left _ _) smaller

noncomputable def PrefixRoute.piDomainProvenance
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domainNode bodyNode))
    (provenance : EndpointProvenance context node) : EndpointProvenance context domainNode :=
  { provenance with
    location := .piDomain (route.locate provenance.location)
    context_eq := provenance.context_eq.trans
      (route.locate_contextDerivation provenance.location provenance.initial).symm }

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
