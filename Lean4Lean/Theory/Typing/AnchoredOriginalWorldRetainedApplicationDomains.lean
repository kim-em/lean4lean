import Lean4Lean.Theory.Typing.AnchoredOriginalRecipePendingNativeDomains
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedApplicationProgress

/-! Native domain elimination selects an atom of the literal retained domain
certificate. Its output action is pending; actual operand F calls use only
the proper original domain budget. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private piRowWorldChildren from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchor
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private noncomputable def appendDomainPath
    (first : GeneralOutputPath env U registry target a b)
    (second : GeneralOutputPath env U registry target b c) :
    GeneralOutputPath env U registry target a c := by
  induction second with
  | refl => exact first
  | action path change ih => exact .action ih change
  | code path change formed ih => exact .code ih change formed
  | pad path ih => exact .pad ih
  | unpad path ih => exact .unpad ih

theorem executePendingNativeDomainApplication
    {n m : Nat} {ambient : Profile n} {support : Profile m} {atom : Atom m}
    {table : List (Key n × Profile n)} {nextRows : List (Key m × Profile m)}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    (domain : EndpointRef sourceEnv U source (.app f a) (.sort u))
    (body : EndpointState sourceEnv U ((.app f a) :: source) B (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (domainCode : RichCert sourceEnv env U registry target (.ref domain) locals σ true ambient domainFootprint)
    (domainReady : ControlledStoredQuery controls frontier (.certificate domainCode))
    (provenance : EndpointProvenance context (.pi hu hv (.ref domain) body))
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : domainFootprint.Available available)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured]))
    (path : GeneralOutputPath env U registry target (r := n + 1) (n := m + 1)
      (AtomData.pi prototypeDomain prototypeBody ambient table)
      (AtomData.pi nextDomain nextBody support nextRows))
    (selected : atom ∈ support.atoms) :
    ∃ origin : RetainedApplicationOrigin provenance.root env registry target source locals σ f a,
    ∃ children : RetainedApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      origin.footprint.Available available ∧ children.worlds ⊆ domainReady.annotation.worlds ∧
      origin.RootedAt (.ref domain) ∧
      children.retainedSize < sizeOf (show WorldCertProvenance strata domainCode from domainReady.annotation) ∧
      (∀ policy, origin.headDepth policy ≤ domainCode.headDepth policy) ∧
      Nonempty (RetainedApplicationStep controls frontier τ available origin) := by
  obtain ⟨pending⟩ := GeneralOutputPath.pendingNativeDomain path
  obtain ⟨original, originalMember, ⟨outputPath⟩⟩ :=
    pending.selectOriginal domainCode.formed selected
  have funding := piRowWorldFunding controls domain body hu hv captured frontier
  have children := piRowWorldChildren controls domain body hu hv captured
  let domainProvenance : EndpointProvenance context (.ref domain) := {
    rootSource := provenance.rootSource, rootExpression := provenance.rootExpression, rootType := provenance.rootType
    root := provenance.root, initial := provenance.initial
    location := .piDomain provenance.location, context_eq := provenance.context_eq }
  have lowerBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref domain) captured]) :=
    fun retained smaller => bank retained (smaller.trans funding.1)
  obtain ⟨origin, annotations, ⟨firstPath⟩, supplied, worlds, rooted, smaller, depth, step⟩ :=
    domainReady.executeRetainedApplicationSized domainProvenance frame captured data closed formed substitutions
      resources
      henv hscoped sourceBelow (singletonSponsoredBelow paid children.1) lowerBank originalMember
  exact ⟨origin, annotations, ⟨appendDomainPath firstPath outputPath⟩, supplied, worlds, rooted, smaller, depth, step⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
