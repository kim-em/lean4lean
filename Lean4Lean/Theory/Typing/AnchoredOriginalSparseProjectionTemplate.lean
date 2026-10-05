import Lean4Lean.Theory.Typing.AnchoredOriginalCaptureSubstitution
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericProjection
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeHeadDepth

/-! Sparse projection templates retain the fully instantiated original
source. The residual syntax has no claimed original typing derivation and
no total header substitution. Its two realizations are computed from actual
caller substitutions; only the displayed expression is interpreted. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor OriginalFactorCut
open private unselected_var from Lean4Lean.Theory.Typing.AnchoredOriginalCaptureSubstitution
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- A projection which is not a whole captured operand exposes only its
major template. No inverse-typing claim for its field metadata follows. -/
theorem capture_proj_inv
    (equal : VExpr.proj name index major = template.subst ((Subst.ofList arguments).liftN depth))
    (notSelected : ¬CaptureSelected arguments depth template) :
    ∃ majorTemplate, template = .proj name index majorTemplate ∧
      major = majorTemplate.subst ((Subst.ofList arguments).liftN depth) := by
  cases template <;> simp only [subst, reduceCtorEq, proj.injEq] at equal
  · have h := unselected_var arguments depth _ notSelected
    exact (VExpr.noConfusion (equal.trans h))
  · obtain ⟨rfl, rfl, equal⟩ := equal
    exact ⟨_, rfl, equal⟩

/-- A finite residual certificate is attached to its actual instantiated
source node. In particular `template` need not be typable in a declaration
header after replacing all prior fields by projections. -/
structure InstantiatedTemplateCertificate
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    (node : EndpointState sourceEnv U source expression assigned)
    (arguments : List VExpr) (depth : Nat) (template : VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (relevant : Bool) (profile : Profile n) where
  expression_eq : expression = template.subst ((Subst.ofList arguments).liftN depth)
  footprint : Footprint
  certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint
  resources : footprint.Available available

namespace InstantiatedTemplateCertificate

/-- This realization is syntax alone, not a purported typed substitution
for every parameter and prior-field slot. -/
def realization (arguments : List VExpr) (depth : Nat) (σ : Subst) : Subst :=
  ((Subst.ofList arguments).liftN depth).comp σ

theorem realized
    {node : EndpointState sourceEnv U source expression assigned}
    (packet : InstantiatedTemplateCertificate sourceEnv env U registry target node
      arguments depth template locals σ available relevant profile) :
    expression.subst σ = template.subst (realization arguments depth σ) := by
  rw [packet.expression_eq, subst_subst]
  rfl

/-- Attach an existing original certificate without changing any source
metadata, closure, resource, or declaration-head depth. -/
def ofOriginal
    {footprint : Footprint}
    {node : EndpointState sourceEnv U source expression assigned}
    (equal : expression = template.subst ((Subst.ofList arguments).liftN depth))
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (resources : footprint.Available available) :
    InstantiatedTemplateCertificate sourceEnv env U registry target node arguments depth template
      locals σ available relevant profile :=
  ⟨equal, footprint, certificate, resources⟩

end InstantiatedTemplateCertificate

/-- The hard projection leaf of a sparse code template. The two recursive
calls are at the actual instantiated major and field originals, with strict
computed costs. The returned certificate is at that same original projection
node; its metadata never moves to an invented residual header node.

Only the ordinary caller context requires `SubstEq`. There is no typing or
`SubstEq` premise for the capture slots or the residual template context. -/
theorem sparseProjectionCodeStep
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initialContext : ContextDerivation sourceEnv U rootSource)
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead node)
    (location : Located root (projectionNatural head))
    (lineage : location.contextDerivation initialContext = context)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (ordered : sourceEnv.Ordered)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (majorQuery : RichObs sourceEnv env U registry target (.ref (.right head.major))
      locals σ (Profile.singleton (n := n + 1) (.record record)) majorFootprint)
    (fieldCode : RichCert sourceEnv env U registry target head.field locals σ true support fieldFootprint)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain (head.fieldType.subst σ))
    (resources : (majorFootprint ++ fieldFootprint).Available available)
    (sorted : request.input.HasType (.sort relevant))
    (display : VExpr.proj name index major =
      template.subst ((Subst.ofList arguments).liftN depth))
    (majorF : OriginalComputationalInductionAt env registry ordered initialContext
      (.projMajor location)
      (Closure.close ((projectionNatural head).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost)
    (fieldF : OriginalCodeInductionAt env registry ordered initialContext (.projField location)
      (Closure.close ((projectionNatural head).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost) :
    ∃ answer : RichComputationalValue sourceEnv env U registry target (projectionNatural head)
        locals σ τ available request.input,
      ∃ packet : InstantiatedTemplateCertificate sourceEnv env U registry target (projectionNatural head)
          arguments depth template locals τ available relevant request.input,
        TypeRelated env U registry target
          (template.subst (InstantiatedTemplateCertificate.realization arguments depth σ))
          (template.subst (InstantiatedTemplateCertificate.realization arguments depth τ)) request.input ∧
        ∀ policy, packet.certificate.headDepth policy ≤ answer.rightQuery.observation.headDepth policy := by
  obtain ⟨answer⟩ := frame.projectionComputationalStep initialContext head location lineage
    henv hscoped sourceBelow ordered closed formed substitutions nameEq member majorQuery
    fieldCode typed alignment resources majorF fieldF
  obtain ⟨footprint, certificate, available, depthBound⟩ := answer.rightQuery.code_headDepth henv sorted
  let packet := InstantiatedTemplateCertificate.ofOriginal display certificate available
  have interpreted := answer.related.code_of_sortable henv hscoped formed sorted
  refine ⟨answer, packet, ?_, depthBound⟩
  simpa only [InstantiatedTemplateCertificate.realization, ← subst_subst, ← display] using interpreted

end Lean4Lean.AnchoredSource.Adapted
