import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedCode
import Lean4Lean.Theory.Typing.AnchoredNativeSyntax
import Lean4Lean.Theory.Typing.AnchoredDomainChainTransport

/-! Finite source support for one index-determined native field. The two
source domains are fixed by registration, not selected from an arbitrary
argument typing. Transport uses the original formation children separately
at the recursor prefix and at the already reconstructed field prefix.

This is not unconditional typed replay of a saturated program. In particular,
a major of J A B x does not supply a conversion B -> A. The stored bridge
must be produced by the original constructor-equation case. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

/-- A field guard retains actual source certificate children under TWO
realizations. They must not be replaced with arbitrary terms having equal raw
substitutions. The input demand is the copied data demand, possibly functional.
The raw path is retained independently of its finite semantic support. -/
structure NativeIndexGuard {env : VEnv} {U : Nat}
    {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (templates : NativeIndexTemplates program)
    (naturalLocals captureLocals : List Nat)
    (naturalRealization captureRealization : Subst)
    (naturalAvailable captureAvailable : Valuation) (input : Profile n) where
  naturalSupport : Profile n
  declaredSupport : Profile n
  naturalFootprint : Footprint
  naturalCertificate : CodeCert env U registry target naturalLocals naturalRealization
    templates.naturalDomain naturalSupport naturalFootprint
  naturalResources : naturalFootprint.Available naturalAvailable
  declaredFootprint : Footprint
  declaredCertificate : CodeCert env U registry target captureLocals captureRealization
    templates.declaredDomain declaredSupport declaredFootprint
  declaredResources : declaredFootprint.Available captureAvailable
  naturalTyped : input.HasType naturalSupport
  declaredTyped : input.HasType declaredSupport
  alignment : DomainChain env U registry target input
    (templates.naturalDomain.subst naturalRealization)
    (templates.declaredDomain.subst captureRealization)
  declaredCode : TypeRelated env U registry target
    (templates.declaredDomain.subst captureRealization)
    (templates.declaredDomain.subst captureRealization) declaredSupport

/-- Move a stored field bridge by interpreting its two actual source-domain
children. No semantic induction is invoked on the bridge or on synthesized
capture typing. The two source contexts may differ. In a staged fundamental
proof the two Joint arguments are the original registered formation payloads.
The predecessor capture substitution must already be genuine; this theorem
never manufactures it from a proof major. -/
theorem NativeIndexGuard.transportOriginal
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr}
    (hTarget : OnCtx target (env.IsType U))
    {data : NativeRecursorData} {program : SaturatedProgram data}
    {templates : NativeIndexTemplates program}
    {naturalLocals captureLocals : List Nat}
    {σ τ κ κ' : Subst} {naturalAvailable captureAvailable : Valuation}
    {input : Profile n} {naturalLevel declaredLevel : VLevel}
    (naturalClosed : naturalAvailable.AtomClosed)
    (captureClosed : captureAvailable.AtomClosed)
    (naturalSubstitutions : Ctx.SubstEq env U target σ τ templates.naturalContext)
    (captureSubstitutions : Ctx.SubstEq env U target κ κ' templates.declaredContext)
    (naturalFits : PairedFits env U registry templates.naturalContext target naturalLocals
      σ τ naturalAvailable)
    (captureFits : PairedFits env U registry templates.declaredContext target captureLocals
      κ κ' captureAvailable)
    (naturalFormation : env.HasType U templates.naturalContext templates.naturalDomain (.sort naturalLevel))
    (declaredFormation : env.HasType U templates.declaredContext templates.declaredDomain (.sort declaredLevel))
    (originalNatural : GradedJoint env U registry templates.naturalContext
      templates.naturalDomain templates.naturalDomain (.sort naturalLevel))
    (originalDeclared : GradedJoint env U registry templates.declaredContext
      templates.declaredDomain templates.declaredDomain (.sort declaredLevel))
    (guard : NativeIndexGuard (env := env) (U := U) (registry := registry)
      (target := target) templates naturalLocals captureLocals σ κ
      naturalAvailable captureAvailable input) :
    Nonempty (NativeIndexGuard (env := env) (U := U) (registry := registry)
      (target := target) templates naturalLocals captureLocals τ κ'
      naturalAvailable captureAvailable input) := by
  obtain ⟨natural⟩ := guard.naturalCertificate.transfer_graded henv hscoped hTarget
    naturalClosed (originalNatural target naturalLocals σ τ naturalAvailable
      naturalClosed hTarget naturalSubstitutions naturalFits).1 guard.naturalResources
  obtain ⟨declared⟩ := guard.declaredCertificate.transfer_graded henv hscoped hTarget
    captureClosed (originalDeclared target captureLocals κ κ' captureAvailable
      captureClosed hTarget captureSubstitutions captureFits).1 guard.declaredResources
  have naturalPath := naturalFormation.substDF henv naturalSubstitutions.wf hTarget naturalSubstitutions
  have declaredPath := declaredFormation.substDF henv captureSubstitutions.wf hTarget captureSubstitutions
  exact ⟨{
    naturalSupport := guard.naturalSupport
    declaredSupport := guard.declaredSupport
    naturalFootprint := natural.footprint
    naturalCertificate := natural.certificate
    naturalResources := natural.available
    declaredFootprint := declared.footprint
    declaredCertificate := declared.certificate
    declaredResources := declared.available
    naturalTyped := guard.naturalTyped
    declaredTyped := guard.declaredTyped
    alignment := .step (TypeConversion.single naturalPath).symm guard.naturalTyped
      guard.naturalCertificate.formed
      (natural.related.symm henv guard.naturalTyped.wf_type)
      (guard.alignment.trans (.step (.single declaredPath) guard.declaredTyped
        guard.declaredCertificate.formed declared.related (.refl _)))
    declaredCode := (declared.related.symm henv guard.declaredTyped.wf_type).left_diagonal }⟩


/-- The actual data-copy step consumes an ORIGINAL index argument result at
its natural domain. The existing left guard converts that result before the
new field is inserted. Only predecessor captures are required in `fits`;
there is no premise already interpreting the field being inserted. -/
theorem NativeIndexGuard.pushCapture
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {data : NativeRecursorData} {program : SaturatedProgram data}
    {templates : NativeIndexTemplates program}
    {naturalLocals captureLocals : List Nat} {σ κ κ' : Subst}
    {naturalAvailable captureAvailable : Valuation}
    {input : Profile n} {argumentSupport : Profile n} {leftIndex rightIndex : VExpr}
    {declaredLevel : VLevel}
    (guard : NativeIndexGuard (env := env) (U := U) (registry := registry)
      (target := target) templates naturalLocals captureLocals σ κ
      naturalAvailable captureAvailable input)
    (closed : captureAvailable.AtomClosed)
    (substitutions : Ctx.SubstEq env U target κ κ' templates.declaredContext)
    (fits : PairedFits env U registry templates.declaredContext target captureLocals κ κ' captureAvailable)
    (formation : env.HasType U templates.declaredContext templates.declaredDomain (.sort declaredLevel))
    (originalDeclared : GradedJoint env U registry templates.declaredContext
      templates.declaredDomain templates.declaredDomain (.sort declaredLevel))
    (rawIndex : env.IsDefEq U target leftIndex rightIndex
      (templates.naturalDomain.subst σ))
    (indexRelated : Related env U registry target leftIndex rightIndex
      (templates.naturalDomain.subst σ) input argumentSupport)
    (localNeeds : List Need)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ n)
    (covered : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade n).atoms,
      atom ∈ input.atoms) :
    Ctx.SubstEq env U target (κ.cons leftIndex) (κ'.cons rightIndex)
      (templates.declaredDomain :: templates.declaredContext) ∧
    PairedFits env U registry (templates.declaredDomain :: templates.declaredContext) target
      (Locals.push captureLocals) (κ.cons leftIndex) (κ'.cons rightIndex)
      (Valuation.push localNeeds captureAvailable) := by
  exact ⟨Ctx.SubstEq.cons substitutions formation (guard.alignment.path.cast rawIndex),
    fits.pushGraded henv hscoped hTarget closed
      (originalDeclared target captureLocals κ κ' captureAvailable closed
        hTarget substitutions fits).1
      guard.declaredCertificate guard.declaredResources guard.declaredTyped
      (guard.alignment.related henv guard.declaredTyped guard.declaredCode indexRelated)
      localNeeds bounded covered⟩

end Lean4Lean.AnchoredSource.Adapted
