import Lean4Lean.Theory.Typing.AnchoredNativeConvertedSpine
import Lean4Lean.Theory.Typing.AnchoredNativeInitialRouting
import Lean4Lean.Theory.Typing.AnchoredDomainChainTransport

/-! A copied index field may be typed through a converted function spine.
The original argument type is not asserted to equal the registered domain.
Instead, an actual registered-domain certificate is pulled through the original
function conversion and combined with the original variable's declaration
alignment. The two endpoint supports remain independent. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open InductiveSignature NativeRecursorData
open private requirements requirements_available realized_template
  from Lean4Lean.Theory.Typing.AnchoredNativeInitialTemplate
set_option backward.isDefEq.respectTransparency false

/-- The first nontrivial converted native index: a registered dependent
second domain, with an arbitrary ORIGINAL function-type conversion after the
first argument. Every certificate and cut is produced from actual original
children. In particular no typing at the registered second domain is assumed. -/
theorem HasTypeStrong.convertedIndexTemplateGuard
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {D E R firstArgument natural C declared : VExpr} {index : Nat} {structural : Bool}
    {conversionLevel : VLevel}
    (header : SourcePiFormation (OriginalTypePayload sourceEnv env U registry)
      source (.forallE D (.forallE E R)))
    (first : OriginalTypePayload sourceEnv env U registry source firstArgument D)
    (original : sourceEnv.HasTypeStrong U source (.bvar index) natural structural)
    (lookup : Lookup source index declared)
    {conversion : sourceEnv.IsDefEqStrong U source ((VExpr.forallE E R).inst firstArgument)
      (.forallE natural C) (.sort conversionLevel)}
    (converted : OriginalPayload sourceEnv env U registry conversion)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (templates : NativeIndexTemplates program)
    (naturalArguments declaredArguments : List VExpr)
    (naturalOrigin : E.inst firstArgument = templates.naturalDomain.instOuter naturalArguments)
    (declaredOrigin : declared = templates.declaredDomain.instOuter declaredArguments)
    (naturalScope : templates.naturalDomain.ClosedN naturalArguments.length)
    (declaredScope : templates.declaredDomain.ClosedN declaredArguments.length)
    (naturalLocals captureLocals : List Nat)
    {input : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ (.bvar index) input footprint)
    (resources : footprint.Available available) :
    Nonempty (InitialNativeTemplateGuard env U registry target templates locals
      naturalLocals captureLocals σ available naturalArguments declaredArguments input) := by
  obtain ⟨registered⟩ := convertedSecondInput henv hscoped hle header first
    ⟨original.refl, earlier original.refl⟩ converted closed hTarget substitutions fits
    observation resources
  obtain ⟨field⟩ := HasTypeStrong.initialObservedField henv hscoped hle
    (fun h => earlier h) original rfl lookup closed hTarget substitutions fits observation resources
  have naturalCertificate := Eq.mp (congrArg
    (fun e => CodeCert env U registry target locals σ e registered.support registered.footprint)
    naturalOrigin) registered.certificate
  have declaredCertificate := Eq.mp (congrArg
    (fun e => CodeCert env U registry target locals σ e field.support field.declaredFootprint)
    declaredOrigin) field.declaredCertificate
  obtain ⟨naturalFoot, ⟨naturalCode⟩, ⟨naturalCuts⟩⟩ :=
    naturalCertificate.factorNativeTemplate naturalScope naturalLocals
  obtain ⟨declaredFoot, ⟨declaredCode⟩, ⟨declaredCuts⟩⟩ :=
    declaredCertificate.factorNativeTemplate declaredScope captureLocals
  have naturalRealized := realized_template naturalScope σ
  have declaredRealized := realized_template declaredScope σ
  rw [← naturalOrigin] at naturalRealized
  rw [← declaredOrigin] at declaredRealized
  have variableChain : DomainChain env U registry target input
      (natural.subst σ) (declared.subst σ) :=
    .step field.alignment.path field.typed field.declaredCertificate.formed
      field.alignment.related (.refl _)
  have chain := (registered.alignment.symm henv).trans variableChain
  exact ⟨{
    naturalOriginalFootprint := registered.footprint
    naturalOriginalResources := registered.resources
    declaredOriginalFootprint := field.declaredFootprint
    declaredOriginalResources := field.declaredResources
    naturalFootprint := naturalFoot
    declaredFootprint := declaredFoot
    naturalCuts := naturalCuts
    declaredCuts := declaredCuts
    guard := {
      naturalSupport := registered.support
      declaredSupport := field.support
      naturalFootprint := naturalFoot
      naturalCertificate := naturalCode
      naturalResources := requirements_available _
      declaredFootprint := declaredFoot
      declaredCertificate := declaredCode
      declaredResources := requirements_available _
      naturalTyped := registered.typed
      declaredTyped := field.typed
      declaredCode := declaredRealized ▸ (field.alignment.related.symm henv field.typed.wf_type).left_diagonal
      alignment := naturalRealized ▸ declaredRealized ▸ chain }
    naturalFootprint_eq := rfl
    declaredFootprint_eq := rfl }⟩

end Lean4Lean.AnchoredSource.Adapted
