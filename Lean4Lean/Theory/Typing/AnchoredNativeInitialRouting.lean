import Lean4Lean.Theory.Typing.AnchoredNativeInitialTemplate
import Lean4Lean.Theory.Typing.AnchoredNativeSeedCollection

/-! Initial capture routing keeps the original source observer and both
endpoint factor ledgers. A union of field demands need not be a single member
of the fixed valuation: its genuine variable observation is interpreted from
original formation/conversion children instead. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open InductiveSignature NativeRecursorData
open private requirements requirements_available realized_template
  from Lean4Lean.Theory.Typing.AnchoredNativeInitialTemplate
set_option backward.isDefEq.respectTransparency false

structure InitialNativeObservedField (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (declared natural : VExpr) (input : Profile n) where
  support : Profile n
  typed : input.HasType support
  declaredFootprint : Footprint
  declaredCertificate : CodeCert env U registry target locals σ declared support declaredFootprint
  declaredResources : declaredFootprint.Available available
  alignment : InitialNativeAlignment env U registry target locals σ available declared natural support

/-- Interprets the actual finite observation, not an invented aggregate
valuation entry. All semantic calls are the original variable-formation or
outer type-conversion children. -/
theorem HasTypeStrong.initialObservedField
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ A B level}, sourceEnv.IsDefEqStrong U Γ A B (.sort level) →
      GradedJoint env U registry Γ A B (.sort level))
    {source target : List VExpr} {expression natural : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source expression natural structural)
    {index : Nat} {declared : VExpr} (isVariable : expression = .bvar index)
    (lookup : Lookup source index declared)
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {input : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ (.bvar index) input footprint)
    (resources : footprint.Available available) :
    Nonempty (InitialNativeObservedField env U registry target locals σ available declared natural input) := by
  induction original generalizing index declared footprint with
  | bvar found hu formation _ =>
    cases isVariable
    cases found.uniq lookup
    obtain ⟨value⟩ := ((GradedJoint.bvar henv hscoped lookup (earlier formation.refl))
      target locals σ σ available closed hTarget substitutions fits).1 observation resources
    have code := TypeRelated.lower henv value.bound value.typeCode
    exact ⟨{
      support := lowerProfile n value.bound value.support
      typed := value.requestedTyped
      declaredFootprint := value.typeFootprint
      declaredCertificate := value.requestedCertificate
      declaredResources := value.typeAvailable
      alignment := ⟨value.typeFootprint, value.requestedCertificate, value.typeAvailable, .refl, code⟩ }⟩
  | base _ ih => exact ih isVariable lookup substitutions fits observation resources
  | defeq hu conversion _ _ _ _ _ ih =>
    obtain ⟨previous⟩ := ih isVariable lookup substitutions fits observation resources
    obtain ⟨next⟩ := previous.alignment.naturalCertificate.transfer_graded henv hscoped hTarget closed
      (earlier conversion target locals σ σ available closed hTarget substitutions fits).1
      previous.alignment.resources
    have raw := (conversion.defeq.mono hle).substDF henv substitutions.wf hTarget substitutions
    exact ⟨{ previous with alignment := {
      footprint := next.footprint
      naturalCertificate := next.certificate
      resources := next.available
      path := (TypeConversion.single raw).symm.trans previous.alignment.path
      related := TypeRelated.trans henv
        (next.related.symm henv previous.declaredCertificate.formed.wf_value)
        previous.alignment.related } }⟩
  | _ => cases isVariable

/-- The same literal template packet as the single-Need producer, now from
arbitrary finite variable observations at fixed source resources. -/
theorem HasTypeStrong.initialTemplateGuardObserved
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ A B level}, sourceEnv.IsDefEqStrong U Γ A B (.sort level) →
      GradedJoint env U registry Γ A B (.sort level))
    {source target : List VExpr} {index : Nat} {declared natural : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source (.bvar index) natural structural)
    (lookup : Lookup source index declared)
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (templates : NativeIndexTemplates program)
    (naturalArguments declaredArguments : List VExpr)
    (naturalOrigin : natural = templates.naturalDomain.instOuter naturalArguments)
    (declaredOrigin : declared = templates.declaredDomain.instOuter declaredArguments)
    (naturalScope : templates.naturalDomain.ClosedN naturalArguments.length)
    (declaredScope : templates.declaredDomain.ClosedN declaredArguments.length)
    (naturalLocals captureLocals : List Nat)
    {input : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ (.bvar index) input footprint)
    (resources : footprint.Available available) :
    Nonempty (InitialNativeTemplateGuard env U registry target templates locals
      naturalLocals captureLocals σ available naturalArguments declaredArguments input) := by
  obtain ⟨field⟩ := HasTypeStrong.initialObservedField henv hscoped hle earlier original rfl lookup
    closed hTarget substitutions fits observation resources
  have naturalCertificate := Eq.mp (congrArg
    (fun e => CodeCert env U registry target locals σ e field.support field.alignment.footprint)
    naturalOrigin) field.alignment.naturalCertificate
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
  exact ⟨{
    naturalOriginalFootprint := field.alignment.footprint
    naturalOriginalResources := field.alignment.resources
    declaredOriginalFootprint := field.declaredFootprint
    declaredOriginalResources := field.declaredResources
    naturalFootprint := naturalFoot
    declaredFootprint := declaredFoot
    naturalCuts := naturalCuts
    declaredCuts := declaredCuts
    guard := {
      naturalSupport := field.support
      declaredSupport := field.support
      naturalFootprint := naturalFoot
      naturalCertificate := naturalCode
      naturalResources := requirements_available _
      declaredFootprint := declaredFoot
      declaredCertificate := declaredCode
      declaredResources := requirements_available _
      naturalTyped := field.typed
      declaredTyped := field.typed
      alignment := naturalRealized ▸ declaredRealized ▸
        DomainChain.step field.alignment.path field.typed declaredCertificate.formed
          field.alignment.related (.refl _)
      declaredCode := declaredRealized ▸
        (field.alignment.related.symm henv field.typed.wf_type).left_diagonal }
    naturalFootprint_eq := rfl
    declaredFootprint_eq := rfl }⟩

/-- A data-field routing packet retains the actual original variable demand,
its literal native occurrence, and BOTH template factor ledgers. The declared
ledger must be merged into the preceding capture requirements; it is not
replaced by the guard's abstract finite valuation. -/
structure InitialNativeIndexPacket (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (templates : NativeIndexTemplates program)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (nativeArguments captureArguments : List VExpr) where
  sourceIndex : Nat
  nativeOccurrence : nativeArguments[data.indexOffset + templates.slot]? = some (.bvar sourceIndex)
  captureOccurrence : captureArguments[data.indexOffset + templates.field]? = some (.bvar sourceIndex)
  seed : NativeArgumentSeed env U registry target locals σ available (.bvar sourceIndex)
  guardPacket : InitialNativeTemplateGuard env U registry target templates locals
    (List.range (data.indexOffset + templates.slot))
    (List.range (data.indexOffset + templates.field)) σ available
    (nativeArguments.take (data.indexOffset + templates.slot))
    (captureArguments.take (data.indexOffset + templates.field)) seed.demand

end Lean4Lean.AnchoredSource.Adapted
