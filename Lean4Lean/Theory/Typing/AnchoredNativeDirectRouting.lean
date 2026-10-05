import Lean4Lean.Theory.Typing.AnchoredNativeCodePath
import Lean4Lean.Theory.Typing.AnchoredNativeCaptureRouting

/-! Route a copied field from the registered prefix's actual Pi row. The
natural endpoint carries a direct ledger of original argument observations;
only the declaration endpoint is factored into constructor-field templates.
No typing of the field at the registered domain is assumed. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open InductiveSignature NativeRecursorData
open private requirements requirements_available realized_template
  from Lean4Lean.Theory.Typing.AnchoredNativeInitialTemplate
set_option backward.isDefEq.respectTransparency false

structure InitialNativeDirectTemplateGuard
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) {data : NativeRecursorData} {program : SaturatedProgram data}
    (templates : NativeIndexTemplates program)
    (locals naturalLocals captureLocals : List Nat) (σ : Subst) (available : Valuation)
    (naturalArguments declaredArguments : List VExpr) (input : Profile n) where
  naturalFootprint : Footprint
  naturalLedger : NativeArgumentLedger env U registry target locals σ available
    naturalArguments naturalFootprint
  declaredOriginalFootprint : Footprint
  declaredOriginalResources : declaredOriginalFootprint.Available available
  declaredFootprint : Footprint
  declaredCuts : ParamsFootprint env U registry target locals σ declaredArguments
    declaredOriginalFootprint declaredFootprint
  guard : NativeIndexGuard (env := env) (U := U) (registry := registry) (target := target)
    templates naturalLocals captureLocals
    (nativeCaptureSubst (naturalArguments.map (·.subst σ)))
    (nativeCaptureSubst (declaredArguments.map (·.subst σ)))
    (requirements naturalFootprint) (requirements declaredFootprint) input
  naturalFootprint_eq : guard.naturalFootprint = naturalFootprint
  declaredFootprint_eq : guard.declaredFootprint = declaredFootprint

/-- The registered row supplies one side of the domain alignment. The
other side comes from the actual variable's original conversion children.
These chains may use different supports throughout. -/
theorem HasTypeStrong.initialDirectTemplateGuard
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ A B level}, sourceEnv.IsDefEqStrong U Γ A B (.sort level) →
      GradedJoint env U registry Γ A B (.sort level))
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {index : Nat} {actual declared : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source (.bvar index) actual structural)
    (lookup : Lookup source index declared)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (templates : NativeIndexTemplates program)
    (naturalArguments declaredArguments : List VExpr)
    (declaredOrigin : declared = templates.declaredDomain.instOuter declaredArguments)
    (declaredScope : templates.declaredDomain.ClosedN declaredArguments.length)
    (naturalLocals captureLocals : List Nat)
    {input : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ (.bvar index) input footprint)
    (resources : footprint.Available available)
    {rowAvailable : Valuation} {body : VExpr} {result : Profile n}
    (row : PiRowCertificate env U registry target naturalLocals
      (nativeCaptureSubst (naturalArguments.map (·.subst σ))) rowAvailable
      templates.naturalDomain body ⟨actual.subst σ, σ index, input⟩ result)
    (observed : NativeObservedValuation env U registry target locals σ available
      naturalArguments rowAvailable) :
    Nonempty (InitialNativeDirectTemplateGuard env U registry target templates locals
      naturalLocals captureLocals σ available naturalArguments declaredArguments input) := by
  obtain ⟨field⟩ := HasTypeStrong.initialObservedField henv hscoped hle earlier original rfl lookup
    closed hTarget substitutions fits observation resources
  obtain ⟨naturalLedger⟩ := observed.ledger row.domainAvailable
  have declaredCertificate := Eq.mp (congrArg
    (fun e => CodeCert env U registry target locals σ e field.support field.declaredFootprint)
    declaredOrigin) field.declaredCertificate
  obtain ⟨declaredFoot, ⟨declaredCode⟩, ⟨declaredCuts⟩⟩ :=
    declaredCertificate.factorNativeTemplate declaredScope captureLocals
  have declaredRealized := realized_template declaredScope σ
  rw [← declaredOrigin] at declaredRealized
  have variableChain : DomainChain env U registry target input
      (actual.subst σ) (declared.subst σ) :=
    .step field.alignment.path field.typed field.declaredCertificate.formed
      field.alignment.related (.refl _)
  exact ⟨{
    naturalFootprint := row.domainFootprint
    naturalLedger := naturalLedger
    declaredOriginalFootprint := field.declaredFootprint
    declaredOriginalResources := field.declaredResources
    declaredFootprint := declaredFoot
    declaredCuts := declaredCuts
    guard := {
      naturalSupport := row.domainSupport
      declaredSupport := field.support
      naturalFootprint := row.domainFootprint
      naturalCertificate := row.domain
      naturalResources := requirements_available _
      declaredFootprint := declaredFoot
      declaredCertificate := declaredCode
      declaredResources := requirements_available _
      naturalTyped := row.inputTyped
      declaredTyped := field.typed
      alignment := declaredRealized ▸ (row.alignment.symm henv).trans variableChain
      declaredCode := declaredRealized ▸
        (field.alignment.related.symm henv field.typed.wf_type).left_diagonal }
    naturalFootprint_eq := rfl
    declaredFootprint_eq := rfl }⟩

structure InitialNativeDirectIndexPreparation (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (templates : NativeIndexTemplates program) (locals : List Nat) (σ : Subst)
    (available : Valuation) (nativeArguments captureArguments : List VExpr)
    (required : Footprint) (minimum : Nat) where
  sourceIndex : Nat
  nativeOccurrence : nativeArguments[data.indexOffset + templates.slot]? = some (.bvar sourceIndex)
  captureOccurrence : captureArguments[data.indexOffset + templates.field]? = some (.bvar sourceIndex)
  seed : NativeArgumentSeed env U registry target locals σ available (.bvar sourceIndex)
  guardPacket : InitialNativeDirectTemplateGuard env U registry target templates locals
    (List.range (data.indexOffset + templates.slot))
    (List.range (data.indexOffset + templates.field)) σ available
    (nativeArguments.take (data.indexOffset + templates.slot))
    (captureArguments.take (data.indexOffset + templates.field)) seed.demand
  bound : minimum ≤ seed.rank
  packed : Profile seed.rank
  pack : BinderPack seed.rank packed required (externalArguments required)
  covered : ∀ atom ∈ packed.atoms, atom ∈ seed.demand.atoms
  previous : NativeArgumentLedger env U registry target locals σ available
    (captureArguments.take (data.indexOffset + templates.field))
    (guardPacket.guard.declaredFootprint ++ externalArguments required)
  native : NativeArgumentLedger env U registry target locals σ available nativeArguments
    (Footprint.sourceLift (.skipN .refl (nativeArguments.length - (data.indexOffset + templates.slot)))
      guardPacket.guard.naturalFootprint ++
      [(nativeArguments.length - 1 - (data.indexOffset + templates.slot), ⟨seed.rank, seed.demand⟩)])

/-- The seed is collected before the registered-prefix walk. The resulting
row is then consumed here; no function producing arbitrary rows is required. -/
theorem NativeSeedCover.prepareDirectIndex
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ A B level}, sourceEnv.IsDefEqStrong U Γ A B (.sort level) →
      GradedJoint env U registry Γ A B (.sort level))
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (templates : NativeIndexTemplates program)
    {nativeArguments captureArguments : List VExpr} {index : Nat}
    (nativeOccurrence : nativeArguments[data.indexOffset + templates.slot]? = some (.bvar index))
    (captureOccurrence : captureArguments[data.indexOffset + templates.field]? = some (.bvar index))
    {declared actual : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source (.bvar index) actual structural)
    (lookup : Lookup source index declared)
    (declaredOrigin : declared = templates.declaredDomain.instOuter
      (captureArguments.take (data.indexOffset + templates.field)))
    (declaredScope : templates.declaredDomain.ClosedN
      (captureArguments.take (data.indexOffset + templates.field)).length)
    {required : Footprint} {minimum : Nat}
    (ledger : NativeArgumentLedger env U registry target locals σ available
      (captureArguments.take (data.indexOffset + templates.field + 1)) required)
    (cover : NativeSeedCover env U registry target locals σ available (.bvar index)
      (argumentNeeds required 0) minimum)
    {rowAvailable : Valuation} {body : VExpr} {result : Profile cover.seed.rank}
    (row : PiRowCertificate env U registry target (List.range (data.indexOffset + templates.slot))
      (nativeCaptureSubst ((nativeArguments.take (data.indexOffset + templates.slot)).map (·.subst σ)))
      rowAvailable templates.naturalDomain body
      ⟨actual.subst σ, σ index, cover.seed.demand⟩ result)
    (observed : NativeObservedValuation env U registry target locals σ available
      (nativeArguments.take (data.indexOffset + templates.slot)) rowAvailable) :
    Nonempty (InitialNativeDirectIndexPreparation env U registry target templates locals σ available
      nativeArguments captureArguments required minimum) := by
  have captureNext : captureArguments.take (data.indexOffset + templates.field + 1) =
      captureArguments.take (data.indexOffset + templates.field) ++ [.bvar index] := by
    rw [List.take_add_one, captureOccurrence]
    rfl
  have current := captureNext ▸ ledger
  obtain ⟨guard⟩ := HasTypeStrong.initialDirectTemplateGuard henv hscoped hle earlier original lookup
    closed hTarget substitutions fits templates _ _ declaredOrigin declaredScope
    (List.range (data.indexOffset + templates.slot)) (List.range (data.indexOffset + templates.field))
    cover.seed.observation cover.seed.resources row observed
  obtain ⟨packed, pack, covered⟩ := cover.packLast
  have declaredScoped : Footprint.Scoped
      (captureArguments.take (data.indexOffset + templates.field)).length guard.declaredFootprint := by
    rw [← guard.declaredFootprint_eq]
    exact guard.guard.declaredCertificate.scoped declaredScope
  obtain ⟨declaredLedger⟩ := guard.declaredCuts.argumentLedger guard.declaredOriginalResources declaredScoped
  have nativeBound := (List.getElem?_eq_some_iff.mp nativeOccurrence).1
  have nativeValue := (List.getElem?_eq_some_iff.mp nativeOccurrence).2
  have nativePrefix := guard.naturalLedger.intoPrefix rfl (Nat.le_of_lt nativeBound)
  have previous := declaredLedger.append current.withoutLast
  rw [← guard.declaredFootprint_eq] at previous
  rw [← guard.naturalFootprint_eq] at nativePrefix
  have nativeIndexBound : nativeArguments.length - 1 - (data.indexOffset + templates.slot) < nativeArguments.length := by omega
  have nativeIndex : nativeArguments.length - 1 -
      (nativeArguments.length - 1 - (data.indexOffset + templates.slot)) =
      data.indexOffset + templates.slot := by omega
  have field : Obs env U registry target locals σ
      nativeArguments[nativeArguments.length - 1 -
        (nativeArguments.length - 1 - (data.indexOffset + templates.slot))]
      cover.seed.demand cover.seed.footprint := by
    simpa only [nativeIndex, nativeValue] using cover.seed.observation
  have copied := NativeArgumentLedger.cons (need := ⟨cover.seed.rank, cover.seed.demand⟩)
    nativeIndexBound field cover.seed.resources .nil
  exact ⟨{
    sourceIndex := index
    nativeOccurrence := nativeOccurrence
    captureOccurrence := captureOccurrence
    seed := cover.seed
    guardPacket := guard
    bound := cover.bound
    packed := packed
    pack := pack
    covered := covered
    previous := previous
    native := nativePrefix.append copied }⟩

/-- Finish the actual core capture support and its original-source argument
ledger after the earlier capture prefix has been routed. -/
noncomputable def InitialNativeDirectIndexPreparation.finish
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {program : SaturatedProgram data}
    {templates : NativeIndexTemplates program}
    (prepared : InitialNativeDirectIndexPreparation env U registry target templates locals σ available
      nativeArguments captureArguments required minimum)
    (nativeValues : program.prefixArgs = nativeArguments.map (·.subst σ))
    (capturedValues : witnesses = captureArguments.map (·.subst σ))
    (previous : InitialNativeCaptureRoute env U registry target program witnesses locals σ available
      nativeArguments templates.field
      (prepared.guardPacket.guard.declaredFootprint ++ externalArguments required)) :
    InitialNativeCaptureRoute env U registry target program witnesses locals σ available
      nativeArguments (templates.field + 1) required := by
  let packet := prepared.guardPacket
  let guard : NativeIndexGuard (env := env) (U := U) (registry := registry) (target := target)
      templates (List.range (data.indexOffset + templates.slot))
      (List.range (data.indexOffset + templates.field))
      (nativeCaptureSubst (program.prefixArgs.take (data.indexOffset + templates.slot)))
      (nativeCaptureSubst (witnesses.take (data.indexOffset + templates.field)))
      (requirements packet.naturalFootprint) (requirements packet.declaredFootprint) prepared.seed.demand := {
    naturalSupport := packet.guard.naturalSupport
    declaredSupport := packet.guard.declaredSupport
    naturalFootprint := packet.guard.naturalFootprint
    naturalCertificate := by
      simpa only [nativeValues, List.map_take] using packet.guard.naturalCertificate
    naturalResources := packet.guard.naturalResources
    declaredFootprint := packet.guard.declaredFootprint
    declaredCertificate := by
      simpa only [capturedValues, List.map_take] using packet.guard.declaredCertificate
    declaredResources := packet.guard.declaredResources
    naturalTyped := packet.guard.naturalTyped
    declaredTyped := packet.guard.declaredTyped
    alignment := by
      simpa only [nativeValues, capturedValues, List.map_take] using packet.guard.alignment
    declaredCode := by
      simpa only [capturedValues, List.map_take] using packet.guard.declaredCode }
  have naturalValue : program.prefixArgs[data.indexOffset + templates.slot]? = some (σ prepared.sourceIndex) := by
    rw [nativeValues, List.getElem?_map, prepared.nativeOccurrence]
    rfl
  have capturedValue : witnesses[data.indexOffset + templates.field]? = some (σ prepared.sourceIndex) := by
    rw [capturedValues, List.getElem?_map, prepared.captureOccurrence]
    rfl
  have previousSupport : NativeCaptureSupport env U registry target program witnesses templates.field
      (guard.declaredFootprint ++ externalArguments required) previous.nativeFootprint := by
    simpa only [guard, packet] using previous.support
  refine ⟨_, .index guard naturalValue capturedValue prepared.pack prepared.covered previousSupport, ?_⟩
  simpa only [nativeValues, List.length_map, List.append_assoc, guard, packet] using
    previous.ledger.append prepared.native

end Lean4Lean.AnchoredSource.Adapted
