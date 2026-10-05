import Lean4Lean.Theory.Typing.AnchoredNativeArgumentLedger
import Lean4Lean.Theory.Typing.AnchoredNativeProofSeed

/-! Concrete initial index routing. Declared-domain cuts join the remaining
capture ledger before recursion; natural-domain cuts and the actual field
observation join the native ledger afterward. Every ledger entry retains an
original source observer at the fixed valuation. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open InductiveSignature NativeRecursorData
open private requirements realized_template from Lean4Lean.Theory.Typing.AnchoredNativeInitialTemplate
set_option backward.isDefEq.respectTransparency false

structure InitialNativeIndexPreparation (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (templates : NativeIndexTemplates program) (locals : List Nat) (σ : Subst)
    (available : Valuation) (nativeArguments captureArguments : List VExpr)
    (required : Footprint) (minimum : Nat) where
  packet : InitialNativeIndexPacket env U registry target templates locals σ available nativeArguments captureArguments
  bound : minimum ≤ packet.seed.rank
  packed : Profile packet.seed.rank
  pack : BinderPack packet.seed.rank packed required (externalArguments required)
  covered : ∀ atom ∈ packed.atoms, atom ∈ packet.seed.demand.atoms
  previous : NativeArgumentLedger env U registry target locals σ available
    (captureArguments.take (data.indexOffset + templates.field))
    (packet.guardPacket.guard.declaredFootprint ++ externalArguments required)
  native : NativeArgumentLedger env U registry target locals σ available nativeArguments
    (Footprint.sourceLift (.skipN .refl (nativeArguments.length - (data.indexOffset + templates.slot)))
      packet.guardPacket.guard.naturalFootprint ++
      [(nativeArguments.length - 1 - (data.indexOffset + templates.slot), ⟨packet.seed.rank, packet.seed.demand⟩)])

/-- One actual index step. The field input is collected from its finite
ledger, interpreted through ORIGINAL variable/conversion children, and only
then used in the native field guard. -/
theorem NativeArgumentLedger.prepareIndex
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
    {declared natural : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source (.bvar index) natural structural)
    (lookup : Lookup source index declared)
    (naturalOrigin : natural = templates.naturalDomain.instOuter
      (nativeArguments.take (data.indexOffset + templates.slot)))
    (declaredOrigin : declared = templates.declaredDomain.instOuter
      (captureArguments.take (data.indexOffset + templates.field)))
    (naturalScope : templates.naturalDomain.ClosedN
      (nativeArguments.take (data.indexOffset + templates.slot)).length)
    (declaredScope : templates.declaredDomain.ClosedN
      (captureArguments.take (data.indexOffset + templates.field)).length)
    {required : Footprint}
    (ledger : NativeArgumentLedger env U registry target locals σ available
      (captureArguments.take (data.indexOffset + templates.field + 1)) required)
    (minimum : Nat) :
    Nonempty (InitialNativeIndexPreparation env U registry target templates locals σ available
      nativeArguments captureArguments required minimum) := by
  have captureNext : captureArguments.take (data.indexOffset + templates.field + 1) =
      captureArguments.take (data.indexOffset + templates.field) ++ [.bvar index] := by
    rw [List.take_add_one, captureOccurrence]
    rfl
  have current := captureNext ▸ ledger
  obtain ⟨cover⟩ := current.lastSeed minimum
  obtain ⟨guard⟩ := HasTypeStrong.initialTemplateGuardObserved henv hscoped hle earlier original lookup
    closed hTarget substitutions fits templates
    (nativeArguments.take (data.indexOffset + templates.slot))
    (captureArguments.take (data.indexOffset + templates.field)) naturalOrigin declaredOrigin
    naturalScope declaredScope (List.range (data.indexOffset + templates.slot))
    (List.range (data.indexOffset + templates.field)) cover.seed.observation cover.seed.resources
  obtain ⟨packed, pack, covered⟩ := cover.packLast
  have declaredScoped : Footprint.Scoped
      (captureArguments.take (data.indexOffset + templates.field)).length guard.declaredFootprint := by
    rw [← guard.declaredFootprint_eq]
    exact guard.guard.declaredCertificate.scoped declaredScope
  have naturalScoped : Footprint.Scoped
      (nativeArguments.take (data.indexOffset + templates.slot)).length guard.naturalFootprint := by
    rw [← guard.naturalFootprint_eq]
    exact guard.guard.naturalCertificate.scoped naturalScope
  obtain ⟨declaredLedger⟩ := guard.declaredCuts.argumentLedger guard.declaredOriginalResources declaredScoped
  obtain ⟨naturalLedger⟩ := guard.naturalCuts.argumentLedger guard.naturalOriginalResources naturalScoped
  have nativeBound := (List.getElem?_eq_some_iff.mp nativeOccurrence).1
  have nativeValue := (List.getElem?_eq_some_iff.mp nativeOccurrence).2
  have nativePrefix := naturalLedger.intoPrefix rfl (Nat.le_of_lt nativeBound)
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
  have copied := NativeArgumentLedger.cons (need := ⟨cover.seed.rank, cover.seed.demand⟩) nativeIndexBound field cover.seed.resources .nil
  exact ⟨{
    packet := ⟨index, nativeOccurrence, captureOccurrence, cover.seed, guard⟩
    bound := cover.bound
    packed := packed
    pack := pack
    covered := covered
    previous := previous
    native := nativePrefix.append copied }⟩

/-- A completed prefix of the backward capture pass, with both operational
support and its actual original-source native observation ledger. -/
structure InitialNativeCaptureRoute (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    {data : NativeRecursorData} (program : SaturatedProgram data) (witnesses : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation) (nativeArguments : List VExpr)
    (fields : Nat) (required : Footprint) where
  nativeFootprint : Footprint
  support : NativeCaptureSupport env U registry target program witnesses fields required nativeFootprint
  ledger : NativeArgumentLedger env U registry target locals σ available nativeArguments nativeFootprint

/-- Finish one index node after the preceding captures have been routed.
The guard and the ledger refer to the exact same footprint endpoints. -/
noncomputable def InitialNativeIndexPreparation.finish
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {program : SaturatedProgram data}
    {templates : NativeIndexTemplates program}
    (prepared : InitialNativeIndexPreparation env U registry target templates locals σ available
      nativeArguments captureArguments required minimum)
    (nativeValues : program.prefixArgs = nativeArguments.map (·.subst σ))
    (capturedValues : witnesses = captureArguments.map (·.subst σ))
    (previous : InitialNativeCaptureRoute env U registry target program witnesses locals σ available
      nativeArguments templates.field
      (prepared.packet.guardPacket.guard.declaredFootprint ++ externalArguments required)) :
    InitialNativeCaptureRoute env U registry target program witnesses locals σ available
      nativeArguments (templates.field + 1) required := by
  let packet := prepared.packet
  let guard : NativeIndexGuard (env := env) (U := U) (registry := registry) (target := target)
      templates (List.range (data.indexOffset + templates.slot))
      (List.range (data.indexOffset + templates.field))
      (nativeCaptureSubst (program.prefixArgs.take (data.indexOffset + templates.slot)))
      (nativeCaptureSubst (witnesses.take (data.indexOffset + templates.field)))
      (requirements packet.guardPacket.naturalFootprint)
      (requirements packet.guardPacket.declaredFootprint) packet.seed.demand := {
    naturalSupport := packet.guardPacket.guard.naturalSupport
    declaredSupport := packet.guardPacket.guard.declaredSupport
    naturalFootprint := packet.guardPacket.guard.naturalFootprint
    naturalCertificate := by
      simpa only [nativeValues, List.map_take] using packet.guardPacket.guard.naturalCertificate
    naturalResources := packet.guardPacket.guard.naturalResources
    declaredFootprint := packet.guardPacket.guard.declaredFootprint
    declaredCertificate := by
      simpa only [capturedValues, List.map_take] using packet.guardPacket.guard.declaredCertificate
    declaredResources := packet.guardPacket.guard.declaredResources
    naturalTyped := packet.guardPacket.guard.naturalTyped
    declaredTyped := packet.guardPacket.guard.declaredTyped
    alignment := by
      simpa only [nativeValues, capturedValues, List.map_take] using packet.guardPacket.guard.alignment
    declaredCode := by
      simpa only [capturedValues, List.map_take] using packet.guardPacket.guard.declaredCode }
  have naturalValue : program.prefixArgs[data.indexOffset + templates.slot]? = some (σ packet.sourceIndex) := by
    rw [nativeValues, List.getElem?_map, packet.nativeOccurrence]
    rfl
  have capturedValue : witnesses[data.indexOffset + templates.field]? = some (σ packet.sourceIndex) := by
    rw [capturedValues, List.getElem?_map, packet.captureOccurrence]
    rfl
  have previousSupport : NativeCaptureSupport env U registry target program witnesses templates.field
      (guard.declaredFootprint ++ externalArguments required) previous.nativeFootprint := by
    simpa only [guard, packet] using previous.support
  refine ⟨_, .index guard naturalValue capturedValue prepared.pack prepared.covered previousSupport, ?_⟩
  simpa only [nativeValues, List.length_map, List.append_assoc, guard, packet] using previous.ledger.append prepared.native

/-- Common original prefix variables are embedded into the full native
argument ledger; no native head theorem is used to produce their observers. -/
noncomputable def InitialNativeCaptureRoute.prefix
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {program : SaturatedProgram data}
    {nativeArguments capturePrefix : List VExpr}
    (nativeValues : program.prefixArgs = nativeArguments.map (·.subst σ))
    (prefix_eq : capturePrefix = nativeArguments.take data.indexOffset)
    (bound : data.indexOffset ≤ nativeArguments.length)
    (ledger : NativeArgumentLedger env U registry target locals σ available capturePrefix required) :
    InitialNativeCaptureRoute env U registry target program witnesses locals σ available
      nativeArguments 0 required := by
  refine ⟨_, .prefix required, ?_⟩
  simpa only [nativeValues, List.length_map] using ledger.intoPrefix prefix_eq bound

/-- A proof field retains its actual collected source seed. Its pack is
proved empty from ORIGINAL proposition typing, while the predecessor keeps
every outside requirement in its original order. -/
structure InitialNativeProofPreparation (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    {data : NativeRecursorData} (program : SaturatedProgram data) (witnesses : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation) (captureArguments : List VExpr)
    (field : Nat) (argument : VExpr) (required : Footprint) (minimum : Nat) where
  cover : NativeSeedCover env U registry target locals σ available argument
    (argumentNeeds required 0) minimum
  domain : VExpr
  instruction : program.instructions[field]? = some (.proof domain)
  captured : witnesses[data.indexOffset + field]? = some (argument.subst σ)
  sourceProof : env.HasType U
    (((program.equationBody.domains.take (data.indexOffset + field)).map
      (·.instL program.levels)).reverse) domain (.sort .zero)
  domainProof : env.HasType U target
    (domain.subst (nativeCaptureSubst (witnesses.take (data.indexOffset + field)))) (.sort .zero)
  inhabitant : env.HasType U target (argument.subst σ)
    (domain.subst (nativeCaptureSubst (witnesses.take (data.indexOffset + field))))
  pack : BinderPack cover.seed.rank .empty required (externalArguments required)
  previous : NativeArgumentLedger env U registry target locals σ available
    (captureArguments.take (data.indexOffset + field)) (externalArguments required)

/-- The target proof and its formation are substitutions of retained
original evidence. There is no new target proof-classification premise. -/
theorem NativeArgumentLedger.prepareProof
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {data : NativeRecursorData} {program : SaturatedProgram data}
    {witnesses captureArguments : List VExpr} {field : Nat} {argument proposition domain : VExpr}
    (instruction : program.instructions[field]? = some (.proof domain))
    (captureOccurrence : captureArguments[data.indexOffset + field]? = some argument)
    (capturedValues : witnesses = captureArguments.map (·.subst σ))
    (originalProposition : OriginalTypePayload sourceEnv env U registry source proposition (.sort .zero))
    (originalArgument : OriginalTypePayload sourceEnv env U registry source argument proposition)
    (sourceProof : sourceEnv.IsDefEqStrong U
      (((program.equationBody.domains.take (data.indexOffset + field)).map
        (·.instL program.levels)).reverse) domain domain (.sort .zero))
    (propositionOrigin : proposition = domain.instOuter
      (captureArguments.take (data.indexOffset + field)))
    (domainScope : domain.ClosedN (captureArguments.take (data.indexOffset + field)).length)
    {required : Footprint}
    (ledger : NativeArgumentLedger env U registry target locals σ available
      (captureArguments.take (data.indexOffset + field + 1)) required)
    (minimum : Nat) :
    Nonempty (InitialNativeProofPreparation env U registry target program witnesses locals σ available
      captureArguments field argument required minimum) := by
  have captureNext : captureArguments.take (data.indexOffset + field + 1) =
      captureArguments.take (data.indexOffset + field) ++ [argument] := by
    rw [List.take_add_one, captureOccurrence]
    rfl
  have current := captureNext ▸ ledger
  obtain ⟨cover⟩ := current.lastSeed minimum
  obtain ⟨outside, pack⟩ := cover.proofPack originalProposition originalArgument closed hTarget substitutions fits
  have outside_eq := BinderPack.externalArguments pack
  subst outside
  have domainRealized : proposition.subst σ =
      domain.subst (nativeCaptureSubst (witnesses.take (data.indexOffset + field))) := by
    rw [propositionOrigin, capturedValues, ← List.map_take]
    exact realized_template domainScope σ
  have domainProof := (originalProposition.1.defeq.mono hle).substDF henv substitutions.wf hTarget substitutions
  have inhabitant := (originalArgument.1.defeq.mono hle).substDF henv substitutions.wf hTarget substitutions
  have captured : witnesses[data.indexOffset + field]? = some (argument.subst σ) := by
    rw [capturedValues, List.getElem?_map, captureOccurrence]
    rfl
  exact ⟨⟨cover, domain, instruction, captured, sourceProof.defeq.mono hle,
    by simpa only [domainRealized, VExpr.subst] using domainProof.hasType.1,
    domainRealized ▸ inhabitant, pack, current.withoutLast⟩⟩

/-- A proof node contributes no native argument demand. Its actual source
requirements have already been retained in the preceding capture ledger. -/
noncomputable def InitialNativeProofPreparation.finish
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (prepared : InitialNativeProofPreparation env U registry target program witnesses locals σ available
      captureArguments field argument required minimum)
    (previous : InitialNativeCaptureRoute env U registry target program witnesses locals σ available
      nativeArguments field (externalArguments required)) :
    InitialNativeCaptureRoute env U registry target program witnesses locals σ available
      nativeArguments (field + 1) required :=
  ⟨previous.nativeFootprint,
    .proof prepared.instruction prepared.captured prepared.sourceProof prepared.domainProof
      prepared.inhabitant prepared.pack previous.support,
    previous.ledger⟩

end Lean4Lean.AnchoredSource.Adapted
