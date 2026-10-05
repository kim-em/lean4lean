import Lean4Lean.Theory.Typing.AnchoredConstructorHeader
import Lean4Lean.Theory.Typing.AnchoredFamilyHeader
import Lean4Lean.Theory.Typing.AnchoredNativeDeclarationOrigin
import Lean4Lean.Theory.Typing.NativeRegistryPrefix
import Lean4Lean.Theory.Typing.AnchoredBoundedConversion
import Lean4Lean.Theory.Typing.AnchoredBoundedVariable
import Lean4Lean.Theory.Typing.AnchoredDefinitionTransfer
import Lean4Lean.Theory.Typing.DefinitionRegistryPrefix

/-! The native constant rule in the ORIGINAL current declaration header.
The actual registry continuation excludes later heads. Old entries use the
earlier history's completed header theorem; current entries use strictly less
observer fuel in this same header. All source observation closures are handled
at unchanged fuel. This is a stage-induction step, not an assumed native rule.
-/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

def blockCurrent (block : VInductBlock) (name : Name) : Bool :=
  block.recursors.any (fun value => value.name == name)

section
variable {base installed env : VEnv} {declarations finalDeclarations : List VDecl}
  {old : Name → Option NativeRecursorData} {source expanded : VInductDecl}
  {block : VInductBlock} {signature : InductiveSignature} {generated : Instance signature}
  {auxiliaries : List ContainerSpecialization} {key : Name}
  {U : Nat} {registry : CanonicalHead.Registry}
  (previous : NativeRegistryHistory base declarations old)
  (original : source.WF base) (compiled : source.CompilesTo base block)
  (formed : block.WF base) (installation : block.install base = some installed)
  (compilation : CompilationData base source expanded signature generated auxiliaries block)
  (specializations : CertifiedSpecializations base auxiliaries)
  (stages : VInductBlock.TypingStages base block installed)
  {last : NativeRegistryHistory env finalDeclarations registry.natives}
  (continuation : NativeRegistryHistory.Prefix
    (.native previous original compiled formed installation compilation specializations .rfl (key := key)) last)

/-- The previous-history induction hypothesis retains its own concrete origin
and local control filter. There is no native semantic conclusion in this
premise: it is the earlier ORIGINAL Strong theorem at every local fuel. -/
def PreviousHeaders : Prop :=
  ∀ name data, old name = some data →
    ∃ origin : NativeDeclarationOrigin base declarations data,
      ∀ fuel, ∀ {Γ l r A}, origin.stage.typing.recursors.IsDefEqStrong U Γ l r A →
        Joint origin.current fuel env U registry Γ l r A

/-- Previously completed definition headers are indexed by the literal finite
history table, with their original header/body proof trees retained. -/
def PreviousDefinitions : Prop :=
  ∀ name value, definitionRegistry declarations name = some value →
    ∃ origin : DefinitionDeclarationOrigin base declarations value,
      ∀ fuel, ∀ {Γ l r A}, origin.stage.header.IsDefEqStrong U Γ l r A →
        Joint origin.current fuel env U registry Γ l r A

include previous original compiled formed installation compilation specializations stages in
/-- Once the current HEADER theorem has been proved by fuel induction, install
its entry into the cumulative earlier-header hypothesis for the next stage.
Installing equations does not claim same-fuel semantics for those equations. -/
theorem PreviousHeaders.installNative
    (oldHeaders : PreviousHeaders (old := old) (base := base) (declarations := declarations)
      (env := env) (U := U) (registry := registry))
    (header : ∀ fuel, ∀ {Γ l r A}, stages.recursors.IsDefEqStrong U Γ l r A →
      Joint (blockCurrent block) fuel env U registry Γ l r A) :
    PreviousHeaders (old := installEntries old (compilationEntries key source signature auxiliaries generated))
      (base := installed) (declarations := .induct source :: declarations)
      (env := env) (U := U) (registry := registry) := by
  intro name data lookup
  unfold installEntries at lookup
  cases found : (compilationEntries key source signature auxiliaries generated).find?
      (fun value => value.name == name) with
  | none =>
    obtain ⟨origin, earlier⟩ := oldHeaders name data (by simpa only [found, Option.orElse_none] using lookup)
    exact ⟨origin.later (.induct original (.intro original compiled formed installation)), earlier⟩
  | some selected =>
    simp only [found, Option.orElse_some, Option.some.injEq] at lookup
    subst selected
    let here : NativeDeclarationOrigin installed (.induct source :: declarations) data := {
      source := source
      stage := ⟨base, installed, block, declarations, previous.history,
        Nat.lt_succ_self _, original, compiled, stages, .rfl⟩
      laterDeclarations := []
      declarations_eq := rfl
      expanded := expanded
      signature := signature
      generated := generated
      auxiliaries := auxiliaries
      key := key
      compilationBase := base
      compilationBelow := .rfl
      compilation := compilation
      specializations := specializations
      entry := List.mem_of_find?_eq_some found }
    exact ⟨here, header⟩

include compilation in
private theorem current_entry (entry : data ∈ compilationEntries key source signature auxiliaries generated) :
    blockCurrent block data.name = true := by
  have names := compilation.nativeEntries_names (key := key)
  have member : data.name ∈ block.recursors.map (·.name) := by
    rw [← names]
    exact List.mem_map.mpr ⟨data, entry, rfl⟩
  obtain ⟨value, member, same⟩ := List.mem_map.mp member
  exact List.any_eq_true.mpr ⟨value, member, by simpa only [beq_iff_eq] using same⟩

include previous original compiled formed installation compilation specializations stages continuation in
/-- This leaf performs the actual stage/fuel split. The two original header
proof roots are recovered from concrete compilation membership in both cases. -/
theorem Obs.headerNative
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (oldHeaders : PreviousHeaders (old := old) (base := base) (declarations := declarations)
      (env := env) (U := U) (registry := registry))
    {fuel : Nat}
    (smaller : ∀ lower, lower < fuel → ∀ {Γ l r A}, stages.recursors.IsDefEqStrong U Γ l r A →
      Joint (blockCurrent block) lower env U registry Γ l r A)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {data : NativeRecursorData} {name : Name} {ci : VConstant}
    (constant : stages.recursors.constants name = some ci)
    {seedLevels levels levels' : List VLevel}
    (lookup : registry.natives name = some data)
    (notDefinition : registry.definitions name = none)
    (nameEq : data.name = name) (registered : NativeRecursorRegistered env data)
    (seedWF : ∀ level ∈ seedLevels, level.WF U)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (rightWF : ∀ level ∈ levels', level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
    (rightEquivalent : List.Forall₂ (· ≈ ·) levels levels')
    (packet : NativeConstantSignature data seedLevels) (typeClosed : packet.type.Closed)
    {demand support : Profile n} {typeRealization : Subst}
    (certificate : CodeCert env U registry target [] typeRealization
      (packet.type.instL seedLevels) support []) (typed : demand.HasType support)
    (plan : Adapted.NativePlan env U registry target packet [] demand [])
    (bound : max (plan.nativeDepth (blockCurrent block)) (certificate.nativeDepth (blockCurrent block)) +
      (if blockCurrent block name then 1 else 0) ≤ fuel) :
    Nonempty (Result (blockCurrent block) fuel env U registry target locals σ τ available
      (.const name levels) (.const name levels') (ci.type.instL levels) demand) := by
  have headerBelow : stages.recursors ≤ env := stages.recursors_le.trans continuation.le
  have selectedType := registered.recursorType packet.typeOrigin
  rw [nameEq, headerBelow.constants constant] at selectedType
  have typeEq : packet.type = ci.type :=
    (congrArg VConstant.type (Option.some.inj selectedType)).symm
  have selected := continuation.previous_lookup (stages.recursors_le.constants constant) lookup
  unfold installEntries at selected
  cases found : (compilationEntries key source signature auxiliaries generated).find?
      (fun value => value.name == name) with
  | none =>
    have priorLookup : old name = some data := by simpa only [found, Option.orElse_none] using selected
    obtain ⟨oldOrigin, earlier⟩ := oldHeaders name data priorLookup
    let completedOrigin := oldOrigin.later
      (VDecl.WF.induct original (.intro original compiled formed installation))
    let finalOrigin := continuation.origin completedOrigin
    have earlier' : ∀ localFuel, ∀ {Γ l r A}, finalOrigin.stage.typing.recursors.IsDefEqStrong U Γ l r A →
        Joint finalOrigin.current localFuel env U registry Γ l r A := earlier
    have budget : Budgeted.Within [(blockCurrent block, fuel)] (fun filter =>
        max (plan.nativeDepth filter) (certificate.nativeDepth filter) + if filter name then 1 else 0) := by
      intro filter limit member
      cases List.mem_singleton.mp member
      exact bound
    obtain ⟨result⟩ := Budgeted.Obs.nativeAtOrigin finalOrigin henv hscoped earlier' hTarget
      lookup notDefinition nameEq seedWF levelsWF rightWF equivalent rightEquivalent
      packet typeClosed certificate typed plan budget
    exact ⟨by simpa only [typeEq] using result.toStaged (List.mem_singleton_self _)⟩
  | some selectedData =>
    simp only [found, Option.orElse_some, Option.some.injEq] at selected
    subst selectedData
    have member := List.mem_of_find?_eq_some found
    have counted := current_entry compilation member
    rw [nameEq] at counted
    have lower : max (plan.nativeDepth (blockCurrent block)) (certificate.nativeDepth (blockCurrent block)) < fuel := by
      rw [counted] at bound
      simp only [↓reduceIte] at bound
      omega
    let here : NativeDeclarationOrigin installed (.induct source :: declarations) data := {
      source := source
      stage := ⟨base, installed, block, declarations, previous.history,
        Nat.lt_succ_self _, original, compiled, stages, .rfl⟩
      laterDeclarations := []
      declarations_eq := rfl
      expanded := expanded
      signature := signature
      generated := generated
      auxiliaries := auxiliaries
      key := key
      compilationBase := base
      compilationBelow := .rfl
      compilation := compilation
      specializations := specializations
      entry := member }
    obtain ⟨typeLevel, typeFormation⟩ := here.signatureFormation seedWF packet
    obtain ⟨result⟩ := Obs.nativeTransfer henv hscoped stages.recursorsWF.ordered headerBelow
      (smaller _ lower) hTarget lookup notDefinition nameEq registered seedWF levelsWF rightWF
      equivalent rightEquivalent packet typeClosed typeFormation
      (fun _ selected => here.singletonOriginal seedWF selected) certificate typed plan
      (Nat.le_max_left _ _) (Nat.le_max_right _ _) bound
    exact ⟨by simpa only [typeEq] using result⟩

include previous original compiled formed installation compilation specializations stages continuation in
/-- Registered definitions used in this native header belong to the actual
previous history; later definition installations cannot supply this leaf. -/
theorem Obs.headerDefinition
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (oldDefinitions : PreviousDefinitions (base := base) (declarations := declarations)
      (env := env) (U := U) (registry := registry))
    {fuel : Nat} {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {value : VDefVal} {name : Name} {ci : VConstant}
    (constant : stages.recursors.constants name = some ci)
    {seedLevels levels levels' : List VLevel}
    (lookup : registry.definitions name = some value)
    (nameEq : value.name = name) (registered : DefinitionRegistered env value)
    (seedWF : ∀ level ∈ seedLevels, level.WF U)
    (seedLength : seedLevels.length = value.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (rightWF : ∀ level ∈ levels', level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
    (rightEquivalent : List.Forall₂ (· ≈ ·) levels levels')
    (bodyClosed : value.value.Closed) (typeClosed : value.type.Closed)
    {atom : Atom n} {support : Profile n} {typeRealization bodyRealization : Subst}
    (certificate : CodeCert env U registry target [] typeRealization
      (value.type.instL seedLevels) support [])
    (typed : (Profile.singleton atom).HasType support)
    (body : Obs env U registry target [] bodyRealization
      (value.value.instL seedLevels) (.singleton atom) [])
    (bound : max (body.nativeDepth (blockCurrent block)) (certificate.nativeDepth (blockCurrent block)) +
      (if blockCurrent block name then 1 else 0) ≤ fuel) :
    Nonempty (Result (blockCurrent block) fuel env U registry target locals σ τ available
      (.const name levels) (.const name levels') (ci.type.instL levels) (.singleton atom)) := by
  have headerBelow : stages.recursors ≤ env := stages.recursors_le.trans continuation.le
  have selectedType := registered.1
  rw [nameEq, headerBelow.constants constant] at selectedType
  have typeEq : value.type = ci.type :=
    (congrArg VConstant.type (Option.some.inj selectedType)).symm
  have finalLookup := last.history.definitionLookup registered
  rw [nameEq] at finalLookup
  have priorLookup : definitionRegistry declarations name = some value :=
    continuation.previous_definition (stages.recursors_le.constants constant) finalLookup
  obtain ⟨oldOrigin, earlier⟩ := oldDefinitions name value priorLookup
  let finalOrigin := oldOrigin.metadata (stages.base_le_recursors.trans headerBelow)
  have earlier' : ∀ localFuel, ∀ {Γ l r A}, finalOrigin.stage.header.IsDefEqStrong U Γ l r A →
      Joint finalOrigin.current localFuel env U registry Γ l r A := earlier
  have budget : Budgeted.Within [(blockCurrent block, fuel)] (fun filter =>
      max (body.nativeDepth filter) (certificate.nativeDepth filter) + if filter name then 1 else 0) := by
    intro filter limit member
    cases List.mem_singleton.mp member
    exact bound
  obtain ⟨result⟩ := Budgeted.Obs.deltaAtOrigin finalOrigin henv hscoped earlier' hTarget
    lookup nameEq registered seedWF seedLength levelsWF rightWF equivalent rightEquivalent
    bodyClosed typeClosed certificate typed body budget
  exact ⟨by simpa only [typeEq] using result.toStaged (List.mem_singleton_self _)⟩

include previous original compiled formed installation compilation specializations stages continuation in
/-- Constant transfer consumes every permitted observation closure. Only the
native leaf invokes stage induction; reconstructed views and raised results
are handled by the already checked same-bound closure laws. -/
theorem Obs.headerConstTransfer
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (oldHeaders : PreviousHeaders (old := old) (base := base) (declarations := declarations)
      (env := env) (U := U) (registry := registry))
    (oldDefinitions : PreviousDefinitions (base := base) (declarations := declarations)
      (env := env) (U := U) (registry := registry))
    (constantHeaders : OriginalConstantHeaders stages.recursors env U registry)
    {fuel : Nat}
    (smaller : ∀ lower, lower < fuel → ∀ {Γ l r A}, stages.recursors.IsDefEqStrong U Γ l r A →
      Joint (blockCurrent block) lower env U registry Γ l r A)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {name : Name} {ci : VConstant} (constant : stages.recursors.constants name = some ci)
    {levels levels' : List VLevel}
    (rightWF : ∀ level ∈ levels', level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) levels levels')
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ (.const name levels) demand footprint)
    (bound : observation.nativeDepth (blockCurrent block) ≤ fuel)
    (resources : footprint.Available available) :
    Nonempty (Result (blockCurrent block) fuel env U registry target locals σ τ available
      (.const name levels) (.const name levels') (ci.type.instL levels) demand) := by
  match observation with
  | .delta lookup nameEq registered seedWF seedLength levelsWF seedEq bodyClosed typeClosed certificate typed body =>
    exact Obs.headerDefinition previous original compiled formed installation compilation specializations stages continuation
      henv hscoped oldDefinitions hTarget constant lookup nameEq registered seedWF seedLength levelsWF rightWF
      seedEq equivalent bodyClosed typeClosed certificate typed body (by simpa only [Obs.nativeDepth] using bound)
  | .native lookup notDefinition nameEq registered seedWF levelsWF seedEq packet typeClosed certificate typed plan =>
    exact Obs.headerNative previous original compiled formed installation compilation specializations stages continuation
      henv hscoped oldHeaders smaller hTarget constant lookup notDefinition nameEq registered seedWF levelsWF rightWF
      seedEq equivalent packet typeClosed certificate typed plan (by simpa only [Obs.nativeDepth] using bound)
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF seedEq signature typeClosed certificate typed plan =>
    have below : stages.recursors ≤ env := stages.recursors_le.trans continuation.le
    have same := Option.some.inj (lookup.symm.trans (below.constants constant))
    cases same
    exact Obs.familyAtHeader henv hscoped below constantHeaders hTarget constant
      noDefinition noNative noQuotient seedLength seedWF levelsWF rightWF seedEq equivalent
      signature typeClosed certificate typed plan (by simpa only [Obs.nativeDepth] using bound)
  | .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF seedEq signature typeClosed certificate typed plan =>
    have below : stages.recursors ≤ env := stages.recursors_le.trans continuation.le
    have same := Option.some.inj (lookup.symm.trans (below.constants constant))
    cases same
    exact Obs.constructorAtHeader henv hscoped below constantHeaders hTarget constant
      noDefinition noNative noQuotient seedLength seedWF levelsWF rightWF seedEq equivalent
      signature typeClosed certificate typed plan (by simpa only [Obs.nativeDepth] using bound)
  | .empty => exact ⟨.empty⟩
  | .union left right =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth] using bound)
    obtain ⟨a⟩ := Obs.headerConstTransfer
      henv hscoped oldHeaders oldDefinitions constantHeaders smaller hTarget constant rightWF equivalent left bounds.1
      (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨b⟩ := Obs.headerConstTransfer
      henv hscoped oldHeaders oldDefinitions constantHeaders smaller hTarget constant rightWF equivalent right bounds.2
      (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    obtain ⟨result⟩ := Obs.headerConstTransfer
      henv hscoped oldHeaders oldDefinitions constantHeaders smaller hTarget constant rightWF equivalent source (by simpa only [Obs.nativeDepth] using bound) resources
    exact ⟨result.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨result⟩ := Obs.headerConstTransfer
      henv hscoped oldHeaders oldDefinitions constantHeaders smaller hTarget constant rightWF equivalent source (by simpa only [Obs.nativeDepth] using bound) resources
    exact ⟨result.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨result⟩ := Obs.headerConstTransfer
      henv hscoped oldHeaders oldDefinitions constantHeaders smaller hTarget constant rightWF equivalent source (by simpa only [Obs.nativeDepth] using bound) resources
    exact ⟨result.unpad⟩
  | .rowShift source =>
    obtain ⟨result⟩ := Obs.headerConstTransfer
      henv hscoped oldHeaders oldDefinitions constantHeaders smaller hTarget constant rightWF equivalent source (by simpa only [Obs.nativeDepth] using bound) resources
    exact ⟨(result.pad henv hscoped hTarget).view henv hscoped hTarget (.commutePadFn _ _)⟩
termination_by sizeOf observation

include previous original compiled formed installation compilation specializations stages continuation in
/-- The full original `Strong.constDF` semantic case at a current header.
The backward direction uses its ORIGINAL source type-equality child. -/
theorem Joint.headerConstDF
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (oldHeaders : PreviousHeaders (old := old) (base := base) (declarations := declarations)
      (env := env) (U := U) (registry := registry))
    (oldDefinitions : PreviousDefinitions (base := base) (declarations := declarations)
      (env := env) (U := U) (registry := registry))
    (constantHeaders : OriginalConstantHeaders stages.recursors env U registry)
    {fuel : Nat}
    (smaller : ∀ lower, lower < fuel → ∀ {Γ l r A}, stages.recursors.IsDefEqStrong U Γ l r A →
      Joint (blockCurrent block) lower env U registry Γ l r A)
    {Γ : List VExpr} {name : Name} {ci : VConstant}
    (constant : stages.recursors.constants name = some ci)
    {levels levels' : List VLevel}
    (leftWF : ∀ level ∈ levels, level.WF U)
    (rightWF : ∀ level ∈ levels', level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) levels levels')
    (originalType : Joint (blockCurrent block) fuel env U registry Γ
      (ci.type.instL levels) (ci.type.instL levels') (.sort typeLevel)) :
    Joint (blockCurrent block) fuel env U registry Γ
      (.const name levels) (.const name levels') (ci.type.instL levels) := by
  apply Joint.of_transfers henv
  intro target locals σ τ available closed hTarget substitutions fits
  constructor
  · intro n demand footprint observation bound resources
    exact Obs.headerConstTransfer previous original compiled formed installation compilation specializations stages continuation
      henv hscoped oldHeaders oldDefinitions constantHeaders smaller hTarget constant rightWF equivalent observation bound resources
  · apply Transfer.convert henv hscoped originalType.symm closed hTarget substitutions fits
    intro n demand footprint observation bound resources
    exact Obs.headerConstTransfer previous original compiled formed installation compilation specializations stages continuation
      henv hscoped oldHeaders oldDefinitions constantHeaders smaller hTarget constant leftWF (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip equivalent)) observation bound resources

end
end Lean4Lean.AnchoredSource.Adapted.Staged
