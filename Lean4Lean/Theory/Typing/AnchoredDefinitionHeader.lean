import Lean4Lean.Theory.Typing.AnchoredHeaderConstant
import Lean4Lean.Theory.Typing.DefinitionStageSelection

/-! The constant case in an actual transparent-definition header. A current
mutual member spends one unit of observer fuel before interpreting its original
body; old definitions and natives use their own completed earlier headers. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

def definitionCurrent (values : List VDefVal) (name : Name) : Bool :=
  values.any (fun value => value.name == name)

section
variable {base installed env : VEnv} {declarations finalDeclarations : List VDecl}
  {old : Name → Option NativeRecursorData} {declaration : VDecl} {representative : VDefVal}
  {U : Nat} {registry : CanonicalHead.Registry}
  (previous : NativeRegistryHistory base declarations old)
  (stage : DefinitionTypingStage base declaration installed representative)
  {last : NativeRegistryHistory env finalDeclarations registry.natives}
  (continuation : NativeRegistryHistory.Prefix (.decl previous stage.declarationWF) last)

include previous stage in
/-- Installation adds the current completed header roots to the finite-history
hypothesis. No installed-equation semantic theorem is assumed or concluded. -/
theorem PreviousDefinitions.installDefinition
    (oldDefinitions : PreviousDefinitions (base := base) (declarations := declarations)
      (env := env) (U := U) (registry := registry))
    (header : ∀ fuel, ∀ {Γ l r A}, stage.header.IsDefEqStrong U Γ l r A →
      Joint (definitionCurrent stage.values) fuel env U registry Γ l r A) :
    PreviousDefinitions (base := installed) (declarations := declaration :: declarations)
      (env := env) (U := U) (registry := registry) := by
  intro name value lookup
  change installDefinitions (definitionRegistry declarations) declaration.definitionEntries name = some value at lookup
  rw [← stage.entries] at lookup
  unfold installDefinitions at lookup
  cases found : stage.values.find? (fun entry => entry.name == name) with
  | none =>
    obtain ⟨origin, earlier⟩ := oldDefinitions name value (by simpa only [found, Option.orElse_none] using lookup)
    exact ⟨origin.later stage.declarationWF, earlier⟩
  | some selected =>
    simp only [found, Option.orElse_some, Option.some.injEq] at lookup
    subst selected
    let here : DefinitionDeclarationOrigin installed (declaration :: declarations) value := {
      base := base
      installed := installed
      earlierDeclarations := declarations
      history := previous.history
      declaration := declaration
      stage := stage.select (List.mem_of_find?_eq_some found)
      laterDeclarations := []
      declarations_eq := rfl
      installedBelow := .rfl }
    refine ⟨here, ?_⟩
    have currentEq : here.current = definitionCurrent stage.values := by
      funext name
      simp only [here, DefinitionDeclarationOrigin.current,
        DefinitionTypingStage.select_values, definitionCurrent]
    intro fuel Γ l r A proof
    rw [currentEq]
    exact header fuel (by simpa only [here, DefinitionTypingStage.select_header] using proof)

include stage in
theorem PreviousHeaders.installDefinition
    (oldHeaders : PreviousHeaders (base := base) (declarations := declarations) (old := old)
      (env := env) (U := U) (registry := registry)) :
    PreviousHeaders (base := installed) (declarations := declaration :: declarations) (old := old)
      (env := env) (U := U) (registry := registry) := by
  intro name data lookup
  obtain ⟨origin, earlier⟩ := oldHeaders name data lookup
  exact ⟨origin.later stage.declarationWF, earlier⟩

include previous stage continuation in
theorem Obs.definitionHeaderDelta
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (oldDefinitions : PreviousDefinitions (base := base) (declarations := declarations)
      (env := env) (U := U) (registry := registry))
    {fuel : Nat}
    (smaller : ∀ lower, lower < fuel → ∀ {Γ l r A}, stage.header.IsDefEqStrong U Γ l r A →
      Joint (definitionCurrent stage.values) lower env U registry Γ l r A)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {value : VDefVal} {name : Name} {ci : VConstant}
    (constant : stage.header.constants name = some ci)
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
    (bound : max (body.nativeDepth (definitionCurrent stage.values))
      (certificate.nativeDepth (definitionCurrent stage.values)) +
      (if definitionCurrent stage.values name then 1 else 0) ≤ fuel) :
    Nonempty (Result (definitionCurrent stage.values) fuel env U registry target locals σ τ available
      (.const name levels) (.const name levels') (ci.type.instL levels) (.singleton atom)) := by
  have headerBelow : stage.header ≤ env := stage.header_le.trans continuation.le
  have selectedType := registered.1
  rw [nameEq, headerBelow.constants constant] at selectedType
  have typeEq : value.type = ci.type :=
    (congrArg VConstant.type (Option.some.inj selectedType)).symm
  have finalLookup := last.history.definitionLookup registered
  rw [nameEq] at finalLookup
  have selected := continuation.previous_definition (stage.header_le.constants constant) finalLookup
  change installDefinitions (definitionRegistry declarations) declaration.definitionEntries name = some value at selected
  rw [← stage.entries] at selected
  unfold installDefinitions at selected
  have budget : Budgeted.Within [(definitionCurrent stage.values, fuel)] (fun filter =>
      max (body.nativeDepth filter) (certificate.nativeDepth filter) + if filter name then 1 else 0) := by
    intro filter limit member
    cases List.mem_singleton.mp member
    exact bound
  cases found : stage.values.find? (fun entry => entry.name == name) with
  | none =>
    have prior : definitionRegistry declarations name = some value := by
      simpa only [found, Option.orElse_none] using selected
    obtain ⟨oldOrigin, earlier⟩ := oldDefinitions name value prior
    let finalOrigin := oldOrigin.metadata ((VEnv.addConsts_le stage.headers).trans headerBelow)
    have earlier' : ∀ localFuel, ∀ {Γ l r A}, finalOrigin.stage.header.IsDefEqStrong U Γ l r A →
        Joint finalOrigin.current localFuel env U registry Γ l r A := earlier
    obtain ⟨result⟩ := Budgeted.Obs.deltaAtOrigin finalOrigin henv hscoped earlier' hTarget
      lookup nameEq registered seedWF seedLength levelsWF rightWF equivalent rightEquivalent
      bodyClosed typeClosed certificate typed body budget
    exact ⟨by simpa only [typeEq] using result.toStaged (List.mem_singleton_self _)⟩
  | some selectedValue =>
    simp only [found, Option.orElse_some, Option.some.injEq] at selected
    subst selectedValue
    have member := List.mem_of_find?_eq_some found
    have counted : definitionCurrent stage.values name = true :=
      List.any_eq_true.mpr ⟨value, member, by simpa only [beq_iff_eq] using nameEq⟩
    have lower : max (body.nativeDepth (definitionCurrent stage.values))
        (certificate.nativeDepth (definitionCurrent stage.values)) < fuel := by
      rw [counted] at bound
      simp only [↓reduceIte] at bound
      omega
    let here : DefinitionDeclarationOrigin env (declaration :: declarations) value := {
      base := base
      installed := installed
      earlierDeclarations := declarations
      history := previous.history
      declaration := declaration
      stage := stage.select member
      laterDeclarations := []
      declarations_eq := rfl
      installedBelow := continuation.le }
    have earlier : ∀ {Γ l r A}, here.stage.header.IsDefEqStrong U Γ l r A →
        Joint (definitionCurrent stage.values)
          (max (body.nativeDepth (definitionCurrent stage.values))
            (certificate.nativeDepth (definitionCurrent stage.values))) env U registry Γ l r A := by
      intro Γ l r A proof
      exact smaller _ lower (by simpa only [here, DefinitionTypingStage.select_header] using proof)
    obtain ⟨result⟩ := Budgeted.Obs.deltaTransfer here henv hscoped earlier hTarget
      lookup nameEq registered seedWF seedLength levelsWF rightWF equivalent rightEquivalent
      bodyClosed typeClosed certificate typed body (Nat.le_max_left _ _) (Nat.le_max_right _ _) budget
    exact ⟨by simpa only [typeEq] using result.toStaged (List.mem_singleton_self _)⟩

include previous stage continuation in
theorem Obs.definitionHeaderNative
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (oldHeaders : PreviousHeaders (old := old) (base := base) (declarations := declarations)
      (env := env) (U := U) (registry := registry))
    {fuel : Nat} {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {data : NativeRecursorData} {name : Name} {ci : VConstant}
    (constant : stage.header.constants name = some ci)
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
    (bound : max (plan.nativeDepth (definitionCurrent stage.values)) (certificate.nativeDepth (definitionCurrent stage.values)) +
      (if definitionCurrent stage.values name then 1 else 0) ≤ fuel) :
    Nonempty (Result (definitionCurrent stage.values) fuel env U registry target locals σ τ available
      (.const name levels) (.const name levels') (ci.type.instL levels) demand) := by
  have headerBelow : stage.header ≤ env := stage.header_le.trans continuation.le
  have selectedType := registered.recursorType packet.typeOrigin
  rw [nameEq, headerBelow.constants constant] at selectedType
  have typeEq : packet.type = ci.type :=
    (congrArg VConstant.type (Option.some.inj selectedType)).symm
  have priorLookup : old name = some data :=
    continuation.previous_lookup (stage.header_le.constants constant) lookup
  obtain ⟨oldOrigin, earlier⟩ := oldHeaders name data priorLookup
  let finalOrigin := continuation.origin (oldOrigin.later stage.declarationWF)
  have earlier' : ∀ localFuel, ∀ {Γ l r A}, finalOrigin.stage.typing.recursors.IsDefEqStrong U Γ l r A →
      Joint finalOrigin.current localFuel env U registry Γ l r A := earlier
  have budget : Budgeted.Within [(definitionCurrent stage.values, fuel)] (fun filter =>
      max (plan.nativeDepth filter) (certificate.nativeDepth filter) + if filter name then 1 else 0) := by
    intro filter limit member
    cases List.mem_singleton.mp member
    exact bound
  obtain ⟨result⟩ := Budgeted.Obs.nativeAtOrigin finalOrigin henv hscoped earlier' hTarget
    lookup notDefinition nameEq seedWF levelsWF rightWF equivalent rightEquivalent
    packet typeClosed certificate typed plan budget
  exact ⟨by simpa only [typeEq] using result.toStaged (List.mem_singleton_self _)⟩

include previous stage continuation in
/-- Constant transfer consumes every permitted observation closure. Current definition leaves spend strictly smaller fuel; old heads invoke
the actual earlier declaration header; reconstructed views and raised results
are handled by the already checked same-bound closure laws. -/
theorem Obs.definitionHeaderConstTransfer
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (oldHeaders : PreviousHeaders (old := old) (base := base) (declarations := declarations)
      (env := env) (U := U) (registry := registry))
    (oldDefinitions : PreviousDefinitions (base := base) (declarations := declarations)
      (env := env) (U := U) (registry := registry))
    (constantHeaders : OriginalConstantHeaders stage.header env U registry)
    {fuel : Nat}
    (smaller : ∀ lower, lower < fuel → ∀ {Γ l r A}, stage.header.IsDefEqStrong U Γ l r A →
      Joint (definitionCurrent stage.values) lower env U registry Γ l r A)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {name : Name} {ci : VConstant} (constant : stage.header.constants name = some ci)
    {levels levels' : List VLevel}
    (rightWF : ∀ level ∈ levels', level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) levels levels')
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ (.const name levels) demand footprint)
    (bound : observation.nativeDepth (definitionCurrent stage.values) ≤ fuel)
    (resources : footprint.Available available) :
    Nonempty (Result (definitionCurrent stage.values) fuel env U registry target locals σ τ available
      (.const name levels) (.const name levels') (ci.type.instL levels) demand) := by
  match observation with
  | .delta lookup nameEq registered seedWF seedLength levelsWF seedEq bodyClosed typeClosed certificate typed body =>
    exact Obs.definitionHeaderDelta previous stage continuation
      henv hscoped oldDefinitions smaller hTarget constant lookup nameEq registered seedWF seedLength levelsWF rightWF
      seedEq equivalent bodyClosed typeClosed certificate typed body (by simpa only [Obs.nativeDepth] using bound)
  | .native lookup notDefinition nameEq registered seedWF levelsWF seedEq packet typeClosed certificate typed plan =>
    exact Obs.definitionHeaderNative previous stage continuation
      henv hscoped oldHeaders hTarget constant lookup notDefinition nameEq registered seedWF levelsWF rightWF
      seedEq equivalent packet typeClosed certificate typed plan (by simpa only [Obs.nativeDepth] using bound)
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF seedEq signature typeClosed certificate typed plan =>
    have below : stage.header ≤ env := stage.header_le.trans continuation.le
    have same := Option.some.inj (lookup.symm.trans (below.constants constant))
    cases same
    exact Obs.familyAtHeader henv hscoped below constantHeaders hTarget constant
      noDefinition noNative noQuotient seedLength seedWF levelsWF rightWF seedEq equivalent
      signature typeClosed certificate typed plan (by simpa only [Obs.nativeDepth] using bound)
  | .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF seedEq signature typeClosed certificate typed plan =>
    have below : stage.header ≤ env := stage.header_le.trans continuation.le
    have same := Option.some.inj (lookup.symm.trans (below.constants constant))
    cases same
    exact Obs.constructorAtHeader henv hscoped below constantHeaders hTarget constant
      noDefinition noNative noQuotient seedLength seedWF levelsWF rightWF seedEq equivalent
      signature typeClosed certificate typed plan (by simpa only [Obs.nativeDepth] using bound)
  | .empty => exact ⟨.empty⟩
  | .union left right =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth] using bound)
    obtain ⟨a⟩ := Obs.definitionHeaderConstTransfer
      henv hscoped oldHeaders oldDefinitions constantHeaders smaller hTarget constant rightWF equivalent left bounds.1
      (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨b⟩ := Obs.definitionHeaderConstTransfer
      henv hscoped oldHeaders oldDefinitions constantHeaders smaller hTarget constant rightWF equivalent right bounds.2
      (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    obtain ⟨result⟩ := Obs.definitionHeaderConstTransfer
      henv hscoped oldHeaders oldDefinitions constantHeaders smaller hTarget constant rightWF equivalent source (by simpa only [Obs.nativeDepth] using bound) resources
    exact ⟨result.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨result⟩ := Obs.definitionHeaderConstTransfer
      henv hscoped oldHeaders oldDefinitions constantHeaders smaller hTarget constant rightWF equivalent source (by simpa only [Obs.nativeDepth] using bound) resources
    exact ⟨result.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨result⟩ := Obs.definitionHeaderConstTransfer
      henv hscoped oldHeaders oldDefinitions constantHeaders smaller hTarget constant rightWF equivalent source (by simpa only [Obs.nativeDepth] using bound) resources
    exact ⟨result.unpad⟩
  | .rowShift source =>
    obtain ⟨result⟩ := Obs.definitionHeaderConstTransfer
      henv hscoped oldHeaders oldDefinitions constantHeaders smaller hTarget constant rightWF equivalent source (by simpa only [Obs.nativeDepth] using bound) resources
    exact ⟨(result.pad henv hscoped hTarget).view henv hscoped hTarget (.commutePadFn _ _)⟩
termination_by sizeOf observation

include previous stage continuation in
/-- The full original `Strong.constDF` semantic case at an actual definition header.
The backward direction uses its ORIGINAL source type-equality child. -/
theorem Joint.definitionHeaderConstDF
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (oldHeaders : PreviousHeaders (old := old) (base := base) (declarations := declarations)
      (env := env) (U := U) (registry := registry))
    (oldDefinitions : PreviousDefinitions (base := base) (declarations := declarations)
      (env := env) (U := U) (registry := registry))
    (constantHeaders : OriginalConstantHeaders stage.header env U registry)
    {fuel : Nat}
    (smaller : ∀ lower, lower < fuel → ∀ {Γ l r A}, stage.header.IsDefEqStrong U Γ l r A →
      Joint (definitionCurrent stage.values) lower env U registry Γ l r A)
    {Γ : List VExpr} {name : Name} {ci : VConstant}
    (constant : stage.header.constants name = some ci)
    {levels levels' : List VLevel}
    (leftWF : ∀ level ∈ levels, level.WF U)
    (rightWF : ∀ level ∈ levels', level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) levels levels')
    (originalType : Joint (definitionCurrent stage.values) fuel env U registry Γ
      (ci.type.instL levels) (ci.type.instL levels') (.sort typeLevel)) :
    Joint (definitionCurrent stage.values) fuel env U registry Γ
      (.const name levels) (.const name levels') (ci.type.instL levels) := by
  apply Joint.of_transfers henv
  intro target locals σ τ available closed hTarget substitutions fits
  constructor
  · intro n demand footprint observation bound resources
    exact Obs.definitionHeaderConstTransfer previous stage continuation
      henv hscoped oldHeaders oldDefinitions constantHeaders smaller hTarget constant rightWF equivalent observation bound resources
  · apply Transfer.convert henv hscoped originalType.symm closed hTarget substitutions fits
    intro n demand footprint observation bound resources
    exact Obs.definitionHeaderConstTransfer previous stage continuation
      henv hscoped oldHeaders oldDefinitions constantHeaders smaller hTarget constant leftWF (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip equivalent)) observation bound resources

end
end Lean4Lean.AnchoredSource.Adapted.Staged
