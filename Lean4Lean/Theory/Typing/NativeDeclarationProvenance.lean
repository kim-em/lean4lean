import Lean4Lean.Theory.Typing.NativeRegistryInstallation
import Lean4Lean.Theory.Typing.InductiveDeclarationHistory
import Lean4Lean.Theory.Typing.CanonicalHeadRegistry

/-! Native table installation with original declaration provenance.

`NativeRecursorRegistered` checks a final environment.  It does not identify
the declaration whose pre-equation header may be used by stage induction.
The finite construction here follows the actual `WF'` constructors and the
existing `installEntries` operation.  Lookup therefore returns the original
header and its ordinal, rather than an unrelated existential predecessor.
-/
namespace Lean4Lean.VEnv
open InductiveSignature NativeRecursorData
open private declaration_le from Lean4Lean.Theory.Typing.DefinitionHistory
variable {name key : Name} {env extended base envTypes envCtors : VEnv}
  {source expanded : VInductDecl} {block : VInductBlock} {schema : CaseSchema}
  {signature : InductiveSignature} {generated : Instance signature}
  {auxiliaries : List ContainerSpecialization} {equation : VDefEq}

/-- A lookup packet, produced from a concrete table history below. -/
structure NativeDeclarationOrigin (env : VEnv) (declarations : List VDecl)
    (data : NativeRecursorData) where
  source : VInductDecl
  stage : InductiveStage env source declarations.length
  laterDeclarations : List VDecl
  declarations_eq : declarations = laterDeclarations ++ .induct source :: stage.earlierDeclarations
  expanded : VInductDecl
  signature : InductiveSignature
  generated : Instance signature
  auxiliaries : List ContainerSpecialization
  key : Name
  compilationBase : VEnv
  compilationBelow : compilationBase ≤ stage.base
  compilation : CompilationData compilationBase source expanded signature generated auxiliaries stage.block
  specializations : CertifiedSpecializations compilationBase auxiliaries
  entry : data ∈ compilationEntries key source signature auxiliaries generated

namespace NativeDeclarationOrigin

def later (origin : NativeDeclarationOrigin env declarations data)
    (declaration : VDecl.WF env d extended) : NativeDeclarationOrigin extended (d :: declarations) data where
  source := origin.source
  stage := origin.stage.later (declaration_le declaration) (Nat.le_succ _)
  laterDeclarations := d :: origin.laterDeclarations
  declarations_eq := by simpa only [List.cons_append, InductiveStage.later] using congrArg (List.cons d) origin.declarations_eq
  expanded := origin.expanded
  signature := origin.signature
  generated := origin.generated
  auxiliaries := origin.auxiliaries
  key := origin.key
  compilationBase := origin.compilationBase
  compilationBelow := origin.compilationBelow
  compilation := origin.compilation
  specializations := origin.specializations
  entry := origin.entry

def metadata (origin : NativeDeclarationOrigin env declarations data)
    (hle : env ≤ extended) : NativeDeclarationOrigin extended declarations data where
  source := origin.source
  stage := origin.stage.later hle (Nat.le_refl _)
  laterDeclarations := origin.laterDeclarations
  declarations_eq := origin.declarations_eq
  expanded := origin.expanded
  signature := origin.signature
  generated := origin.generated
  auxiliaries := origin.auxiliaries
  key := origin.key
  compilationBase := origin.compilationBase
  compilationBelow := origin.compilationBelow
  compilation := origin.compilation
  specializations := origin.specializations
  entry := origin.entry

/-- Metadata entries use exactly the names installed by their original block. -/
theorem name_member (origin : NativeDeclarationOrigin env declarations data) :
    data.name ∈ origin.stage.block.recursors.map (·.name) := by
  rw [← origin.compilation.nativeEntries_names (key := origin.key)]
  exact List.mem_map.mpr ⟨data, origin.entry, rfl⟩

/-- The local control filter is the original block's finite name list. -/
def current (origin : NativeDeclarationOrigin env declarations data) (name : Name) : Bool :=
  origin.stage.block.recursors.any (fun value => value.name == name)

theorem current_self (origin : NativeDeclarationOrigin env declarations data) :
    origin.current data.name = true := by
  obtain ⟨value, member, same⟩ := List.mem_map.mp origin.name_member
  exact List.any_eq_true.mpr ⟨value, member, by simpa only [beq_iff_eq] using same⟩

/-- A declaration ordinal is retained even when later metadata leaves the
declaration list unchanged. -/
theorem ordinal_lt (origin : NativeDeclarationOrigin env declarations data) :
    origin.stage.earlierDeclarations.length < declarations.length := origin.stage.earlier

theorem installed (origin : NativeDeclarationOrigin env declarations data) :
    origin.stage.block.install origin.stage.base = some origin.stage.installed := by
  simp [VInductBlock.install, origin.stage.typing.addTypes,
    origin.stage.typing.addConstructors, origin.stage.typing.addRecursors,
    Option.bind_some, origin.stage.typing.installed_eq]

theorem metadata_eq (origin : NativeDeclarationOrigin env declarations data) :
    data.block = origin.key ∧
      data.schema = CaseSchema.ofCompilation origin.source origin.signature origin.auxiliaries := by
  obtain ⟨owner, _, same⟩ := List.mem_map.mp origin.entry
  exact ⟨congrArg (·.block) same.symm, congrArg (·.schema) same.symm⟩

theorem registered (origin : NativeDeclarationOrigin env declarations data) :
    NativeRecursorRegistered env data :=
  NativeRecursorRegistered.compilationEntries origin.compilation origin.specializations
    origin.compilationBelow origin.installed origin.stage.installedBelow origin.entry

private theorem selectedCompilation_of_mem
    (compiled : CompilationData base source expanded signature generated auxiliaries block)
    (entry : data ∈ compilationEntries key source signature auxiliaries generated) :
    CompilationData base source expanded data.schema.signature data.nativeInstance auxiliaries block := by
  obtain ⟨owner, _, rfl⟩ := List.mem_map.mp entry
  have same : (ofInstance key (CaseSchema.ofCompilation source signature auxiliaries)
      generated owner).nativeInstance = generated := by
    cases generated
    simp only [ofInstance, nativeInstance, CaseSchema.ofCompilation]
    congr 1
    exact funext fun owner => (compiled.recursorNames owner).symm
  change CompilationData base source expanded signature _ auxiliaries block
  rw [same]
  exact compiled

/-- Normalize the occurrence descriptor to the exact compilation packet,
without selecting a new existential installation from final registration. -/
theorem selectedCompilation (origin : NativeDeclarationOrigin env declarations data) :
    CompilationData origin.compilationBase origin.source origin.expanded data.schema.signature
      data.nativeInstance origin.auxiliaries origin.stage.block :=
  selectedCompilation_of_mem origin.compilation origin.entry

theorem restoration (origin : NativeDeclarationOrigin env declarations data) :
    data.schema.restoration = compilationRestoration origin.source origin.auxiliaries := by
  rw [origin.metadata_eq.2]
  rfl

theorem type_member (origin : NativeDeclarationOrigin env declarations data)
    (selected : data.recursorType = some type) :
    ({ name := data.name, uvars := data.uvars, type := type } : VConstVal) ∈
      origin.stage.block.recursors := by
  have compiled := origin.selectedCompilation
  have generated : data.nativeInstance.recursor data.owner ∈ data.nativeInstance.recursors :=
    List.mem_map.mpr ⟨data.owner, List.mem_finRange _, rfl⟩
  obtain ⟨actual, member, restored⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    (List.mapM_eq_some.mp compiled.recursors) _ generated
  have target : (compilationRestoration origin.source origin.auxiliaries).expr
      (data.nativeInstance.recursorType data.owner) = some type := by
    simpa only [NativeRecursorData.recursorType, origin.restoration] using selected
  have same : actual = { name := data.name, uvars := data.uvars, type := type } := by
    simp only [Restoration.recursor, Instance.recursor, target] at restored
    have equal := Option.some.inj restored
    rw [← equal]
    simp only [NativeRecursorData.name, origin.restoration, NativeRecursorData.nativeInstance]
  exact same ▸ member

theorem equation_member (origin : NativeDeclarationOrigin env declarations data)
    (selected : data.equation index = some equation) : equation ∈ origin.stage.block.rules := by
  have compiled := origin.selectedCompilation
  have generated : data.nativeInstance.equation index ∈ data.nativeInstance.equations :=
    List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩
  obtain ⟨actual, member, restored⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    (List.mapM_eq_some.mp compiled.equations) _ generated
  have target : (compilationRestoration origin.source origin.auxiliaries).equation
      (data.nativeInstance.equation index) = some equation := by
    simpa only [NativeRecursorData.equation, origin.restoration] using selected
  exact Option.some.inj (restored.symm.trans target) ▸ member

theorem singleton_member (origin : NativeDeclarationOrigin env declarations data)
    (selected : data.singletonEquation = some equation) : equation ∈ origin.stage.block.rules := by
  unfold singletonEquation at selected
  dsimp only at selected
  split at selected <;> try contradiction
  exact origin.equation_member selected

/-- Both endpoints are ORIGINAL equation-typing roots at the pre-equation
header selected by this registry entry. -/
theorem singletonStrong (origin : NativeDeclarationOrigin env declarations data)
    (selected : data.singletonEquation = some equation) :
    origin.stage.typing.recursors.IsDefEqStrong equation.uvars [] equation.lhs equation.lhs equation.type ∧
      origin.stage.typing.recursors.IsDefEqStrong equation.uvars [] equation.rhs equation.rhs equation.type :=
  origin.stage.typing.ruleStrong (origin.singleton_member selected)

theorem typeStrong (origin : NativeDeclarationOrigin env declarations data)
    (selected : data.recursorType = some type) :
    ∃ level, origin.stage.typing.recursors.IsDefEqStrong data.uvars [] type type (.sort level) := by
  obtain ⟨level, original⟩ := origin.stage.typing.recursorTypeStrong (origin.type_member selected)
  exact ⟨level, original.mono (VEnv.addConstVals_le origin.stage.typing.addRecursors)⟩

/-- Current names cannot already occur in the declaration's predecessor.
This is actual installation freshness, not an absence premise on semantics. -/
theorem current_old (origin : NativeDeclarationOrigin env declarations data)
    (lookup : origin.stage.base.constants name = some value) : origin.current name = false := by
  cases selected : origin.current name with
  | false => rfl
  | true =>
    obtain ⟨recursor, member, same⟩ := List.any_eq_true.mp selected
    have fresh := VEnv.addConstVals_names_fresh origin.stage.typing.addRecursors recursor member
    have baseLE : origin.stage.base ≤ origin.stage.typing.constructors.addProjections origin.stage.block.projections :=
      (VEnv.addConstVals_le origin.stage.typing.addTypes).trans
        ((VEnv.addConstVals_le origin.stage.typing.addConstructors).trans VEnv.addProjections_le)
    have contradiction := baseLE.constants lookup
    have eqName : recursor.name = name := by simpa only [beq_iff_eq] using same
    rw [← eqName, fresh] at contradiction
    cases contradiction

end NativeDeclarationOrigin

/-- A finite native registry built along an actual declaration history.
The `native` constructor registers all family descriptors from the very block
whose constants and equations are installed by that declaration.  Ordinary
declarations and metadata preserve previously recorded entries. -/
inductive NativeRegistryHistory : VEnv → List VDecl → (Name → Option NativeRecursorData) → Prop where
  | empty : NativeRegistryHistory .empty [] (fun _ => none)
  | decl {env extended : VEnv} {declarations : List VDecl} {table : Name → Option NativeRecursorData} (previous : NativeRegistryHistory env declarations table)
      (declaration : VDecl.WF env d extended) :
      NativeRegistryHistory extended (d :: declarations) table
  | native {base extended compilationBase : VEnv} {declarations : List VDecl} {table : Name → Option NativeRecursorData}
      {source expanded : VInductDecl} {block : VInductBlock} {signature : InductiveSignature}
      {generated : Instance signature} {auxiliaries : List ContainerSpecialization} {key : Name}
      (previous : NativeRegistryHistory base declarations table)
      (original : source.WF base)
      (compiled : source.CompilesTo base block)
      (formed : block.WF base)
      (installed : block.install base = some extended)
      (compilation : CompilationData compilationBase source expanded signature generated auxiliaries block)
      (specializations : CertifiedSpecializations compilationBase auxiliaries)
      (compilationBelow : compilationBase ≤ base) :
      NativeRegistryHistory extended (.induct source :: declarations)
        (installEntries table (compilationEntries key source signature auxiliaries generated))
  | eliminators {env base : VEnv} {declarations baseDeclarations : List VDecl}
      {table : Name → Option NativeRecursorData} {source : VInductDecl} {block : VInductBlock}
      {schema : CaseSchema} {key : Name} (previous : NativeRegistryHistory env declarations table)
      (baseHistory : base.WF' baseDeclarations)
      (hle : base ≤ env)
      (formed : schema.Certified base source block)
      (keyEq : source.types.head?.map (·.name) = some key)
      (constants : (∀ value ∈ block.types ++ block.ctors,
        env.constants value.name = some value.toVConstant) ∧ env.defeqs = base.defeqs ∧
        schema.ProjNamesRegistered env key)
      (fresh : schema.Fresh env key)
      (compat : schema.StructCompat env) :
      NativeRegistryHistory (env.addEliminator key schema) declarations table
  | projections {base envTypes envCtors : VEnv} {declarations baseDeclarations : List VDecl}
      {table : Name → Option NativeRecursorData} {source : VInductDecl} {block : VInductBlock}
      (previous : NativeRegistryHistory envCtors declarations table)
      (baseHistory : base.WF' baseDeclarations)
      (sourceNames : source.sourceNames.Nodup)
      (typeHeadersWF : ∀ type ∈ source.types, type.toVConstant.WF base)
      (constructorUvars : ∀ ctor ∈ source.constructorConstants, ctor.uvars = source.uvars)
      (constructorsWF : ∀ ctor ∈ source.constructorConstants, ctor.toVConstant.WF envTypes)
      (parameters : source.SourceParameterWF base)
      (shape : ∀ type ∈ source.types, ∀ ctor ∈ type.ctors, source.RawCtorShape type ctor)
      (types : block.types = source.typeConstants)
      (constructors : block.ctors = source.constructorConstants)
      (projections : block.projections = source.projectionEntries)
      (addTypes : base.addConstVals block.types = some envTypes)
      (addConstructors : envTypes.addConstVals block.ctors = some envCtors) :
      NativeRegistryHistory (envCtors.addProjections block.projections) declarations table

namespace NativeRegistryHistory

theorem history (H : NativeRegistryHistory env declarations table) : env.WF' declarations := by
  induction H with
  | empty => exact .empty
  | decl _ declaration ih => exact .decl declaration ih
  | native _ original compiled formed installed _ _ _ ih =>
    exact .decl (.induct original (.intro original compiled formed installed)) ih
  | eliminators _ baseHistory hle formed keyEq constants fresh compat ih =>
    exact .inductEliminators baseHistory ih hle formed keyEq constants fresh compat
  | projections _ baseHistory sourceNames typeHeadersWF constructorUvars constructorsWF parameters shape types constructors projections addTypes addConstructors ih =>
    exact .inductProjections baseHistory ih sourceNames typeHeadersWF constructorUvars constructorsWF
      parameters shape types constructors projections addTypes addConstructors

/-- Lookup follows the concrete list installation, retaining exactly one
original compilation and header. No current/final-environment Strong proof
is reinterpreted as an earlier induction hypothesis. -/
theorem origin (H : NativeRegistryHistory env declarations table)
    (lookup : table name = some data) :
    data.name = name ∧ Nonempty (NativeDeclarationOrigin env declarations data) := by
  induction H with
  | empty => cases lookup
  | decl _ declaration ih =>
    obtain ⟨same, ⟨origin⟩⟩ := ih lookup
    exact ⟨same, ⟨origin.later declaration⟩⟩
  | @native base extended compilationBase declarations table source expanded block signature generated auxiliaries key
      previous original compiled formed installed compilation specializations compilationBelow ih =>
    unfold installEntries at lookup
    cases found : (compilationEntries key source signature auxiliaries generated).find?
        (fun value => value.name == name) with
    | none =>
      obtain ⟨same, ⟨origin⟩⟩ := ih (by simpa only [found, Option.orElse_none] using lookup)
      exact ⟨same, ⟨origin.later (.induct original (.intro original compiled formed installed))⟩⟩
    | some selected =>
      simp only [found, Option.orElse_some, Option.some.injEq] at lookup
      subst selected
      obtain ⟨stages⟩ := VInductBlock.TypingStages.ofInstallation
        ⟨declarations, previous.history⟩ original compiled formed installed
      refine ⟨by simpa only [beq_iff_eq] using List.find?_some found, ⟨{
        source := source
        stage := ⟨base, extended, block, declarations, previous.history,
          Nat.lt_succ_self _, original, compiled, stages, .rfl⟩
        laterDeclarations := []
        declarations_eq := rfl
        expanded := expanded
        signature := signature
        generated := generated
        auxiliaries := auxiliaries
        key := key
        compilationBase := compilationBase
        compilationBelow := compilationBelow
        compilation := compilation
        specializations := specializations
        entry := List.mem_of_find?_eq_some found }⟩⟩
  | eliminators _ _ _ _ _ _ _ _ ih =>
    obtain ⟨same, ⟨origin⟩⟩ := ih lookup
    exact ⟨same, ⟨origin.metadata VEnv.addEliminator_le⟩⟩
  | projections _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨same, ⟨origin⟩⟩ := ih lookup
    exact ⟨same, ⟨origin.metadata VEnv.addProjections_le⟩⟩

/-- The actual table history supplies native registration independently of
optional abstract-schema metadata. -/
theorem registered (H : NativeRegistryHistory env declarations table)
    (lookup : table name = some data) : NativeRecursorRegistered env data ∧ data.name = name := by
  obtain ⟨same, ⟨origin⟩⟩ := H.origin lookup
  exact ⟨origin.registered, same⟩

theorem registryScoped (H : NativeRegistryHistory env declarations table) :
    (CanonicalHead.Registry.ofHistory declarations table).Scoped :=
  CanonicalHead.Registry.ofHistory_scoped H.history
    (fun name data lookup => (H.registered lookup).1)

end NativeRegistryHistory

/-- A native installation cannot manufacture a new metadata entry for an
already present constant. This is the backward lookup used when interpreting
an earlier source header against a later final registry. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.installEntries_previous
    (compiled : CompilationData base source expanded signature generated auxiliaries block)
    (installed : block.install installBase = some extended)
    (present : installBase.constants name = some value)
    (lookup : installEntries table (compilationEntries key source signature auxiliaries generated)
      name = some data) : table name = some data := by
  unfold installEntries at lookup
  cases found : (compilationEntries key source signature auxiliaries generated).find?
      (fun value => value.name == name) with
  | none => simpa only [found, Option.orElse_none] using lookup
  | some newEntry =>
    have same : newEntry.name = name := by simpa only [beq_iff_eq] using List.find?_some found
    have fresh := compiled.nativeEntries_fresh installed (List.mem_of_find?_eq_some found)
    rw [same, present] at fresh
    cases fresh

end Lean4Lean.VEnv
