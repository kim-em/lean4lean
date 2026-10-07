import Lean4Lean.Theory.Typing.NativeDeclarationProvenance

/-! Actual continuation of a finite native table history. Earlier header
constants pull lookup backwards through every subsequent native install. -/
namespace Lean4Lean.VEnv.NativeRegistryHistory
open InductiveSignature NativeRecursorData
open private declaration_le from Lean4Lean.Theory.Typing.DefinitionHistory

inductive Prefix {base : VEnv} {before : List VDecl} {old : Name → Option NativeRecursorData}
    (first : NativeRegistryHistory base before old) :
    {env : VEnv} → {declarations : List VDecl} → {table : Name → Option NativeRecursorData} →
      NativeRegistryHistory env declarations table → Prop where
  | refl : Prefix first first
  | decl {env extended : VEnv} {declarations : List VDecl} {table : Name → Option NativeRecursorData}
      {previous : NativeRegistryHistory env declarations table}
      (continuation : Prefix first previous) (declaration : VDecl.WF env d extended) :
      Prefix first (.decl previous declaration)
  | native {base extended compilationBase : VEnv} {declarations : List VDecl} {table : Name → Option NativeRecursorData}
      {source expanded : VInductDecl} {block : VInductBlock} {signature : InductiveSignature}
      {generated : Instance signature} {auxiliaries : List ContainerSpecialization} {key : Name}
      {previous : NativeRegistryHistory base declarations table}
      (continuation : Prefix first previous)
      (original : source.WF base) (compiled : source.CompilesTo base block)
      (formed : block.WF base) (installed : block.install base = some extended)
      (compilation : CompilationData compilationBase source expanded signature generated auxiliaries block)
      (specializations : CertifiedSpecializations compilationBase auxiliaries)
      (compilationBelow : compilationBase ≤ base) :
      Prefix first (.native previous original compiled formed installed compilation specializations compilationBelow (key := key))
  | eliminators {env base : VEnv} {declarations baseDeclarations : List VDecl}
      {table : Name → Option NativeRecursorData} {source : VInductDecl} {block : VInductBlock}
      {schema : CaseSchema} {key : Name} {previous : NativeRegistryHistory env declarations table}
      (continuation : Prefix first previous) (baseHistory : base.WF' baseDeclarations)
      (hle : base ≤ env) (formed : schema.Certified base source block)
      (keyEq : source.types.head?.map (·.name) = some key)
      (constants : (∀ value ∈ block.types ++ block.ctors,
        env.constants value.name = some value.toVConstant) ∧ env.defeqs = base.defeqs ∧
        schema.ProjNamesRegistered env key)
      (fresh : schema.Fresh env key) (compat : schema.StructCompat env) :
      Prefix first (.eliminators previous baseHistory hle formed keyEq constants fresh compat)
  | projections {base envTypes envCtors : VEnv} {declarations baseDeclarations : List VDecl}
      {table : Name → Option NativeRecursorData} {source : VInductDecl} {block : VInductBlock}
      {previous : NativeRegistryHistory envCtors declarations table}
      (continuation : Prefix first previous) (baseHistory : base.WF' baseDeclarations)
      (sourceNames : source.sourceNames.Nodup)
      (typeHeadersWF : ∀ type ∈ source.types, type.toVConstant.WF base)
      (constructorUvars : ∀ ctor ∈ source.constructorConstants, ctor.uvars = source.uvars)
      (constructorsWF : ∀ ctor ∈ source.constructorConstants, ctor.toVConstant.WF envTypes)
      (parameters : source.SourceParameterWF base)
      (shape : ∀ type ∈ source.types, ∀ ctor ∈ type.ctors, source.RawCtorShape type ctor)
      (types : block.types = source.typeConstants) (constructors : block.ctors = source.constructorConstants)
      (projections : block.projections = source.projectionEntries)
      (addTypes : base.addConstVals block.types = some envTypes)
      (addConstructors : envTypes.addConstVals block.ctors = some envCtors) :
      Prefix first (.projections previous baseHistory sourceNames typeHeadersWF constructorUvars constructorsWF
        parameters shape types constructors projections addTypes addConstructors)

namespace Prefix
variable {base env : VEnv} {before declarations : List VDecl}
    {old table : Name → Option NativeRecursorData}
    {first : NativeRegistryHistory base before old} {last : NativeRegistryHistory env declarations table}

theorem le (continuation : Prefix first last) : base ≤ env := by
  induction continuation with
  | refl => exact .rfl
  | decl _ declaration ih => exact ih.trans (declaration_le declaration)
  | native _ original compiled formed installed _ _ _ ih =>
    exact ih.trans (declaration_le (.induct original (.intro original compiled formed installed)))
  | eliminators _ _ _ _ _ _ _ _ ih => exact ih.trans VEnv.addEliminator_le
  | projections _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih.trans VEnv.addProjections_le

theorem declarations_eq (continuation : Prefix first last) : ∃ added, declarations = added ++ before := by
  induction continuation with
  | refl => exact ⟨[], rfl⟩
  | decl _ _ ih | native _ _ _ _ _ _ _ _ ih =>
    obtain ⟨added, rfl⟩ := ih
    exact ⟨_ :: added, rfl⟩
  | eliminators _ _ _ _ _ _ _ _ ih => exact ih
  | projections _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

theorem length_le (continuation : Prefix first last) : before.length ≤ declarations.length := by
  obtain ⟨added, rfl⟩ := continuation.declarations_eq
  simp only [List.length_append]
  omega

theorem previous_lookup (continuation : Prefix first last) {name : Name}
    (present : base.constants name = some value) (lookup : table name = some data) : old name = some data := by
  induction continuation with
  | refl => exact lookup
  | decl _ _ ih => exact ih lookup
  | native continuation original compiled formed installed compilation _ _ ih =>
    exact ih (compilation.installEntries_previous installed (continuation.le.constants present) lookup)
  | eliminators _ _ _ _ _ _ _ _ ih => exact ih lookup
  | projections _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih lookup

/-- Transport only the final-history frame. The original header and its
compilation remain definitionally identical. -/
noncomputable def origin (continuation : Prefix first last)
    (packet : NativeDeclarationOrigin base before data) : NativeDeclarationOrigin env declarations data where
  source := packet.source
  stage := packet.stage.later continuation.le continuation.length_le
  laterDeclarations := continuation.declarations_eq.choose ++ packet.laterDeclarations
  declarations_eq := by
    simpa only [InductiveStage.later, List.append_assoc] using
      continuation.declarations_eq.choose_spec.trans
        (congrArg (fun ds : List VDecl => continuation.declarations_eq.choose ++ ds) packet.declarations_eq)
  expanded := packet.expanded
  signature := packet.signature
  generated := packet.generated
  auxiliaries := packet.auxiliaries
  key := packet.key
  compilationBase := packet.compilationBase
  compilationBelow := packet.compilationBelow
  compilation := packet.compilation
  specializations := packet.specializations
  entry := packet.entry

end Prefix
end Lean4Lean.VEnv.NativeRegistryHistory
