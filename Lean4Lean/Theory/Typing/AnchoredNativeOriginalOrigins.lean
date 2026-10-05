import Lean4Lean.Theory.Typing.AnchoredNativeGeneratedOrigins
import Lean4Lean.Theory.Typing.NativeSingletonSourceFields
import Lean4Lean.Theory.Typing.NativeDeclarationProvenance

/-! The complete finite capture-origin chain at its genuine declaration
stage. Proof-field formation comes from the original singleton branch; no
instruction-indexed typing producer is supplied by the caller. -/
namespace Lean4Lean.VEnv.NativeDeclarationOrigin
open VExpr InductiveSignature NativeRecursorData
open AnchoredSource.Adapted
set_option backward.isDefEq.respectTransparency false

private theorem telescope_context {env : VEnv} {U : Nat} {Γ domains : List VExpr}
    {result : VExpr} (henv : env.Ordered)
    (formed : OnCtx Γ (env.IsType U))
    (type : env.IsType U Γ (wrapForalls domains result)) :
    OnCtx (domains.reverse ++ Γ) (env.IsType U) := by
  induction domains generalizing Γ with
  | nil => exact formed
  | cons domain domains ih =>
    obtain ⟨domainType, bodyType⟩ := IsType.forallE_inv henv type
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
      ih (Γ := domain :: Γ) ⟨formed, domainType⟩ bodyType

/-- Literal header provenance identifies the checked admissibility environment
with the actual source-header stage retained by installation. -/
theorem sourceAdmissible
    (origin : NativeDeclarationOrigin env declarations data)
    (families : data.schema.signature.families.size = 1) :
    data.nativeInstance.Admissible origin.stage.typing.types := by
  obtain ⟨headers, added, admissible⟩ := origin.selectedCompilation.admissible
  apply admissible.mono
  apply VEnv.addConstVals_mono origin.compilationBelow added
  rw [← origin.selectedCompilation.typeConstants_of_singleton families,
    ← origin.selectedCompilation.types]
  exact origin.stage.typing.addTypes

/-- All copied-index and proof-field origins are constructed from their actual
compiled equation and original singleton-elimination evidence. -/
theorem captureOrigins_of_singleton
    {env : VEnv} {declarations : List VDecl} {data : NativeRecursorData}
    {program : SaturatedProgram data} {U : Nat}
    (origin : NativeDeclarationOrigin env declarations data)
    (henv : env.Ordered)
    (eliminator : env.eliminators data.block data.schema)
    (singleton : data.schema.signature.SingletonElimination
      origin.stage.typing.types data.uvars data.levels)
    (levelsWF : ∀ level ∈ program.levels, level.WF U)
    {signature : NativeConstantSignature data program.levels}
    {index : Fin data.schema.signature.constructors.size} {rule : VDefEq}
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule)
    (selected : data.saturatedProgram program.levels
      (program.prefixArgs ++ program.trailing) = some program) :
    Nonempty (NativeCaptureOrigins origin.stage.typing.recursors U
      (program.equationBody.domains.map (·.instL program.levels)).reverse program
      (program.equationBody.lhs.instL program.levels).getAppFnArgs.2
      (vars program.equationBody.domains.length 0) program.instructions.length) := by
  have hsource := origin.stage.typing.recursorsWF.ordered
  have spec := saturatedProgram_spec selected
  have member := origin.singleton_member spec.2.2.2.2.2.2.2.2.1
  have original := (origin.stage.typing.originalRules program.equation member).1
  obtain ⟨typeLevel, typeWF⟩ := IsDefEq.isType hsource (Γ := []) trivial original
  have specialized := typeWF.instL levelsWF
  have fullType : origin.stage.typing.recursors.IsType U []
      (wrapForalls (program.equationBody.domains.map (·.instL program.levels))
        (program.equationBody.type.instL program.levels)) := by
    rw [← instL_wrapForalls,
      (CaseSchema.EquationBody.extract_sound spec.2.2.2.2.2.2.2.2.2.1).2.2]
    exact ⟨_, specialized⟩
  have fullContext : OnCtx
      (program.equationBody.domains.map (·.instL program.levels)).reverse
      (origin.stage.typing.recursors.IsType U) := by
    simpa only [List.append_nil] using telescope_context (Γ := []) hsource trivial fullType
  have typesBelow : origin.stage.typing.types ≤ origin.stage.typing.recursors :=
    (VEnv.addConstVals_le origin.stage.typing.addConstructors).trans
      (VEnv.addProjections_le.trans (VEnv.addConstVals_le origin.stage.typing.addRecursors))
  have identity : data.schema.restoration = {} :=
    origin.restoration.trans (origin.selectedCompilation.restoration_of_singleton singleton.1)
  apply NativeCaptureOrigins.generated henv hsource (signature := signature)
    origin.registered singleton.1 singleton.2.1 owner equation selected
  intro field domain instruction
  have raw := data.saturatedProgram_proofField_inst origin.stage.typing.typesWF.ordered
    identity singleton levelsWF selected instruction
  apply (raw.mono typesBelow).strong hsource
  have reordered : OnCtx
      (((program.equationBody.domains.drop (data.indexOffset + field)).map
        (·.instL program.levels)).reverse ++
       ((program.equationBody.domains.take (data.indexOffset + field)).map
        (·.instL program.levels)).reverse)
      (origin.stage.typing.recursors.IsType U) := by
    rw [← List.reverse_append, ← List.map_append, List.take_append_drop]
    exact fullContext
  exact reordered.of_append

/-- In the large-elimination branch whose family is not always relevant,
the installed declaration's own admissibility proof selects singleton
elimination. No field-typing predicate remains in the caller contract. -/
theorem captureOrigins
    {env : VEnv} {declarations : List VDecl} {data : NativeRecursorData}
    {program : SaturatedProgram data} {U : Nat}
    (origin : NativeDeclarationOrigin env declarations data)
    (henv : env.Ordered)
    (eliminator : env.eliminators data.block data.schema)
    (families : data.schema.signature.families.size = 1)
    (notRelevant : ¬ ∀ family ∈ data.schema.signature.families.toList,
      (family.resultLevel.inst data.levels).IsNeverZero)
    (notProofTarget : ¬ data.target ≈ .zero)
    (levelsWF : ∀ level ∈ program.levels, level.WF U)
    {signature : NativeConstantSignature data program.levels}
    {index : Fin data.schema.signature.constructors.size} {rule : VDefEq}
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule)
    (selected : data.saturatedProgram program.levels
      (program.prefixArgs ++ program.trailing) = some program) :
    Nonempty (NativeCaptureOrigins origin.stage.typing.recursors U
      (program.equationBody.domains.map (·.instL program.levels)).reverse program
      (program.equationBody.lhs.instL program.levels).getAppFnArgs.2
      (vars program.equationBody.domains.length 0) program.instructions.length) := by
  have singleton := ((origin.sourceAdmissible families).elimination.resolve_left notRelevant).resolve_left
    notProofTarget
  exact origin.captureOrigins_of_singleton henv eliminator singleton levelsWF
    (signature := signature) owner equation selected

end Lean4Lean.VEnv.NativeDeclarationOrigin
