import Lean4Lean.Theory.Typing.NativeSingletonProofFields

namespace Lean4Lean.InductiveSignature
open VExpr VEnv NativeRecursorData

/-- Specialize the actual declaration's singleton field classification. -/
theorem SingletonElimination.instL
    {s : InductiveSignature} {env : VEnv} {U V : Nat}
    {levels substitution : List VLevel}
    (singleton : s.SingletonElimination env U levels)
    (levelsWF : ∀ level ∈ substitution, level.WF V) :
    s.SingletonElimination env V (levels.map (·.inst substitution)) := by
  refine ⟨singleton.1, singleton.2.1, ?_⟩
  intro ctor member field bound
  rcases singleton.2.2 ctor member field bound with proof | index
  · left
    have specialized := proof.instL levelsWF
    simpa only [List.map_append, List.map_reverse, List.map_map, Function.comp_def,
      ← VExpr.instL_instL, VExpr.instL, VLevel.inst] using specialized
  · exact Or.inr index

/-- The actual singleton branch of source-header admissibility justifies all
proof instructions at an occurrence's universe packet. Source admissibility
itself is supplied by `CompilationData.admissible_source_of_singleton`, whose
literal header identity preserves the original declaration environment. -/
theorem NativeRecursorData.saturatedProgram_proofField_inst
    {data : NativeRecursorData} {program : SaturatedProgram data}
    {env : VEnv} {U : Nat} {levels : List VLevel} {arguments : List VExpr}
    (henv : env.Ordered) (identity : data.schema.restoration = {})
    (singleton : data.schema.signature.SingletonElimination env data.uvars data.levels)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (selected : data.saturatedProgram levels arguments = some program)
    {field : Nat} {domain : VExpr}
    (instruction : program.instructions[field]? = some (.proof domain)) :
    env.HasType U
      (((program.equationBody.domains.take (data.indexOffset + field)).map
        (·.instL levels)).reverse) domain (.sort .zero) :=
  data.saturatedProgram_proofField henv identity (singleton.instL levelsWF) selected instruction

end Lean4Lean.InductiveSignature
