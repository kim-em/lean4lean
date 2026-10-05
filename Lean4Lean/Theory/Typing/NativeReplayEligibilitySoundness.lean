import Lean4Lean.Theory.Inductive.NativeReplayEligibility
import Lean4Lean.Theory.Typing.AnchoredNativeOriginalOrigins

/-! The finite replay classification is justified by the actual declaration's
elimination permission. It introduces no field-typing callback or new oracle. -/

namespace Lean4Lean.VEnv.NativeDeclarationOrigin
open VExpr InductiveSignature NativeRecursorData

theorem singleton_of_proofReplayEligible
    (origin : NativeDeclarationOrigin env declarations data)
    (eligible : data.proofReplayEligible = true) :
    data.schema.signature.SingletonElimination
      origin.stage.typing.types data.uvars data.levels := by
  obtain ⟨families, notRelevant, notProofTarget⟩ := proofReplayEligible_spec eligible
  exact ((origin.sourceAdmissible families).elimination.resolve_left notRelevant).resolve_left
    notProofTarget

/-- Every fresh slot selected by the actual parser has a source derivation
that its declared domain is Prop. The declaration also fixes restoration. -/
theorem proofField_of_proofReplayEligible
    (origin : NativeDeclarationOrigin env declarations data)
    (eligible : data.proofReplayEligible = true)
    {program : SaturatedProgram data} {U : Nat} {levels : List VLevel}
    {arguments : List VExpr}
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (selected : data.saturatedProgram levels arguments = some program)
    {field : Nat} {domain : VExpr}
    (instruction : program.instructions[field]? = some (.proof domain)) :
    origin.stage.typing.types.HasType U
      (((program.equationBody.domains.take (data.indexOffset + field)).map
        (·.instL levels)).reverse) domain (.sort .zero) := by
  have singleton := origin.singleton_of_proofReplayEligible eligible
  have identity : data.schema.restoration = {} :=
    origin.restoration.trans (origin.selectedCompilation.restoration_of_singleton singleton.1)
  exact data.saturatedProgram_proofField_inst origin.stage.typing.typesWF.ordered
    identity singleton levelsWF selected instruction

end Lean4Lean.VEnv.NativeDeclarationOrigin
