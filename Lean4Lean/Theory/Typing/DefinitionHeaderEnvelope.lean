import Lean4Lean.Theory.Typing.DefinitionOuterStage

/-! Header saturation is an environment fact, independent of semantic
interpretation. A mutual definition's actual body source fits an envelope
exactly when that envelope contains the complete original header block. -/
namespace Lean4Lean.VEnv
set_option Elab.async false

private theorem addConst_le_envelope
    {base header envelope : VEnv}
    (installed : base.addConst name value = some header)
    (previous : base ≤ envelope)
    (present : envelope.constants name = some value) : header ≤ envelope := by
  unfold VEnv.addConst at installed
  split at installed <;> cases installed
  refine ⟨?_, previous.defeqs, previous.projections, previous.eliminators⟩
  intro selected constant member
  dsimp only at member
  split at member
  · rename_i same
    cases same
    exact Option.some.inj member ▸ present
  · exact previous.constants member

/-- A whole block may be borrowed by any smaller original endpoint, provided
its surrounding envelope contains every original member of that block. -/
theorem addConsts_le_envelope
    {base header envelope : VEnv} {values : List VDefVal}
    (installed : base.addConsts values = some header)
    (previous : base ≤ envelope)
    (members : ∀ value ∈ values, envelope.constants value.name = some value.toVConstant) :
    header ≤ envelope := by
  induction values generalizing base with
  | nil => cases installed; exact previous
  | cons value values ih =>
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at installed
    obtain ⟨next, first, rest⟩ := installed
    exact ih rest (addConst_le_envelope first previous (members _ List.mem_cons_self))
      (fun _ member => members _ (List.mem_cons_of_mem _ member))

namespace DefinitionTypingStage

/-- Unlike an arbitrary constant prefix, a saturated phase contains the
actual source used to check all mutually recursive bodies. -/
theorem header_le_iff
    (stage : DefinitionTypingStage base declaration installed value)
    (previous : base ≤ envelope) :
    stage.header ≤ envelope ↔
      ∀ member ∈ stage.values, envelope.constants member.name = some member.toVConstant := by
  constructor
  · intro below member present
    exact below.constants (VEnv.addConsts_constants stage.headers member present)
  · exact VEnv.addConsts_le_envelope stage.headers previous

/-- An internal prefix missing even one sibling cannot host this retained
body source, even if the queried definition's own name is already installed. -/
theorem header_not_le_of_missing
    (stage : DefinitionTypingStage base declaration installed value)
    (member : sibling ∈ stage.values)
    (missing : prefixEnv.constants sibling.name = none) :
    ¬ stage.header ≤ prefixEnv := by
  intro below
  have present := below.constants (VEnv.addConsts_constants stage.headers sibling member)
  rw [missing] at present
  cases present

end DefinitionTypingStage
end Lean4Lean.VEnv
