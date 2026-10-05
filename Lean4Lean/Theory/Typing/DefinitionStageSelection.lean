import Lean4Lean.Theory.Typing.DefinitionDeclarationProvenance

/-! Selecting a different member retains the literal original mutual header,
all original body proofs, and the installed declaration position. -/
namespace Lean4Lean.VEnv.DefinitionTypingStage
variable {base installed : VEnv} {declaration : VDecl} {value selected : VDefVal}

def select (stage : DefinitionTypingStage base declaration installed value)
    (member : selected ∈ stage.values) : DefinitionTypingStage base declaration installed selected := by
  cases stage with
  | single body headers =>
    have same := List.mem_singleton.mp member
    subst selected
    exact .single body headers
  | mutualBlock types headers bodies _ => exact .mutualBlock types headers bodies member

@[simp] theorem select_header (stage : DefinitionTypingStage base declaration installed value)
    (member : selected ∈ stage.values) : (stage.select member).header = stage.header := by
  cases stage with
  | single body headers =>
    have same := List.mem_singleton.mp member
    subst selected
    rfl
  | mutualBlock => rfl

@[simp] theorem select_values (stage : DefinitionTypingStage base declaration installed value)
    (member : selected ∈ stage.values) : (stage.select member).values = stage.values := by
  cases stage with
  | single body headers =>
    have same := List.mem_singleton.mp member
    subst selected
    rfl
  | mutualBlock => rfl
end Lean4Lean.VEnv.DefinitionTypingStage
