import Lean4Lean.Theory.Inductive.SaturatedNativeRenaming
import Lean4Lean.Theory.Typing.NativeRuleRegistration

/-! Scope and syntax transport at an actually registered native head.

The declaration history supplies the scopes used by the pure capture program.
Consequently a successful program on renamed arguments has a program on the
original arguments, with the same declared proof slots. This is the syntax
part of removing a preliminary proof frame from a head trace. Typed guards
must still be pulled back using the frame's actual typed retraction.
-/

namespace Lean4Lean.VEnv
open VExpr InductiveSignature NativeRecursorData

variable {env : VEnv} {data : NativeRecursorData} {equation : VDefEq}
  {levels : List VLevel} {arguments : List VExpr}
  {program : SaturatedProgram data}

private theorem singleton_rhs_closed (henv : env.WF)
    (H : NativeRecursorRegistered env data)
    (hequation : data.singletonEquation = some equation) : equation.rhs.Closed := by
  unfold NativeRecursorData.singletonEquation at hequation
  dsimp only at hequation
  split at hequation <;> try contradiction
  exact (H.equation_closed henv hequation).2.1

/-- The scope assumptions for capture transport come from the actual
registered equation, not an extra assumption about its generated open body. -/
theorem NativeRecursorRegistered.saturatedProgram_rename
    (henv : env.WF) (H : NativeRecursorRegistered env data)
    (h : data.saturatedProgram levels arguments = some program) (ρ : Lift) :
    data.saturatedProgram levels (arguments.map (·.lift' ρ)) = some (program.rename ρ) ∧
    (program.rename ρ).state.added = renameAdded ρ program.state.added ∧
    (program.rename ρ).state.captures =
      program.state.captures.map (·.lift' (ρ.consN program.state.added.length)) ∧
    (program.rename ρ).result = program.result.lift' (ρ.consN program.state.added.length) := by
  obtain ⟨_, _, _, _, _, _, _, _, hequation, _, _, _, _, _⟩ := saturatedProgram_spec h
  exact saturatedProgram_rename_of_closed_rhs h
    ((singleton_rhs_closed henv H hequation).instL (ls := levels)) ρ

/-- A renamed successful execution cannot hide a missing base execution.
This uses total parser naturality and retains every fresh proof binder; it
does not strengthen an arbitrary typing derivation out of its context. -/
theorem NativeRecursorRegistered.saturatedProgram_pullback
    (henv : env.WF) (H : NativeRecursorRegistered env data) (ρ : Lift)
    (h : data.saturatedProgram levels (arguments.map (·.lift' ρ)) = some program) :
    ∃ original : SaturatedProgram data,
      data.saturatedProgram levels arguments = some original ∧
      program = original.rename ρ ∧
      program.result = original.result.lift' (ρ.consN original.state.added.length) := by
  obtain ⟨_, _, _, _, _, _, _, _, hequation, hbody, _, _, _, _⟩ := saturatedProgram_spec h
  have hs := (scope_of_extract hbody (singleton_rhs_closed henv H hequation)).1
  rw [saturatedProgram_rename_eq hequation hbody hs levels arguments ρ] at h
  obtain ⟨original, horiginal, hrename⟩ := Option.map_eq_some_iff.mp h
  have hr := (H.saturatedProgram_rename henv horiginal ρ).2.2.2
  exact ⟨original, horiginal, hrename.symm, hrename ▸ hr⟩

end Lean4Lean.VEnv
