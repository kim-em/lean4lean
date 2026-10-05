import Lean4Lean.Theory.Typing.AnchoredGeneralGradedAdapters

/-! General function adapters expose the retained directional key program.
Code leaves cannot create a function demand because their outputs are sortable. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

noncomputable def GeneralKeyProgram.arguments {old new : Key n}
    (program : GeneralKeyProgram env U registry Γ old new) :
    GeneralProfileAdapter env U registry Γ new.input old.input := by
  match program with
  | .refl key => exact .refl key.input
  | .input _ arguments => exact arguments
  | .reanchor _ => exact .refl _
  | .domainRekey _ _ _ _ => exact .refl _
  | .comp first second => exact second.arguments.comp first.arguments
termination_by sizeOf program

theorem GeneralAtomAdapter.fn_inv {atom : Atom (n + 1)} {key : Key n} {output : Atom n}
    (adapter : GeneralAtomAdapter env U registry Γ atom (.fn key output)) :
    ∃ sourceKey sourceOutput,
      atom = .fn sourceKey sourceOutput ∧
      Nonempty (GeneralKeyProgram env U registry Γ sourceKey key) ∧
      Nonempty (GeneralAtomAdapter env U registry Γ sourceOutput output) := by
  cases adapter with
  | refl => exact ⟨key, output, rfl, ⟨.refl _⟩, ⟨.refl _⟩⟩
  | fn keys result => exact ⟨_, _, rfl, ⟨keys⟩, ⟨result⟩⟩
  | code action formed =>
    have sorted := action.preservesSort formed
    obtain ⟨cover, member, impossible⟩ := sorted.2.2 _ (List.mem_singleton_self _)
    cases List.mem_singleton.mp member
    contradiction

noncomputable def GeneralAtomAdapter.extendInput {key : Key n} {output : Atom n} {input : Profile n}
    (seed : AdapterSeed env U registry Γ key input)
    (included : List.Subset key.input input) :
    GeneralAtomAdapter env U registry Γ (n := n + 1)
      (.fn key output) (.fn (inputKey key input) output) :=
  .fn (.input seed (.select included)) (.refl output)

def GeneralAtomAdapter.fnOutput (key : Key n) {output output' : Atom n}
    (result : GeneralAtomAdapter env U registry Γ output output') :
    GeneralAtomAdapter env U registry Γ (n := n + 1) (.fn key output) (.fn key output') :=
  .fn (.refl key) result

end Lean4Lean.AnchoredSemantics
