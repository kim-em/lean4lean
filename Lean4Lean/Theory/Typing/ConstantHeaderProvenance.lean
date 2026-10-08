import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.EnvLemmas

/-! Original formation stages for all constant headers.

A constant's closed type was checked before its own fresh installation. This
also covers the family and constructor prefixes within one inductive declaration,
where the length of the declaration list is not a decreasing measure. The finite
constant domain gives a strict measure at every such header edge.
-/
namespace Lean4Lean.VEnv
variable {env : VEnv}

namespace ConstantDomain

variable {env extended : VEnv}

end ConstantDomain

namespace ConstantHeaderOrigin
variable {env extended : VEnv} {name : Name} {value : VConstant}

end ConstantHeaderOrigin

/-- No lookup can appear except from the old environment or a literal
member of the installed block. -/
theorem addConstVals_lookup_origin {base extended : VEnv}
    (installed : base.addConstVals values = some extended)
    (lookup : extended.constants name = some value) :
    base.constants name = some value ∨
      ∃ entry ∈ values, entry.name = name ∧ entry.toVConstant = value := by
  induction values generalizing base with
  | nil => cases installed; exact Or.inl lookup
  | cons entry entries ih =>
    simp only [addConstVals, Option.bind_eq_bind, Option.bind_eq_some_iff] at installed
    obtain ⟨middle, first, rest⟩ := installed
    rcases ih rest with old | added
    · rw [VEnv.addConst_constants_eq first] at old
      dsimp only at old
      by_cases same : entry.name = name
      · simp only [same, ite_true, Option.some.injEq] at old
        exact Or.inr ⟨entry, List.mem_cons_self, same, old⟩
      · exact Or.inl (by simpa only [same, ite_false] using old)
    · obtain ⟨selected, member, sameName, sameValue⟩ := added
      exact Or.inr ⟨selected, List.mem_cons_of_mem _ member, sameName, sameValue⟩

end Lean4Lean.VEnv
