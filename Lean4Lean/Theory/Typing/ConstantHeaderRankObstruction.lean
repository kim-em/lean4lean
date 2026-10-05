import Lean4Lean.Theory.Typing.ConstantHeaderProvenance

/-! Borrowed constant origins do not induce an environment-only strict rank.
Two independent, well-formed constants admit crossed original header sources.
This obstructs that rank interface, not source-query interpretation: the
sort-shaped children in this example cannot themselves observe the other head. -/
namespace Lean4Lean.VEnv
set_option Elab.async false

namespace CrossedHeaders

def value : VConstant := ⟨0, .sort .zero⟩
def one (name : Name) : VEnv where
  constants selected := if name = selected then some value else none
  defeqs _ := False

def both (first second : Name) : VEnv where
  constants selected := if first = selected ∨ second = selected then some value else none
  defeqs _ := False

theorem value_wf (env : VEnv) : value.WF env :=
  ⟨.succ .zero, .sortDF trivial trivial rfl⟩

theorem one_ordered (name : Name) : (one name).Ordered :=
  .const .empty (value_wf _) rfl

theorem one_wf (name : Name) : (one name).WF := by
  let constant : VConstVal := { name := name, uvars := 0, type := .sort .zero }
  exact ⟨[.axiom constant], .decl (.axiom (value_wf _) rfl) .empty⟩

theorem install_second (first second : Name) (distinct : first ≠ second) :
    (one first).addConst second value = some (both first second) := by
  simp only [VEnv.addConst, one, if_neg distinct]
  apply congrArg some
  apply VEnv.ext
  · funext selected
    by_cases left : first = selected <;> by_cases right : second = selected <;>
      simp [both, left, right]
  · rfl
  · rfl
  · rfl

theorem both_wf (first second : Name) (distinct : first ≠ second) :
    (both first second).WF := by
  obtain ⟨declarations, history⟩ := one_wf first
  let constant : VConstVal := { name := second, uvars := 0, type := .sort .zero }
  exact ⟨.axiom constant :: declarations,
    .decl (.axiom (value_wf _) (install_second first second distinct)) history⟩

theorem one_below_left (first second : Name) : one first ≤ both first second := by
  refine ⟨?_, False.elim, False.elim, False.elim⟩
  intro selected constant lookup
  simp only [one] at lookup
  split at lookup
  · rename_i same
    cases same
    simpa only [both, true_or, ↓reduceIte] using lookup
  · cases lookup

theorem one_below_right (first second : Name) : one second ≤ both first second := by
  refine ⟨?_, False.elim, False.elim, False.elim⟩
  intro selected constant lookup
  simp only [one] at lookup
  split at lookup
  · rename_i same
    cases same
    simpa only [both, or_true, ↓reduceIte] using lookup
  · cases lookup

def firstOrigin (first second : Name) (distinct : first ≠ second) :
    ConstantHeaderOrigin (both first second) first value where
  source := one second
  ordered := one_ordered second
  formation := value_wf _
  sourceBelow := one_below_right first second
  fresh := by simp [one, Ne.symm distinct]
  constant := by simp [both]

def secondOrigin (first second : Name) (distinct : first ≠ second) :
    ConstantHeaderOrigin (both first second) second value where
  source := one first
  ordered := one_ordered first
  formation := value_wf _
  sourceBelow := one_below_left first second
  fresh := by simp [one, distinct]
  constant := by simp [both]

/-- No natural rank can justify all borrowed header openings merely from
ambient provenance and availability of the head in the caller's source. -/
theorem no_borrowed_header_rank (first second : Name) (distinct : first ≠ second) :
    ¬ ∃ rank : VEnv → Nat,
      ∀ {name info} (origin : ConstantHeaderOrigin (both first second) name info)
        {source : VEnv}, source.Ordered → source ≤ both first second →
        source.constants name = some info → rank origin.source < rank source := by
  rintro ⟨rank, decrease⟩
  have firstStep := decrease (firstOrigin first second distinct)
    (one_ordered first) (one_below_left first second) (by simp [one])
  have secondStep := decrease (secondOrigin first second distinct)
    (one_ordered second) (one_below_right first second) (by simp [one])
  change rank (one second) < rank (one first) at firstStep
  change rank (one first) < rank (one second) at secondStep
  exact Nat.lt_irrefl _ (Nat.lt_trans firstStep secondStep)

end CrossedHeaders
end Lean4Lean.VEnv
