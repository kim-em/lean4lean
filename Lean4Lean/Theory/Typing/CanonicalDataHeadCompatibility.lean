import Lean4Lean.Theory.Typing.CanonicalDataHeadTrace

/-! Concrete compatibility of the extended machine with existing beta,
delta and singleton producers. These are trace embeddings, not an assumed
head-machine interface. -/
namespace Lean4Lean.CanonicalDataHead
open VExpr InductiveSignature.NativeRecursorData

theorem step_of_legacy (selected : CanonicalHead.step registry.toRegistry expression = some out) :
    step registry expression = some out := by
  cases expression <;> simp only [step, selected]

theorem Trace.ofLegacy
    (trace : CanonicalHead.Trace registry.toRegistry expression added result) :
    Trace registry expression added result := by
  induction trace with
  | refl => exact .refl
  | next step _ ih => exact .next (step_of_legacy step) ih

theorem step_pi (registry : Registry) (A B : VExpr) :
    step registry (.forallE A B) = none := by
  simp only [step, CanonicalHead.step_pi]

theorem step_sort (registry : Registry) (level : VLevel) :
    step registry (.sort level) = none := by
  simp only [step, CanonicalHead.step_sort]

theorem Trace.pi_unique
    (first : Trace registry expression added (.forallE A B))
    (second : Trace registry expression added' (.forallE A' B')) :
    added = added' ∧ A = A' ∧ B = B' := by
  obtain ⟨sameAdded, sameHead⟩ := first.terminal_unique second (step_pi ..) (step_pi ..)
  cases sameHead
  exact ⟨sameAdded, rfl, rfl⟩

theorem Trace.sort_unique
    (first : Trace registry expression added (.sort u))
    (second : Trace registry expression added' (.sort v)) : added = added' ∧ u = v := by
  obtain ⟨sameAdded, sameHead⟩ := first.terminal_unique second (step_sort ..) (step_sort ..)
  cases sameHead
  exact ⟨sameAdded, rfl⟩

theorem Trace.pi_unique_renamed (scope : registry.Scoped)
    (first : Trace registry expression added (.forallE A B)) (ρ : Lift)
    (second : Trace registry (expression.lift' ρ) added' (.forallE A' B')) :
    renameAdded ρ added = added' ∧ A.lift' (ρ.consN added.length) = A' ∧
      B.lift' (ρ.consN added.length).cons = B' :=
  (first.rename scope ρ).pi_unique second

end Lean4Lean.CanonicalDataHead
