import Lean4Lean.Theory.Typing.AnchoredOriginalRichComputationalBudgets

/-! A delta head spends every caller control which selects its name. These
lemmas keep all controls on the same children and reconstructed observation;
no quiet-head premise is needed. A spent zero budget cannot fund a new head:
the input observation supplies the necessary positive-fuel evidence. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096

namespace Budgeted

/-- Spend one unit in every control which observes this head. -/
def spend (name : Name) (budgets : Budgets) : Budgets :=
  budgets.map fun (current, fuel) => (current, fuel - if current name then 1 else 0)

/-- Retained evidence that every selected head can be rebuilt. -/
def HeadPaid (name : Name) (budgets : Budgets) : Prop :=
  ∀ current fuel, (current, fuel) ∈ budgets → (if current name then 1 else 0) ≤ fuel

@[simp] theorem spend_cons (name : Name) (current : Name → Bool) (fuel : Nat) (budgets : Budgets) :
    spend name ((current, fuel) :: budgets) =
      (current, fuel - if current name then 1 else 0) :: spend name budgets := rfl

/-- Simultaneous descent to both stored children of a named delta head. -/
theorem Within.spendDelta {budgets : Budgets} {name : Name}
    {body certificate : (Name → Bool) → Nat}
    (bounded : Within budgets fun current =>
      max (body current) (certificate current) + if current name then 1 else 0) :
    HeadPaid name budgets ∧ Within (spend name budgets) body ∧
      Within (spend name budgets) certificate := by
  refine ⟨?_, ?_, ?_⟩
  · intro current fuel member
    have bound := bounded current fuel member
    exact Nat.le_trans (Nat.le_add_left _ _) bound
  · intro current fuel member
    obtain ⟨⟨filter, original⟩, originalMember, equal⟩ := List.mem_map.mp member
    cases equal
    have bound := bounded current original originalMember
    change max (body current) (certificate current) + (if current name then 1 else 0) ≤ original at bound
    have lower := Nat.le_max_left (body current) (certificate current)
    change body current ≤ original - (if current name then 1 else 0)
    omega
  · intro current fuel member
    obtain ⟨⟨filter, original⟩, originalMember, equal⟩ := List.mem_map.mp member
    cases equal
    have bound := bounded current original originalMember
    change max (body current) (certificate current) + (if current name then 1 else 0) ≤ original at bound
    have lower := Nat.le_max_right (body current) (certificate current)
    change certificate current ≤ original - (if current name then 1 else 0)
    omega

/-- Rebuild the head after both recursive outputs preserve the spent list.
`paid` is obtained from the input head, rather than assumed from subtraction. -/
theorem Within.rebuildDelta {budgets : Budgets} {name : Name}
    {body certificate : (Name → Bool) → Nat}
    (paid : HeadPaid name budgets)
    (bodyBound : Within (spend name budgets) body)
    (certificateBound : Within (spend name budgets) certificate) :
    Within budgets fun current =>
      max (body current) (certificate current) + if current name then 1 else 0 := by
  intro current fuel member
  have selected : (current, fuel - if current name then 1 else 0) ∈ spend name budgets :=
    List.mem_map.mpr ⟨(current, fuel), member, rfl⟩
  have bodyLe := bodyBound current _ selected
  have certificateLe := certificateBound current _ selected
  have headLe := paid current fuel member
  exact Nat.le_trans (Nat.add_le_add_right (Nat.max_le.mpr ⟨bodyLe, certificateLe⟩) _)
    (by omega)

/-- The active control strictly decreases; all other controls are spent in
parallel, including any caller control selecting the same definition. -/
theorem spend_active (name : Name) (current : Name → Bool) (fuel : Nat) (budgets : Budgets)
    (active : current name = true) :
    spend name ((current, fuel + 1) :: budgets) = (current, fuel) :: spend name budgets := by
  simp only [spend_cons, active, ↓reduceIte, Nat.add_sub_cancel]

end Budgeted

end Lean4Lean.AnchoredSource.Adapted
