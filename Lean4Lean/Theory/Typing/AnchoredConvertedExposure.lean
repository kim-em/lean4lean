import Lean4Lean.Theory.Typing.AnchoredMixedTransport
import Lean4Lean.Theory.Typing.AnchoredCodeTransitivity

/-! The concrete dependent-row composition consumer for the production
terminal-converted Exposure representation. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

/-- The precise lower-rank transitivity consumer after mixed display
comparison. There is no demand for a literal insertion from converted
contexts and no semantic interpretation of a new typing derivation. -/
theorem RowCapabilities.transMixed
    (henv : env.Ordered)
    (leftPath : MixedInsertion env U Γ₁ Ω i)
    (rightPath : MixedInsertion env U Γ₂ Ω j)
    (keys : key₁.rename i = key₂.rename j)
    (results : result₁.rename i = result₂.rename j)
    (middle : middle₁.lift' i.cons = middle₂.lift' j.cons)
    (first : RowCapabilities env U registry Γ₁ key₁ left middle₁ result₁)
    (second : RowCapabilities env U registry Γ₂ key₂ middle₂ right result₂) :
    RowCapabilities env U registry Ω (key₁.rename i)
      (left.lift' i.cons) (right.lift' j.cons) (result₁.rename i) := by
  have first' := leftPath.rowCapabilities henv first
  have second' := rightPath.rowCapabilities henv second
  rw [← keys, ← results, ← middle] at second'
  intro Δ ρ future x y admitted
  obtain ⟨leftSelf, _, firstCross⟩ := first' Δ ρ future x y admitted
  obtain ⟨_, rightSelf, secondCross⟩ := second' Δ ρ future x y admitted
  exact ⟨leftSelf, rightSelf, firstCross.trans henv secondCross⟩

end Lean4Lean.AnchoredSemantics
