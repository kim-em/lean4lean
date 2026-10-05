import Batteries.Tactic.OpenPrivate
import Lean4Lean.Theory.Typing.AnchoredExposureComparison

/-! Identify the exact fresh telescope of an actual type-display replay.
This is a syntax theorem: typed contraction of the duplicate proof slots
uses the separately constructed chosen copy retraction. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr InductiveSignature.NativeRecursorData
open private lift_pi_shape from Lean4Lean.Theory.Typing.AnchoredExposureComparison

/-- Every successful Pi display at the lifted source has exactly the renamed
original trace front and result. Post-insertions and terminal context
conversions may differ; neither affects this deterministic trace prefix. -/
theorem Exposure.piTrace_renamed
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ Ω Ω' : List VExpr} {expression A B A' B' : VExpr}
    {map map' ρ : Lift}
    (hscoped : registry.Scoped)
    (original : Exposure env U registry Γ expression Ω map (.forallE A B))
    (replayed : Exposure env U registry Δ (expression.lift' ρ) Ω' map' (.forallE A' B')) :
    replayed.added = renameAdded ρ original.added ∧
    replayed.result = original.result.lift' (ρ.consN original.added.length) := by
  obtain ⟨X, Y, originalResult, _, _⟩ := lift_pi_shape original.result_eq
  obtain ⟨X', Y', replayedResult, _, _⟩ := lift_pi_shape replayed.result_eq
  have first := original.trace
  have second := replayed.trace
  rw [originalResult] at first
  rw [replayedResult] at second
  obtain ⟨front, domain, body⟩ := first.pi_unique_renamed hscoped ρ second
  refine ⟨front.symm, ?_⟩
  rw [replayedResult, originalResult]
  simp only [lift', domain, body]

end Lean4Lean.AnchoredSemantics
