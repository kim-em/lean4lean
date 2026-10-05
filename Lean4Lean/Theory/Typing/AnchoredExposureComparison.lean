import Lean4Lean.Theory.Typing.AnchoredSemantics

/-! Compare the actual Pi displays used by anchored semantic capabilities.
Canonical traces start at the same expression, so they agree before either
post-insertion. Their post-insertions then have a common source and can be
amalgamated using their generated proof histories. No type inversion or
retraction of private display components is used.
-/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv

private theorem lift_comp_assoc (ρ τ υ : Lift) :
    (ρ.comp τ).comp υ = ρ.comp (τ.comp υ) := by
  induction υ generalizing ρ τ with
  | refl => rfl
  | skip υ ih => simp only [Lift.comp, ih]
  | cons υ ih =>
    cases τ with
    | refl => cases ρ <;> simp only [Lift.comp]
    | skip τ => simp only [Lift.comp, ih]
    | cons τ => cases ρ <;> simp only [Lift.comp, ih]

private theorem lift_pi_shape {expression A B : VExpr} {ρ : Lift}
    (h : expression.lift' ρ = .forallE A B) :
    ∃ X Y, expression = .forallE X Y ∧ X.lift' ρ = A ∧ Y.lift' ρ.cons = B := by
  cases expression <;> simp only [lift'] at h
  all_goals try contradiction
  case forallE X Y =>
    obtain ⟨hX, hY⟩ := VExpr.forallE.inj h
    exact ⟨X, Y, rfl, hX, hY⟩

/-- Independent exposures have literally equal Pi components after mixed
transport into one common context. The legs first undo terminal context
conversions, then use the actual generated insertion pushout. -/
theorem Exposure.samePi
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ₁ Δ₂ : List VExpr} {expression A₁ B₁ A₂ B₂ : VExpr} {ρ₁ ρ₂ : Lift}
    (left : Exposure env U registry Γ expression Δ₁ ρ₁ (.forallE A₁ B₁))
    (right : Exposure env U registry Γ expression Δ₂ ρ₂ (.forallE A₂ B₂))
    (henv : env.Ordered) :
    ∃ Ω i j,
      MixedInsertion env U Δ₁ Ω i ∧ MixedInsertion env U Δ₂ Ω j ∧
      ρ₁.comp i = ρ₂.comp j ∧
      A₁.lift' i = A₂.lift' j ∧ B₁.lift' i.cons = B₂.lift' j.cons := by
  obtain ⟨X₁, Y₁, hresult₁, hA₁, hB₁⟩ := lift_pi_shape left.result_eq
  obtain ⟨X₂, Y₂, hresult₂, hA₂, hB₂⟩ := lift_pi_shape right.result_eq
  have htrace₁ := left.trace
  have htrace₂ := right.trace
  rw [hresult₁] at htrace₁
  rw [hresult₂] at htrace₂
  obtain ⟨hadded, hX, hY⟩ := htrace₁.pi_unique htrace₂
  have hpost := right.post
  rw [← hadded] at hpost
  obtain ⟨Ω, j, i, hj, hi, hmaps⟩ := left.post.pushoutProof hpost henv
  have leftLeg : MixedInsertion env U Δ₁ Ω i := by
    simpa only [Lift.refl_comp] using MixedInsertion.comp
      (.context (left.terminal.symm henv)) (.proof hi)
  have rightLeg : MixedInsertion env U Δ₂ Ω j := by
    simpa only [Lift.refl_comp] using MixedInsertion.comp
      (.context (right.terminal.symm henv)) (.proof hj)
  refine ⟨Ω, i, j, leftLeg, rightLeg, ?_, ?_, ?_⟩
  · rw [← left.map_eq, ← right.map_eq, ← hadded,
      lift_comp_assoc, lift_comp_assoc, hmaps]
  · rw [← hA₁, ← hA₂, ← lift'_comp, ← lift'_comp, hX, hmaps]
  · rw [← hB₁, ← hB₂, ← lift'_comp, ← lift'_comp, hY]
    exact congrArg (Y₂.lift' ·) (congrArg Lift.cons hmaps)

end Lean4Lean.AnchoredSemantics
