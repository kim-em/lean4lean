import Lean4Lean.Theory.Typing.AnchoredMinimalPiCompose

/-! Universe displays compose through the actual deterministic trace of the
middle expression. Agreement of exposed levels is obtained syntactically;
no sort uniqueness or equality-foundation theorem is used. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

private theorem lift_sort_shape {expression : VExpr} {ρ : Lift} {u : VLevel}
    (h : expression.lift' ρ = .sort u) : expression = .sort u := by
  cases expression <;> simp only [lift'] at h <;> try contradiction
  exact h

theorem Exposure.sameSort
    {Γ Δ₁ Δ₂ : List VExpr} {expression : VExpr} {u v : VLevel} {ρ₁ ρ₂ : Lift}
    (first : Exposure env U registry Γ expression Δ₁ ρ₁ (.sort u))
    (second : Exposure env U registry Γ expression Δ₂ ρ₂ (.sort v))
    (henv : env.Ordered) :
    ∃ Ω i j, MixedInsertion env U Δ₁ Ω i ∧ MixedInsertion env U Δ₂ Ω j ∧
      ρ₁.comp i = ρ₂.comp j ∧ u = v := by
  have hfirst := lift_sort_shape first.result_eq
  have hsecond := lift_sort_shape second.result_eq
  have tfirst := first.trace
  have tsecond := second.trace
  rw [hfirst] at tfirst
  rw [hsecond] at tsecond
  obtain ⟨hadded, hlevels⟩ := tfirst.sort_unique tsecond
  have secondPost := second.post
  rw [← hadded] at secondPost
  obtain ⟨Ω, j, i, hj, hi, hmaps⟩ := first.post.pushoutProof secondPost henv
  have leftLeg : MixedInsertion env U Δ₁ Ω i := by
    simpa only [Lift.refl_comp] using MixedInsertion.comp
      (.context (first.terminal.symm henv)) (.proof hi)
  have rightLeg : MixedInsertion env U Δ₂ Ω j := by
    simpa only [Lift.refl_comp] using MixedInsertion.comp
      (.context (second.terminal.symm henv)) (.proof hj)
  refine ⟨Ω, i, j, leftLeg, rightLeg, ?_, hlevels⟩
  rw [← first.map_eq, ← second.map_eq, ← hadded,
    Lift.comp_assoc, Lift.comp_assoc, hmaps]

theorem SortRelated.symm
    (h : SortRelated env U registry Γ left right relevant) :
    SortRelated env U registry Γ right left relevant := by
  obtain ⟨Δ, ρ, u, v, hl, hr, huv, hu⟩ := h
  refine ⟨Δ, ρ, v, u, hr, hl, huv.symm, ?_⟩
  cases relevant with
  | false => exact huv.symm.trans hu
  | true => exact fun hv => hu (huv.trans hv)

theorem SortRelated.compose
    (henv : env.Ordered)
    (first : SortRelated env U registry Γ left middle relevant)
    (second : SortRelated env U registry Γ middle right otherRelevant) :
    SortRelated env U registry Γ left right relevant := by
  obtain ⟨Δ₁, ρ₁, u, v, ⟨hl⟩, ⟨hm₁⟩, huv, hu⟩ := first
  obtain ⟨Δ₂, ρ₂, v', w, ⟨hm₂⟩, ⟨hr⟩, hvw, _⟩ := second
  obtain ⟨Ω, i, j, hi, hj, hmaps, rfl⟩ := hm₁.sameSort hm₂ henv
  refine ⟨Ω, ρ₁.comp i, u, w, ⟨hl.postMixed henv hi⟩, ?_, huv.trans hvw, hu⟩
  rw [hmaps]
  exact ⟨hr.postMixed henv hj⟩

end Lean4Lean.AnchoredSemantics
