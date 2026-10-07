import Lean4Lean.Theory.Typing.SingletonExtraction
import Lean4Lean.Theory.Typing.LevelEquiv

/-! # Moving telescope instances between related telescopes

Arguments typed along a closed telescope are typed along any telescope that is pointwise
definitionally equal to it in the prefix contexts (`IsDefEqCtx` over the empty context), or
pointwise level-equivalent to it. -/

namespace Lean4Lean.VEnv
open VExpr

variable {env : VEnv} {U : Nat}

theorem IsDefEqCtx.instL (hls : ∀ l ∈ ls, l.WF U) :
    IsDefEqCtx env U' [] Γ₁ Γ₂ →
      IsDefEqCtx env U [] (Γ₁.map (·.instL ls)) (Γ₂.map (·.instL ls))
  | .zero => .zero
  | .succ h1 h2 => .succ (IsDefEqCtx.instL hls h1) (by simpa [VExpr.instL] using h2.instL hls)

/-- An `IsDefEqCtx` over reversed telescopes, split at the last binder. -/
theorem IsDefEqCtx.snoc_inv
    (H : IsDefEqCtx env U [] (A ++ [a]).reverse (B ++ [b]).reverse) :
    IsDefEqCtx env U [] A.reverse B.reverse ∧ ∃ u, env.IsDefEq U A.reverse a b (.sort u) := by
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append] at H
  cases H with
  | succ h1 h2 => exact ⟨h1, _, h2⟩

theorem TelInst.of_ctxDefEq (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {A B args : List VExpr}, TelInst env U Γ A args →
      IsDefEqCtx env U [] A.reverse B.reverse → TelInst env U Γ B args := by
  intro A
  induction A using VEnv.snoc_induction with
  | nil =>
    intro B args H hAB
    have := hAB.length_eq
    simp at this
    have hB : B = [] := List.eq_nil_of_length_eq_zero (by simpa using this.symm)
    subst hB; exact H
  | snoc A a ih =>
    intro B args H hAB
    obtain ⟨Bs, b, rfl⟩ : ∃ Bs b, B = Bs ++ [b] := by
      rcases List.eq_nil_or_concat B with h | ⟨Bs, b, h⟩
      · subst h; have := hAB.length_eq; simp at this
      · exact ⟨Bs, b, by simpa using h⟩
    obtain ⟨as, x, rfl⟩ : ∃ as x, args = as ++ [x] := by
      rcases List.eq_nil_or_concat args with h | ⟨as, x, h⟩
      · subst h; have := H.1; simp at this
      · exact ⟨as, x, by simpa using h⟩
    obtain ⟨hAB', u, hab⟩ := hAB.snoc_inv
    have hl : as.length = A.length := by have := H.1; simp at this; omega
    have hA : TelInst env U Γ A as := by
      have := H.take
      rwa [List.take_left' hl] at this
    have hB := ih hA hAB'
    refine TelInst.append_one hB ?_
    have hx := H.2 A.length (by simp; omega) (by simp)
    rw [List.getElem_append_right (by omega), List.getElem_append_right (by simp)] at hx
    simp only [hl, Nat.sub_self, List.getElem_singleton, List.take_left' hl] at hx
    have hΔ : OnCtx A.reverse (env.IsType U) := hAB'.isType
    have := IsDefEq.closed_instOuter_congr henv hΓ hΔ hab hA.1 hA.1
      (fun j hj _ hd => hA.2 j hj hd)
    simp only [VExpr.instOuter_sort] at this
    exact .defeqDF this hx

theorem TelInst.of_lequiv (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {A B args : List VExpr}, TelInst env U Γ A args →
      List.Forall₂ (VExpr.LEquiv U) A B → TelInst env U Γ B args := by
  intro A B args H hAB
  have hlen := List.Forall₂.length_eq hAB
  refine ⟨H.1.trans hlen, fun j hj hj' => ?_⟩
  have hjA : j < A.length := by omega
  have hx := H.2 j hj hjA
  have hL : VExpr.LEquiv U A[j] B[j] := by
    exact Lean4Lean.List.forall₂_getElem hAB j hjA hj'
  have hdef := (hL.instOuter (args.take j)).defeq henv hΓ
    (hx.isType henv.ordered hΓ |>.elim fun _ h => ⟨_, h⟩)
  exact hx.defeqU_r henv hΓ hdef

end Lean4Lean.VEnv
