import Lean4Lean.Theory.Typing.ShapeModel.RuleValidMatch

/-!
# Rules whose type is a proposition

A computation rule whose motive eliminates into `Sort 0` (at the instance) has both sides proofs:
the type of the left body is the motive applied to the indices and the major, and the motive's
key is typed at an approximation of a telescope ending in the zero sort, so every approximation of
the motive applied to arguments is below a proposition shape, and everything typed at it is
bottom (`Interp.mkApps_bvar_prop`). Both bodies then have only bottom approximations
(`bodies_bot_of_prop`).
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv} [SemSig] [SemSig.Coherent]

/-- A key of a telescope valuation is typed at an approximation of its domain, under the
valuation of the earlier keys. -/
theorem KeysFit.lookup {Ds : List VExpr} (K : KeysFit env ρ Ds σ) :
    ∀ i (hi : i < Ds.length), ∃ ρ' a, (σ (Ds.length - 1 - i)).HasType a ∧
      Interp env ρ' a Ds[i] := by
  induction K with
  | nil => intro i hi; cases hi
  | @cons ρ D Ds σ a x ha hx K ih =>
    intro i hi
    have hlen : ∀ {Ds : List VExpr} {ρ σ : Valuation}, KeysFit env ρ Ds σ →
        ∀ j, σ (Ds.length + j) = ρ j := by
      intro Ds ρ σ K
      induction K with
      | nil => intro j; simp
      | @cons ρ D Ds σ a x _ _ _ ih =>
        intro j
        rw [List.length_cons, show Ds.length + 1 + j = Ds.length + (j + 1) by omega, ih]
        rfl
    cases i with
    | zero =>
      refine ⟨ρ, a, ?_, ha⟩
      rw [show (D :: Ds).length - 1 - 0 = Ds.length + 0 by simp, hlen K]
      exact hx
    | succ i =>
      obtain ⟨ρ', a', h1, h2⟩ := ih i (by simpa using hi)
      refine ⟨ρ', a', ?_, by simpa using h2⟩
      rwa [show (D :: Ds).length - 1 - (i + 1) = Ds.length - 1 - i by simp; omega]

/-- The invariant of an application of a key typed at a telescope ending in a sort. -/
def TypedAt (env : VEnv) [SemSig] (t : TShape) (B : VExpr) : Prop :=
  t ≤ .bot ∨ ∃ (y z : TShape) (ρ' : Valuation), t ≤ y ∧ y.HasType z ∧ Interp env ρ' z B

theorem TypedAt.app {f : WShape (n+1)} {a : WShape n}
    (H : TypedAt env f.T (.forallE E R)) : TypedAt env (f.app a).T R := by
  rcases H with hb | ⟨y, z, ρ', hfy, hyz, hz⟩
  · left
    have : f = .bot := TShape.le_bot.1 hb
    subst this; rw [WShape.bot_app]; exact TShape.bot_eqv.1
  have hz' : z ≤ .bot ∨ ∃ n₂, ∃ b : WShape n₂, ∃ g : WShapeFun n₂,
      Interp env ρ' (WShape.forallE b g).T (.forallE E R) ∧ z ≤ (WShape.forallE b g).T := by
    cases hz with
    | bot => exact .inl TShape.bot_eqv.1
    | forallE hb hb' hd hg hzle => exact .inr ⟨_, _, _, .forallE hb hb' hd hg .rfl, hzle⟩
  rcases hz' with hzb | ⟨n₂, b, g, hzF, hzle⟩
  · left
    have hy := TShape.HasType.bot_r' hzb hyz
    have : f = .bot := TShape.le_bot.1 (hfy.trans hy)
    subst this; rw [WShape.bot_app]; exact TShape.bot_eqv.1
  cases TShape.LE.le_forall hzle with
  | bot hzb =>
    left
    have hy := TShape.HasType.bot_r' hzb hyz
    have : f = .bot := TShape.le_bot.1 (hfy.trans hy)
    subst this; rw [WShape.bot_app]; exact TShape.bot_eqv.1
  | @forallE m f₁ _ b₁ _ hb₁ hf₁ =>
  rcases TShape.HasType.ty_forallE_inv hyz with rfl | ⟨n₃, h, rfl, hh⟩
  · left
    have : f = .bot := TShape.le_bot.1 (hfy.trans TShape.bot_eqv.1)
    subst this; rw [WShape.bot_app]; exact TShape.bot_eqv.1
  right
  let K := max (max n n₃) (max m n₂)
  have hK := Nat.max_le.1 (Nat.le_refl K); simp only [Nat.max_le] at hK
  have hhK := (TShape.HasTypeLam.def hK.1.2 hK.2.1).1 hh
  let h' := h.lift K
  let a' := a.lift K
  have happ : (f.app a).T ≤ (h'.app a').T := by
    have := TShape.app_mono (f := f) (f' := WShape.lam' h') (a := a) (a' := a')
      (hfy.trans (by
        rw [show WShape.lam' h' = (WShape.lam' h).lift (K+1) from (WShape.lift_lam' hK.1.2).symm]
        exact (TShape.lift_eqv (a := (WShape.lam' h).T) (Nat.succ_le_succ hK.1.2)).2))
      (TShape.lift_eqv (a := a.T) hK.1.1).2
    rwa [WShape.lam'_app] at this
  obtain ⟨x', hx'1, hx'2, hx'3⟩ := WShape.HasDom.iff.1 (WShape.HasTypeLam.iff.1 hhK).2.1 a'
  have hty := (WShape.HasTypeLam.iff.1 hhK).2.2 x' hx'2
  have hfg : f₁.lift K ≤ g.lift K := (TShapeFun.LE.def hK.2.1 hK.2.2).1 hf₁
  have hzF' := hzF.lift (n := K+1) (Nat.succ_le_succ hK.2.2)
  simp only [WShape.T, WShape.lift_forallE hK.2.2] at hzF'
  have hcod := (Interp.forallE_inv' hzF').2 x'
  refine ⟨(h'.app x').T, ((f₁.lift K).app x').T, ρ'.push x'.T, happ.trans hx'3.T, hty.T, ?_⟩
  exact hcod.mono (WShapeFun.app_mono_l hfg x').T

theorem TypedAt.mkApps_bvar_rev {Es : List VExpr} {k : Nat} {B : VExpr}
    (hk : (σ k).HasType a) (ha : Interp env ρ' a (VExpr.wrapForalls Es B)) :
    ∀ {rev : List VExpr}, rev.length ≤ Es.length → ∀ {t},
      Interp env σ t (VExpr.mkApps (.bvar k) rev.reverse) →
      TypedAt env t (VExpr.wrapForalls (Es.drop rev.length) B) := by
  intro rev
  induction rev with
  | nil =>
    intro _ t ht
    exact .inr ⟨σ k, a, ρ', Interp.bvar_iff.1 ht, hk, by simpa using ha⟩
  | cons x as ih =>
    intro hlen t ht
    rw [List.reverse_cons, VExpr.mkApps_append_singleton] at ht
    simp only [List.length_cons] at hlen ⊢
    cases ht with
    | bot => exact .inl TShape.bot_eqv.1
    | app hf _ hle =>
      have h1 := ih (by omega) hf
      have hdrop : Es.drop as.length = Es[as.length] :: Es.drop (as.length + 1) := by
        rw [List.drop_eq_getElem_cons (by omega)]
      rw [hdrop, VExpr.wrapForalls_cons] at h1
      rcases h1.app with hb | ⟨y, z, ρ'', h2, h3, h4⟩
      · exact .inl (hle.trans hb)
      · exact .inr ⟨y, z, ρ'', hle.trans h2, h3, h4⟩

/-- Everything typed at an approximation of a key applied to all arguments of its telescope
ending in the zero sort is bottom. -/
theorem Interp.mkApps_bvar_prop {Es : List VExpr} {k : Nat} {l : VLevel} {m' t : TShape}
    (hk : (σ k).HasType a) (ha : Interp env ρ' a (VExpr.wrapForalls Es (.sort l)))
    (hl : SLvl.IsZero l.eval) (hlen : args.length = Es.length)
    (ht : Interp env σ t (VExpr.mkApps (.bvar k) args)) (hm : m'.HasType t) : m' ≤ .bot := by
  rw [← List.reverse_reverse args] at ht
  have := TypedAt.mkApps_bvar_rev hk ha (rev := args.reverse) (by simp [hlen]) ht
  rw [List.length_reverse, hlen, List.drop_length] at this
  rcases this with hb | ⟨y, z, ρ'', hty, hyz, hz⟩
  · exact TShape.HasType.bot_r' hb hm
  · have hz' := hz.le_sort
    have hy : y.HasType (.sort l.eval) := TShape.HasType.mono_r hz' .sort hyz
    have hm' : m'.HasType y := TShape.HasType.mono_r hty hy hm
    exact TShape.HasType.proofIrrel hl hy hm'

/-- A body whose type is a key (typed at a telescope ending in the zero sort) applied to all
its arguments has only bottom approximations. -/
theorem body_bot_of_motive {Es : List VExpr} {k : Nat} {l : VLevel}
    (W : Valuation.Fits env Γ₀ Δ σ) (hrec : StrongSound env Δ b B)
    (hBT : ∀ m, Interp env σ m B → Interp env σ m (VExpr.mkApps (.bvar k) args))
    (hk : (σ k).HasType a) (ha : Interp env ρ' a (VExpr.wrapForalls Es (.sort l)))
    (hl : SLvl.IsZero l.eval) (hlen : args.length = Es.length) :
    ∀ m, Interp env σ m b → m ≤ .bot := by
  intro m hm
  obtain ⟨m', t, hle, -, ht, hty⟩ := hrec.sound W hm
  exact hle.trans (Interp.mkApps_bvar_prop hk ha hl hlen (hBT _ ht) hty)

end

end Lean4Lean.ShapeModel
