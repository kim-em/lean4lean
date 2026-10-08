import Lean4Lean.Verify.Typing.TelescopeTranslation
import Lean4Lean.Verify.Typing.LevelEquiv

/-!
# Transport lemmas for telescope-closed translations

Syntactic facts about binders that a source body does not mention, and the transport of the
depth-bounded certificate `TelTrN` along environment extension (`TelTrN.mono`), level instantiation
(`TelTrN.instL_lequiv`), free-variable weakening (`TelTrN.weakFV`) and substitution of a typed
term (`TelTrN.instN`, `TelTrN.inst`). Each transport moves only the binders already present in the
certified spine: the delete branch of a binder commutes with the operation at the other binders.

`TelTr.toTelTrN` reads a depth-bounded certificate off the unbounded `TelTr` for a source whose
syntactic `forallE` spine is long enough.
-/

namespace Lean.Expr

theorem liftLooseBVars'_inj {x y : Expr} {k d : Nat}
    (h : liftLooseBVars' x k d = liftLooseBVars' y k d) : x = y := by
  induction x generalizing y k with
  | bvar i =>
    cases y <;> simp [liftLooseBVars'] at h ⊢
    split at h <;> split at h <;> omega
  | app f a ihf iha =>
    cases y <;> simp [liftLooseBVars'] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam n t b bi iht ihb | forallE n t b bi iht ihb =>
    cases y <;> simp [liftLooseBVars'] at h ⊢
    exact ⟨h.1, iht h.2.1, ihb h.2.2.1, h.2.2.2⟩
  | letE n t v b nd iht ihv ihb =>
    cases y <;> simp [liftLooseBVars'] at h ⊢
    exact ⟨h.1, iht h.2.1, ihv h.2.2.1, ihb h.2.2.2.1, h.2.2.2.2⟩
  | mdata m e ih =>
    cases y <;> simp [liftLooseBVars'] at h ⊢
    exact ⟨h.1, ih h.2⟩
  | proj s i e ih =>
    cases y <;> simp [liftLooseBVars'] at h ⊢
    exact ⟨h.1, h.2.1, ih h.2.2⟩
  | _ => cases y <;> simp [liftLooseBVars'] at h ⊢; exact h

theorem hasLooseBVar'_liftLooseBVars'_of_lt {e : Expr} {k d i : Nat}
    (h1 : k ≤ i) (h2 : i < k + d) : (liftLooseBVars' e k d).hasLooseBVar' i = false := by
  induction e generalizing k i with
  | bvar j => simp [liftLooseBVars', hasLooseBVar']; split <;> omega
  | _ => simp_all [liftLooseBVars', hasLooseBVar'] <;> grind

theorem hasLooseBVar'_liftLooseBVars'_self {e : Expr} {k : Nat} :
    (liftLooseBVars' e k 1).hasLooseBVar' k = false :=
  hasLooseBVar'_liftLooseBVars'_of_lt (Nat.le_refl _) (Nat.lt_succ_self _)

theorem liftLooseBVars'_lower {e : Expr} {k : Nat} (h : e.hasLooseBVar' k = false) :
    liftLooseBVars' (lowerLooseBVars' e (k + 1) 1) k 1 = e := by
  have hk : ¬ (k + 1 < 1) := by omega
  induction e generalizing k with
  | bvar j =>
    simp [hasLooseBVar'] at h
    simp only [lowerLooseBVars', liftLooseBVars', if_neg hk]
    congr 1; split <;> split <;> omega
  | app _ _ ihf iha =>
    simp only [hasLooseBVar', Bool.or_eq_false_iff] at h
    simp [lowerLooseBVars', liftLooseBVars', ihf h.1, iha h.2]
  | lam _ _ _ _ iht ihb | forallE _ _ _ _ iht ihb =>
    simp only [hasLooseBVar', Bool.or_eq_false_iff] at h
    simp [lowerLooseBVars', liftLooseBVars', iht h.1, ihb h.2]
  | letE _ _ _ _ _ iht ihv ihb =>
    simp only [hasLooseBVar', Bool.or_eq_false_iff] at h
    simp [lowerLooseBVars', liftLooseBVars', iht h.1.1, ihv h.1.2, ihb h.2]
  | mdata _ _ ih | proj _ _ _ ih =>
    simp only [hasLooseBVar'] at h
    simp [lowerLooseBVars', liftLooseBVars', ih h]
  | _ => simp [lowerLooseBVars', liftLooseBVars']

theorem eq_liftLooseBVars'_lower {e : Expr} {k : Nat} (h : e.hasLooseBVar' k = false) :
    e = liftLooseBVars' (lowerLooseBVars' e (k + 1) 1) k 1 := (liftLooseBVars'_lower h).symm

theorem exists_liftLooseBVars'_iff {e : Expr} {k : Nat} :
    (∃ e₀, e = liftLooseBVars' e₀ k 1) ↔ e.hasLooseBVar' k = false :=
  ⟨fun ⟨_, h⟩ => h ▸ hasLooseBVar'_liftLooseBVars'_self,
   fun h => ⟨_, eq_liftLooseBVars'_lower h⟩⟩

theorem hasLooseBVar'_instantiate1'_of_le {e a : Expr} {i k : Nat} (hi : i ≤ k) :
    (e.instantiate1' a (k + 1)).hasLooseBVar' i = e.hasLooseBVar' i := by
  induction e generalizing i k with
  | bvar j =>
    simp only [instantiate1']
    split
    · rfl
    · split
      · subst j
        rw [hasLooseBVar'_liftLooseBVars'_of_lt (Nat.zero_le _) (by omega)]
        simp [hasLooseBVar']; omega
      · simp [hasLooseBVar']; omega
  | lam _ _ _ _ iht ihb | forallE _ _ _ _ iht ihb =>
    simp [instantiate1', hasLooseBVar', iht hi, ihb (Nat.succ_le_succ hi)]
  | letE _ _ _ _ _ iht ihv ihb =>
    simp [instantiate1', hasLooseBVar', iht hi, ihv hi, ihb (Nat.succ_le_succ hi)]
  | _ => simp_all [instantiate1', hasLooseBVar']

theorem instantiate1'_liftLooseBVars'_lo {b a : Expr} {i k : Nat} (hi : i ≤ k) :
    (liftLooseBVars' b i 1).instantiate1' a (k + 1) =
      liftLooseBVars' (b.instantiate1' a k) i 1 := by
  induction b generalizing i k with
  | bvar j =>
    simp only [liftLooseBVars', instantiate1']
    by_cases hj : j < k
    · have : (if j < i then j else j + 1) < k + 1 := by split <;> omega
      simp only [if_pos this, if_pos hj, liftLooseBVars']
    · by_cases hjk : j = k
      · subst hjk
        have h1 : ¬ (if j < i then j else j + 1) < j + 1 := by split <;> omega
        have h2 : (if j < i then j else j + 1) = j + 1 := by split <;> omega
        simp only [h2, Nat.lt_irrefl, if_false, if_true,
          liftLooseBVars_liftLooseBVars (Nat.zero_le i) (by omega : i ≤ j + 0)]
      · have h1 : ¬ (if j < i then j else j + 1) < k + 1 := by split <;> omega
        have h2 : ¬ (if j < i then j else j + 1) = k + 1 := by split <;> omega
        have h3 : (if j < i then j else j + 1) = j + 1 := by split <;> omega
        simp only [h3, if_neg hj, if_neg hjk, liftLooseBVars']
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        congr 1; omega
  | lam _ _ _ _ iht ihb | forallE _ _ _ _ iht ihb =>
    simp [instantiate1', liftLooseBVars', iht hi, ihb (Nat.succ_le_succ hi)]
  | letE _ _ _ _ _ iht ihv ihb =>
    simp [instantiate1', liftLooseBVars', iht hi, ihv hi, ihb (Nat.succ_le_succ hi)]
  | _ => simp_all [instantiate1', liftLooseBVars']

/-- Inverting a substitution above a binder that the result does not mention. -/
theorem instantiate1'_eq_liftLooseBVars' {b a c : Expr} {k : Nat}
    (h : b.instantiate1' a (k + 1) = liftLooseBVars' c 0 1) :
    ∃ b₀, b = liftLooseBVars' b₀ 0 1 ∧ c = b₀.instantiate1' a k := by
  have h0 : b.hasLooseBVar' 0 = false := by
    rw [← hasLooseBVar'_instantiate1'_of_le (a := a) (k := k) (Nat.zero_le _), h]
    exact hasLooseBVar'_liftLooseBVars'_self
  refine ⟨_, eq_liftLooseBVars'_lower h0, ?_⟩
  rw [eq_liftLooseBVars'_lower h0, instantiate1'_liftLooseBVars'_lo (Nat.zero_le _)] at h
  exact (liftLooseBVars'_inj h).symm

theorem instantiateLevelParamsCore'_liftLooseBVars' {e : Expr} {red s} {k d : Nat} :
    instantiateLevelParamsCore' red s (liftLooseBVars' e k d) =
      liftLooseBVars' (instantiateLevelParamsCore' red s e) k d := by
  induction e generalizing k <;> simp_all [instantiateLevelParamsCore', liftLooseBVars']

theorem hasLooseBVar'_instantiateLevelParamsCore' {e : Expr} {red s} {i : Nat} :
    (instantiateLevelParamsCore' red s e).hasLooseBVar' i = e.hasLooseBVar' i := by
  induction e generalizing i <;> simp_all [instantiateLevelParamsCore', hasLooseBVar']

theorem instantiateLevelParams_liftLooseBVars' {e : Expr} {ps ls} {k d : Nat} :
    (liftLooseBVars' e k d).instantiateLevelParams ps ls =
      liftLooseBVars' (e.instantiateLevelParams ps ls) k d := by
  simp only [instantiateLevelParams_eq, instantiateLevelParamsCore'_liftLooseBVars']

theorem instantiateLevelParams_eq_liftLooseBVars' {b c : Expr} {ps ls}
    (h : b.instantiateLevelParams ps ls = liftLooseBVars' c 0 1) :
    ∃ b₀, b = liftLooseBVars' b₀ 0 1 ∧ c = b₀.instantiateLevelParams ps ls := by
  have h0 : b.hasLooseBVar' 0 = false := by
    have := congrArg (hasLooseBVar' · 0) h
    simp only [instantiateLevelParams_eq, hasLooseBVar'_instantiateLevelParamsCore'] at this
    rw [this]; exact hasLooseBVar'_liftLooseBVars'_self
  refine ⟨_, eq_liftLooseBVars'_lower h0, ?_⟩
  rw [eq_liftLooseBVars'_lower h0, instantiateLevelParams_liftLooseBVars'] at h
  exact (liftLooseBVars'_inj h).symm

end Lean.Expr

namespace Lean4Lean
open Lean VEnv

/-! ### Translations of bodies that do not use an inserted binder -/

/-- Translation is syntactically unique: every constructor of `TrExprS` is
determined by the source syntax and the context, including projections
(`TrProj.target_eq`).  This strengthens `TrExprS.unique'`, whose `IsUnique`
hypothesis excludes projections. -/
theorem TrExprS.uniqueCtx {env : VEnv} {Us : List Name} {Δ₁ Δ₂ : VLCtx} {e : Lean.Expr}
    {e₁ e₂ : VExpr} (hΔ : TrExprS.IsUniqueCtx Δ₁ Δ₂)
    (H1 : TrExprS env Us Δ₁ e e₁) (H2 : TrExprS env Us Δ₂ e e₂) : e₁ = e₂ := by
  induction H1 generalizing Δ₂ e₂ with cases H2
  | bvar => exact hΔ.find?_uniq ‹_› ‹_›
  | fvar => exact hΔ.find?_uniq ‹_› ‹_›
  | sort h1
  | const _ h1 => cases h1.symm.trans ‹_›; rfl
  | app _ _ _ _ ih1 ih2 => cases ih1 hΔ ‹_›; cases ih2 hΔ ‹_›; rfl
  | lam _ _ _ ih1 ih2
  | forallE _ _ _ _ ih1 ih2 => cases ih1 hΔ ‹_›; cases ih2 (hΔ.cons .vlam) ‹_›; rfl
  | letE _ _ _ _ _ ih1 ih2 => cases ih1 hΔ ‹_›; cases ih2 (hΔ.cons .vlet) ‹_›; rfl
  | lit _ _ ih => exact ih hΔ ‹_›
  | mdata _ ih => exact ih hΔ ‹_›
  | proj _ hp ih =>
    rename_i h2 hp2
    cases ih hΔ h2
    rw [hp.target_eq, hp2.target_eq]

theorem TrExprS.uniqueS {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Lean.Expr}
    {e₁ e₂ : VExpr} (H1 : TrExprS env Us Δ e e₁) (H2 : TrExprS env Us Δ e e₂) : e₁ = e₂ :=
  H1.uniqueCtx .base H2


theorem VLCtx.BVLift.find?_lift_inv (W : VLCtx.BVLift Δ Δ' dn dk n k)
    (h : Δ'.find? (VLCtx.liftVar dn dk v) = some p) : ∃ x, Δ.find? v = some x := by
  induction W generalizing v p with
  | refl => simp [VLCtx.liftVar_zero] at h; exact ⟨_, h⟩
  | skip d _ ih =>
    obtain i | fv := v
    · simp only [VLCtx.liftVar, Nat.not_lt_zero, if_false, ← Nat.add_assoc, VLCtx.find?,
        VLCtx.next, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, h, -⟩ := h
      exact ih (v := .inl i) (by simpa [VLCtx.liftVar] using h)
    · simp only [VLCtx.liftVar, VLCtx.find?, VLCtx.next, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at h
      obtain ⟨_, h, -⟩ := h
      exact ih (v := .inr fv) (by simpa [VLCtx.liftVar] using h)
  | @cons _ _ dn' dk' _ _ d _ ih =>
    obtain (_ | i) | fv := v
    · exact ⟨_, rfl⟩
    · have e : VLCtx.liftVar dn' (dk' + 1) (.inl (i + 1)) =
          .inl ((if i < dk' then i else i + dn') + 1) := by
        simp only [VLCtx.liftVar]; congr 1; split <;> split <;> omega
      rw [e] at h
      simp only [VLCtx.find?, VLCtx.next, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, h, -⟩ := h
      obtain ⟨⟨e, A⟩, h'⟩ := ih (v := .inl i) (by simpa [VLCtx.liftVar] using h)
      exact ⟨(e.liftN d.depth, A.liftN d.depth), by simp [VLCtx.find?, VLCtx.next, h']⟩
    · simp only [VLCtx.liftVar, VLCtx.find?, VLCtx.next, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at h
      obtain ⟨_, h, -⟩ := h
      obtain ⟨⟨e, A⟩, h'⟩ := ih (v := .inr fv) (by simpa [VLCtx.liftVar] using h)
      exact ⟨(e.liftN d.depth, A.liftN d.depth), by simp [VLCtx.find?, VLCtx.next, h']⟩

/-- The translation of a source that does not mention an inserted binder is a lift. This is the
structural half of strengthening: it needs no typing, only that translation is syntactic. -/
theorem TrExprS.liftN_inv (W : VLCtx.BVLift Δ Δ' 1 dk 1 k)
    (H : TrExprS env Us Δ' (Expr.liftLooseBVars' e₀ dk 1) e') :
    ∃ e₀' : VExpr, e' = e₀'.liftN 1 k := by
  generalize he : Expr.liftLooseBVars' e₀ dk 1 = e at H
  induction H generalizing e₀ Δ dk k with
  | bvar h1 =>
    cases e₀ <;> simp [Expr.liftLooseBVars'] at he
    subst he
    rename_i j
    have hv : VLCtx.liftVar 1 dk (.inl j) = .inl (if j < dk then j else j + 1) := rfl
    obtain ⟨⟨x, A⟩, hx⟩ := W.find?_lift_inv (v := .inl j) (by rw [hv]; exact h1)
    have := W.find? hx
    rw [hv, h1] at this
    cases this; exact ⟨_, rfl⟩
  | fvar h1 =>
    cases e₀ <;> simp [Expr.liftLooseBVars'] at he
    subst he
    obtain ⟨⟨x, A⟩, hx⟩ := W.find?_lift_inv (v := .inr _) h1
    have := W.find? hx
    rw [show VLCtx.liftVar 1 dk (.inr _) = .inr _ from rfl, h1] at this
    cases this; exact ⟨_, rfl⟩
  | sort => exact ⟨.sort _, rfl⟩
  | const => exact ⟨.const _ _, rfl⟩
  | app _ _ _ _ ih1 ih2 =>
    cases e₀ <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨f₀, rfl⟩ := ih1 W rfl
    obtain ⟨a₀, rfl⟩ := ih2 W rfl
    exact ⟨.app f₀ a₀, rfl⟩
  | lam _ _ _ ih1 ih2 =>
    cases e₀ <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    obtain ⟨t₀, rfl⟩ := ih1 W rfl
    obtain ⟨b₀, rfl⟩ := ih2 (W.cons (.vlam t₀)) rfl
    exact ⟨.lam t₀ b₀, rfl⟩
  | forallE _ _ _ _ ih1 ih2 =>
    cases e₀ <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    obtain ⟨t₀, rfl⟩ := ih1 W rfl
    obtain ⟨b₀, rfl⟩ := ih2 (W.cons (.vlam t₀)) rfl
    exact ⟨.forallE t₀ b₀, rfl⟩
  | letE _ _ _ _ ih1 ih2 ih3 =>
    cases e₀ <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
    obtain ⟨t₀, rfl⟩ := ih1 W rfl
    obtain ⟨v₀, rfl⟩ := ih2 W rfl
    exact ih3 (W.cons (.vlet t₀ v₀)) rfl
  | lit _ _ ih =>
    cases e₀ <;> simp [Expr.liftLooseBVars'] at he
    subst he
    exact ih W (Expr.liftLooseBVars_eq_self Closed.toConstructor.looseBVarRange_le)
  | mdata _ ih =>
    cases e₀ <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ih W rfl
  | proj _ hp ih =>
    cases e₀ <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨x₀, rfl⟩ := ih W rfl
    rw [hp.target_eq]
    exact ⟨.proj _ _ x₀, rfl⟩

theorem TrExprS.lift_inv
    (H : TrExprS env Us ((none, .vlam D) :: Δ) (Expr.liftLooseBVars' e₀ 0 1) e') :
    ∃ e₀' : VExpr, e' = e₀'.lift :=
  H.liftN_inv (.skip (.vlam D) .refl)

/-! ### The depth-bounded certificate -/

namespace TelTrN

theorem toTrExprS : TelTrN env Us n Δ e e' → TrExprS env Us Δ e e'
  | .zero h | .succ h .. => h

theorem le : ∀ {m n}, m ≤ n → TelTrN env Us n Δ e e' → TelTrN env Us m Δ e e'
  | 0, _, _, H => .zero H.toTrExprS
  | _ + 1, 0, h, _ => absurd h (by omega)
  | m + 1, n + 1, h, .succ h1 h2 h3 h4 =>
    .succ h1 (le (by omega) h2) h3 fun _ _ hb hb' => le (by omega) (h4 _ _ hb hb')

theorem mono (henv : env ≤ env') (H : TelTrN env Us n Δ e e') : TelTrN env' Us n Δ e e' := by
  induction H with
  | zero h => exact .zero (h.mono henv)
  | succ h1 _ h3 _ ih2 ih4 => exact .succ (h1.mono henv) ih2 h3 fun _ _ hb hb' => ih4 _ _ hb hb'

/-- A positive-depth certificate is a syntactic `forallE`. -/
theorem forallE_of_succ (H : TelTrN env Us (n + 1) Δ e e') :
    ∃ nm d b bi d' b', e = .forallE nm d b bi ∧ e' = .forallE d' b' := by
  cases H; exact ⟨_, _, _, _, _, _, rfl, rfl⟩

theorem keep (H : TelTrN env Us (n + 1) Δ (.forallE nm d b bi) (.forallE d' b')) :
    TelTrN env Us n ((none, .vlam d') :: Δ) b b' := by
  cases H; assumption

/-- The delete branch at the head binder, for a body without loose bound variables (the form in
which the executable meets it). -/
theorem delete_closed (H : TelTrN env Us (n + 1) Δ (.forallE nm d b bi) (.forallE d' b'))
    (hb : b.looseBVarRange' ≤ 0) : ∃ b₀', b' = VExpr.lift b₀' ∧ TelTrN env Us n Δ b b₀' := by
  cases H with
  | succ _ _ h3 h4 =>
    have e : b = Expr.liftLooseBVars' b 0 1 := (Expr.liftLooseBVars_eq_self hb).symm
    obtain ⟨b₀', hb'⟩ := h3 _ e
    exact ⟨_, hb', h4 _ _ e hb'⟩

variable! (henv : Ordered env) in
theorem weakFV (W : VLCtx.FVLift Δ Δ' dk n k) (hΔ' : Δ'.WF env Us.length)
    (H : TelTrN env Us m Δ e e') : TelTrN env Us m Δ' e (e'.liftN n k) := by
  induction H generalizing Δ' dk k with
  | zero h => exact .zero (h.weakFV henv W hΔ')
  | succ h1 _ h3 _ ih2 ih4 =>
    have h1' := h1.weakFV henv W hΔ'
    let .forallE hd _ _ _ := h1'
    refine .succ h1' (ih2 (W.cons_bvar (.vlam _)) ⟨hΔ', nofun, hd⟩) ?_ ?_
    · intro b₀ hb
      obtain ⟨b₀', rfl⟩ := h3 _ hb
      exact ⟨b₀'.liftN n k, (VExpr.lift_liftN' ..).symm⟩
    · intro b₀ c' hb hc'
      obtain ⟨b₀', rfl⟩ := h3 _ hb
      rw [← VExpr.lift_liftN'] at hc'
      cases VExpr.liftN_inj.1 hc'
      exact ih4 _ _ hb rfl W hΔ'

variable! (henv : Ordered env) (h₀ : TrExprS env Us Δ₀ e₀ e₀')
  (t₀ : env.HasType Us.length Δ₀.toCtx e₀' A₀) in
/-- Substitution of a typed term for a variable of the context. The certified binders of the
spine are those of `e`; deletion at a binder commutes with substitution at the others. -/
theorem instN (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) (H : TelTrN env Us m Δ₁ e e') :
    TelTrN env Us m Δ (Expr.instantiate1' e e₀ dk) (e'.inst e₀' k) := by
  induction H generalizing Δ dk k with
  | zero h => exact .zero (h₀.instN henv t₀ W h)
  | succ h1 _ h3 h4 ih2 ih4 =>
    refine .succ (h₀.instN henv t₀ W h1) (ih2 (W.succ (d := .vlam _))) ?_ ?_
    · intro c hc
      obtain ⟨b₀, hb, -⟩ := Expr.instantiate1'_eq_liftLooseBVars' hc
      obtain ⟨b₀', rfl⟩ := h3 _ hb
      exact ⟨_, (VExpr.lift_instN_lo ..).symm⟩
    · intro c c' hc hc'
      obtain ⟨b₀, hb, rfl⟩ := Expr.instantiate1'_eq_liftLooseBVars' hc
      obtain ⟨b₀', rfl⟩ := h3 _ hb
      rw [← VExpr.lift_instN_lo] at hc'
      cases VExpr.liftN_inj.1 hc'
      exact ih4 _ _ hb rfl W

variable! (henv : Ordered env) in
theorem inst {Δ : VLCtx} (t₀ : env.HasType Us.length Δ.toCtx e₀' A₀)
    (H : TelTrN env Us m ((none, .vlam A₀) :: Δ) e e') (h₀ : TrExprS env Us Δ e₀ e₀') :
    TelTrN env Us m Δ (e.instantiate1' e₀) (e'.inst e₀') :=
  H.instN henv h₀ t₀ .zero

theorem _root_.Lean.Expr.instantiateLevelParams_forallE {n : Name} {d b : Expr} {bi} {ps ls} :
    (Expr.forallE n d b bi).instantiateLevelParams ps ls =
      .forallE n (d.instantiateLevelParams ps ls) (b.instantiateLevelParams ps ls) bi := by
  simp [Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore']

section
variable {Us ps : List Name} {ls : List Level} {ls' : List VLevel}
  (henv : VEnv.WF env)
  (Hls : ls.mapM (VLevel.ofLevel Us) = some ls')
  (eq : ps.length = ls.length)

include henv Hls eq in
/-- Level instantiation, into any context definitionally equal to the instantiated one: every
translation of the instantiated source is certified. The keep branch follows the actual translated
domain of the instantiated binder; the delete branch identifies the translation of the lowered
body syntactically. -/
theorem instL_core (H : TelTrN env ps m Δ e e') (hΔ : VLCtx.WF env ps.length Δ) :
    ∀ {Δ₂ e₁}, VLCtx.IsDefEq env Us.length (Δ.instL ls') Δ₂ →
      TrExprS env Us Δ₂ (e.instantiateLevelParams ps ls) e₁ →
      TelTrN env Us m Δ₂ (e.instantiateLevelParams ps ls) e₁ := by
  have hlen : ls'.length = ps.length := by
    rw [eq]; exact (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 Hls)).symm
  induction H with
  | zero => intro _ _ _ H₂; exact .zero H₂
  | @succ k Δ n d b bi d' b' h1 _ h3 h4 ih2 ih4 =>
    intro Δ₂ e₁ hΔ₂ H₂
    rw [Expr.instantiateLevelParams_forallE] at H₂ ⊢
    obtain ⟨d₁, b₁, rfl, hd₁T, hd₁, hb₁⟩ : ∃ d₁ b₁, e₁ = .forallE d₁ b₁ ∧
        env.IsType Us.length Δ₂.toCtx d₁ ∧
        TrExprS env Us Δ₂ (d.instantiateLevelParams ps ls) d₁ ∧
        TrExprS env Us ((none, .vlam d₁) :: Δ₂) (b.instantiateLevelParams ps ls) b₁ := by
      cases H₂ with | forallE h1 _ h3 h4 => exact ⟨_, _, rfl, h1, h3, h4⟩
    let .forallE hd'T _ hd _ := h1
    have hΔ' : VLCtx.WF env ls'.length Δ := hlen ▸ hΔ
    have hΓ := hΔ₂.wf.toCtx
    have hΓ₂ := (hΔ₂.symm henv.ordered).defeqCtx
    -- the instantiated domain agrees with the actual translated domain
    obtain ⟨X, hX, hXeq⟩ := hd.instL henv hΔ' Hls eq
    have hu : VEnv.IsDefEqU env Us.length (Δ.instL ls').toCtx (d'.instL ls') _ :=
      hXeq.symm.trans henv hΓ (hX.uniq henv hΔ₂ hd₁)
    obtain ⟨u, hd₁u⟩ := hd₁T.defeqDFC henv.ordered hΓ₂
    have hdd := (hu.symm.of_l henv hΓ hd₁u).symm
    have hΔ₂' : VLCtx.IsDefEq env Us.length
        (VLCtx.instL ((none, .vlam d') :: Δ) ls') ((none, .vlam d₁) :: Δ₂) :=
      .cons hΔ₂ (fun _ _ h => by cases h) (.vlam hdd)
    -- the translation of a lowered body in `Δ₂`, and its lift
    have low : ∀ c, b.instantiateLevelParams ps ls = Expr.liftLooseBVars' c 0 1 →
        ∃ b₀ b₀', b = Expr.liftLooseBVars' b₀ 0 1 ∧ b' = VExpr.lift b₀' ∧
          c = b₀.instantiateLevelParams ps ls ∧ ∃ c₂, TrExprS env Us Δ₂ c c₂ ∧ b₁ = c₂.lift := by
      intro c hc
      obtain ⟨b₀, hb, rfl⟩ := Expr.instantiateLevelParams_eq_liftLooseBVars' hc
      obtain ⟨b₀', hb'⟩ := h3 _ hb
      obtain ⟨Y, hY, -⟩ := (h4 _ _ hb hb').toTrExprS.instL henv hΔ' Hls eq
      obtain ⟨c₂, hc₂⟩ := hY.defeqDFC henv hΔ₂
      have hw := hc₂.weakBV henv.ordered (.skip (.vlam d₁) .refl)
      rw [← hc] at hw
      exact ⟨_, _, hb, hb', rfl, _, hc₂, hb₁.uniqueCtx .base hw⟩
    refine .succ H₂ (ih2 ⟨hΔ, nofun, hd'T⟩ hΔ₂' hb₁) ?_ ?_
    · intro c hc
      obtain ⟨-, -, -, -, -, c₂, -, e⟩ := low c hc
      exact ⟨c₂, e⟩
    · intro c c' hc hc'
      obtain ⟨b₀, b₀', hb, hb', rfl, c₂, hc₂, e⟩ := low c hc
      rw [hc'] at e
      cases VExpr.liftN_inj.1 e
      exact ih4 _ _ hb hb' hΔ hΔ₂ hc₂

include henv Hls eq in
/-- Level instantiation of a closed certificate (mirrors `TrExprS.instL_lequiv`). -/
theorem instL_lequiv (H : TelTrN env ps m [] e e') :
    ∃ e₁, TelTrN env Us m [] (e.instantiateLevelParams ps ls) e₁ ∧
      VExpr.LEquiv Us.length e₁ (e'.instL ls') := by
  have hlen : ls'.length = ps.length := by
    rw [eq]; exact (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 Hls)).symm
  obtain ⟨e₁, h1, h2⟩ := H.toTrExprS.instL_lequiv Hls eq henv (Δ := []) trivial
  exact ⟨e₁, H.instL_core henv Hls eq trivial .nil h1, h2⟩

end

end TelTrN

theorem _root_.Lean4Lean.AddInductive.constructorArity_liftLooseBVars' {e : Expr} {s d : Nat} :
    AddInductive.constructorArity (Expr.liftLooseBVars' e s d) = AddInductive.constructorArity e := by
  induction e generalizing s <;> simp_all [Expr.liftLooseBVars', AddInductive.constructorArity]

/-- The unbounded certificate gives the bounded one along the syntactic `forallE` spine. -/
theorem _root_.Lean4Lean.TelTr.toTelTrN :
    ∀ {n : Nat} {Δ : VLCtx} {e : Expr} {e' : VExpr},
    TelTr env Us Δ e e' → n ≤ AddInductive.constructorArity e → TelTrN env Us n Δ e e'
  | 0, _, _, _, H, _ => .zero H.toTrExprS
  | n + 1, Δ, e, e', H, hn => by
    cases e with
    | forallE nm d b bi =>
      simp only [AddInductive.constructorArity] at hn
      have h1 := H.toTrExprS
      obtain ⟨d', b', rfl⟩ : ∃ d' b', e' = .forallE d' b' := by
        cases h1 with | forallE => exact ⟨_, _, rfl⟩
      have hb := h1
      cases hb with | forallE _ _ _ hb =>
      refine .succ h1 (H.keep.toTelTrN (by omega)) ?_ ?_
      · intro b₀ e; subst e; exact hb.lift_inv
      · intro b₀ b₀' e e'
        refine (H.delete e e').toTelTrN ?_
        rw [e, AddInductive.constructorArity_liftLooseBVars'] at hn; omega
    | _ => simp [AddInductive.constructorArity] at hn

end Lean4Lean
