import Lean4Lean.Theory.Typing.LevelEquiv
import Lean4Lean.Verify.Typing.Lemmas

/-!
# Syntactic facts about translation

* `TrExprS.instL_lequiv`: the translation of a level-instantiated expression is `LEquiv` to the
  syntactic level instantiation of the translation of the original.
* `TrExprS.weakBV_inv`: an expression closed below the inserted bound variables translates to
  a lift (the converse of `TrExprS.weakBV`).
-/

namespace Lean4Lean
open VEnv Lean

/-! ### Level-equivalent contexts -/

inductive VLocalDecl.LEquiv (U : Nat) : VLocalDecl → VLocalDecl → Prop
  | vlam : VExpr.LEquiv U A A' → VLocalDecl.LEquiv U (.vlam A) (.vlam A')
  | vlet : VExpr.LEquiv U A A' → VExpr.LEquiv U v v' →
    VLocalDecl.LEquiv U (.vlet A v) (.vlet A' v')

inductive VLCtx.LEquiv (U : Nat) : VLCtx → VLCtx → Prop
  | nil : VLCtx.LEquiv U [] []
  | cons : VLCtx.LEquiv U Δ₁ Δ₂ → VLocalDecl.LEquiv U d₁ d₂ →
    VLCtx.LEquiv U ((ofv, d₁) :: Δ₁) ((ofv, d₂) :: Δ₂)

theorem VLocalDecl.LEquiv.refl : ∀ d, VLocalDecl.LEquiv U d d
  | .vlam _ => .vlam .refl
  | .vlet .. => .vlet .refl .refl

theorem VLCtx.LEquiv.refl : ∀ Δ, VLCtx.LEquiv U Δ Δ
  | [] => .nil
  | (_, d) :: Δ => .cons (.refl Δ) (.refl d)

theorem VLocalDecl.LEquiv.depth : VLocalDecl.LEquiv U d₁ d₂ → d₁.depth = d₂.depth
  | .vlam _ | .vlet .. => rfl

theorem VLocalDecl.LEquiv.value : VLocalDecl.LEquiv U d₁ d₂ → VExpr.LEquiv U d₁.value d₂.value
  | .vlam _ => .refl
  | .vlet _ h => h

theorem VLocalDecl.LEquiv.type : VLocalDecl.LEquiv U d₁ d₂ → VExpr.LEquiv U d₁.type d₂.type
  | .vlam h => h.liftN
  | .vlet h _ => h

theorem VLCtx.LEquiv.find? (H : VLCtx.LEquiv U Δ₁ Δ₂) (h : Δ₂.find? v = some (e, A)) :
    ∃ e₁ A₁, Δ₁.find? v = some (e₁, A₁) ∧ VExpr.LEquiv U e₁ e ∧ VExpr.LEquiv U A₁ A := by
  induction H generalizing v e A with
  | nil => cases h
  | cons _ hd ih =>
    revert h; unfold VLCtx.find?; split
    · rintro ⟨⟩; exact ⟨_, _, rfl, hd.value, hd.type⟩
    · simp; rintro e A h rfl rfl
      obtain ⟨e₁, A₁, h1, l1, l2⟩ := ih h
      exact ⟨_, _, ⟨_, _, h1, rfl, rfl⟩, hd.depth ▸ l1.liftN, hd.depth ▸ l2.liftN⟩

/-! ### Level instantiation -/

section
variable {Us ps : List Name} {ls : List Level} {ls' : List VLevel}
  (Hls : ls.mapM (VLevel.ofLevel Us) = some ls')
  (eq : ps.length = ls.length)
include Hls eq

/-- Two translations, of an expression and of its level instantiation, in level-equivalent
contexts, are level equivalent. -/
theorem TrExprS.instL_lequiv_of (H : TrExprS env ps Δ e e')
    (hΔ₂ : VLCtx.LEquiv Us.length Δ₂ (Δ.instL ls'))
    (H2 : TrExprS env Us Δ₂ (e.instantiateLevelParams ps ls) e₁) :
    VExpr.LEquiv Us.length e₁ (e'.instL ls') := by
  simp only [Expr.instantiateLevelParams_eq] at H2
  generalize (_ && _) = red, eqF : (fun x : Name => _) = F at H2
  have Hls' := VLevel.WF.of_mapM_ofLevel Hls
  induction H generalizing Δ₂ e₁ with
  | bvar h1 =>
    have ⟨_, _, h2, l1, _⟩ := hΔ₂.find? (VLCtx.find?_instL h1)
    simp only [Expr.instantiateLevelParamsCore'] at H2
    let .bvar h3 := H2
    cases h2.symm.trans h3; exact l1
  | fvar h1 =>
    have ⟨_, _, h2, l1, _⟩ := hΔ₂.find? (VLCtx.find?_instL h1)
    simp only [Expr.instantiateLevelParamsCore'] at H2
    let .fvar h3 := H2
    cases h2.symm.trans h3; exact l1
  | sort h1 =>
    simp only [Expr.instantiateLevelParamsCore'] at H2
    let .sort a1 := H2
    have ⟨_, a1', a2⟩ := substParams_wf Hls eq eqF red h1
    cases a1.symm.trans a1'
    exact .sort a2 (.inst Hls')
  | const _ h2 _ =>
    simp only [Expr.instantiateLevelParamsCore'] at H2
    let .const _ a1 _ := H2
    have ⟨_, a1', a2⟩ := substParams_wf_list Hls eq eqF red h2
    cases a1.symm.trans a1'
    refine .const a2 ?_
    simp; exact fun _ _ => .inst Hls'
  | app _ _ _ _ ih1 ih2 =>
    simp only [Expr.instantiateLevelParamsCore'] at H2
    let .app _ _ hf ha := H2
    exact .app (ih1 hΔ₂ hf) (ih2 hΔ₂ ha)
  | lam _ _ _ ih1 ih2 =>
    simp only [Expr.instantiateLevelParamsCore'] at H2
    let .lam _ hty hbody := H2
    have l1 := ih1 hΔ₂ hty
    exact .lam l1 (ih2 (.cons hΔ₂ (.vlam l1)) hbody)
  | forallE _ _ _ _ ih1 ih2 =>
    simp only [Expr.instantiateLevelParamsCore'] at H2
    let .forallE _ _ hty hbody := H2
    have l1 := ih1 hΔ₂ hty
    exact .forallE l1 (ih2 (.cons hΔ₂ (.vlam l1)) hbody)
  | letE _ _ _ _ ih1 ih2 ih3 =>
    simp only [Expr.instantiateLevelParamsCore'] at H2
    let .letE _ hty hval hbody := H2
    have l1 := ih1 hΔ₂ hty
    have l2 := ih2 hΔ₂ hval
    exact ih3 (.cons hΔ₂ (.vlet l1 l2)) hbody
  | lit _ _ ih =>
    simp only [Expr.instantiateLevelParamsCore'] at H2
    let .lit _ h := H2
    refine ih hΔ₂ ?_
    rwa [Expr.instantiateLevelParamsCore_eq_self Literal.toConstructor_hasLevelParam]
  | mdata _ ih =>
    simp only [Expr.instantiateLevelParamsCore'] at H2
    let .mdata h := H2
    exact ih hΔ₂ h
  | proj _ h2 ih =>
    simp only [Expr.instantiateLevelParamsCore'] at H2
    let .proj hs hp := H2
    cases h2; cases hp
    exact .proj (ih hΔ₂ hs)

theorem TrExprS.instL_lequiv (henv : VEnv.WF env) (hΔ : VLCtx.WF env ls'.length Δ)
    (H : TrExprS env ps Δ e e') :
    ∃ e₁, TrExprS env Us (Δ.instL ls') (e.instantiateLevelParams ps ls) e₁ ∧
      VExpr.LEquiv Us.length e₁ (e'.instL ls') :=
  let ⟨e₁, h1, _⟩ := H.instL henv hΔ Hls eq
  ⟨e₁, h1, H.instL_lequiv_of Hls eq (.refl _) h1⟩

end

/-! ### Inverse bound-variable weakening -/

theorem VLCtx.BVLift.find?_exists (W : VLCtx.BVLift Δ Δ' dn dk n k)
    (hv : ∀ i, v = .inl i → i < dk) (h : ∃ x, Δ'.find? v = some x) : ∃ x, Δ.find? v = some x := by
  induction W generalizing v with
  | refl => exact h
  | skip d _ ih =>
    obtain _ | fv := v
    · cases Nat.not_lt_zero _ (hv _ rfl)
    · have ⟨_, h⟩ := h
      simp [VLCtx.find?, VLCtx.next, bind] at h
      obtain ⟨_, _, h, -⟩ := h
      exact ih nofun ⟨_, h⟩
  | cons d _ ih =>
    obtain (_ | i) | fv := v
    · exact ⟨_, rfl⟩
    · have ⟨_, h⟩ := h
      simp [VLCtx.find?, VLCtx.next, bind] at h
      obtain ⟨_, _, h, -⟩ := h
      have ⟨⟨e, A⟩, h'⟩ :=
        ih (v := .inl i) (fun _ e => Nat.lt_of_succ_lt_succ (by cases e; exact hv _ rfl)) ⟨_, h⟩
      exact ⟨(e.liftN d.depth, A.liftN d.depth), by simp [VLCtx.find?, VLCtx.next, bind, h']⟩
    · have ⟨_, h⟩ := h
      simp [VLCtx.find?, VLCtx.next, bind] at h
      obtain ⟨_, _, h, -⟩ := h
      have ⟨⟨e, A⟩, h'⟩ := ih (v := .inr fv) nofun ⟨_, h⟩
      exact ⟨(e.liftN d.depth, A.liftN d.depth), by simp [VLCtx.find?, VLCtx.next, bind, h']⟩

variable! (henv : VEnv.WF env) (hs : env.Strengthening) in
theorem TrExprS.weakBV_inv (W : VLCtx.BVLift Δ Δ' dn dk n k) (hΔ' : Δ'.WF env Us.length)
    (H : TrExprS env Us Δ' e e') (hc : Closed e dk) :
    ∃ e₀, TrExprS env Us Δ e e₀ ∧ e' = e₀.liftN n k := by
  induction H generalizing Δ dk k with
  | @bvar _ _ _ i h1 =>
    have hi : i < dk := hc
    have ⟨⟨e₀, A₀⟩, h2⟩ := W.find?_exists (v := .inl i) (by rintro _ ⟨⟩; exact hi) ⟨_, h1⟩
    have h3 := W.find? h2
    rw [show VLCtx.liftVar dn dk (.inl i) = .inl i by simp [VLCtx.liftVar, hi]] at h3
    cases h1.symm.trans h3
    exact ⟨_, .bvar h2, rfl⟩
  | @fvar _ _ _ fv h1 =>
    have ⟨⟨e₀, A₀⟩, h2⟩ := W.find?_exists (v := .inr fv) nofun ⟨_, h1⟩
    have h3 := W.find? h2
    cases h1.symm.trans h3
    exact ⟨_, .fvar h2, rfl⟩
  | sort h1 => exact ⟨_, .sort h1, rfl⟩
  | const h1 h2 h3 => exact ⟨_, .const h1 h2 h3, rfl⟩
  | app h1 h2 _ _ ih1 ih2 =>
    obtain ⟨f₀, hf₀, rfl⟩ := ih1 W hΔ' hc.1
    obtain ⟨a₀, ha₀, rfl⟩ := ih2 W hΔ' hc.2
    have := (VExpr.WF.weakN_iff henv hs hΔ'.toCtx W.toCtx (e := .app f₀ a₀)).1 ⟨_, h1.app h2⟩
    have ⟨_, _, h3, h4⟩ := this.app_inv henv.ordered (W.wf henv hs hΔ').toCtx
    exact ⟨_, .app h3 h4 hf₀ ha₀, rfl⟩
  | lam h1 _ _ ih1 ih2 =>
    obtain ⟨ty₀, hty₀, rfl⟩ := ih1 W hΔ' hc.1
    have h1' := (IsType.weakN_iff henv hs hΔ'.toCtx W.toCtx).1 h1
    have hΔ'' : VLCtx.WF env Us.length ((none, .vlam (ty₀.liftN n k)) :: _) := ⟨hΔ', nofun, h1⟩
    obtain ⟨body₀, hbody₀, rfl⟩ := ih2 (W.cons (.vlam ty₀)) hΔ'' hc.2
    exact ⟨_, .lam h1' hty₀ hbody₀, rfl⟩
  | forallE h1 h2 _ _ ih1 ih2 =>
    obtain ⟨ty₀, hty₀, rfl⟩ := ih1 W hΔ' hc.1
    have h1' := (IsType.weakN_iff henv hs hΔ'.toCtx W.toCtx).1 h1
    have hΔ'' : VLCtx.WF env Us.length ((none, .vlam (ty₀.liftN n k)) :: _) := ⟨hΔ', nofun, h1⟩
    obtain ⟨body₀, hbody₀, rfl⟩ := ih2 (W.cons (.vlam ty₀)) hΔ'' hc.2
    have hΓ'' : OnCtx (ty₀.liftN n k :: _) (env.IsType Us.length) := ⟨hΔ'.toCtx, h1⟩
    have h2' := (IsType.weakN_iff henv hs hΓ'' (W.cons (.vlam ty₀)).toCtx).1 h2
    exact ⟨_, .forallE h1' h2' hty₀ hbody₀, rfl⟩
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    obtain ⟨ty₀, hty₀, rfl⟩ := ih1 W hΔ' hc.1
    obtain ⟨val₀, hval₀, rfl⟩ := ih2 W hΔ' hc.2.1
    have h1' := (HasType.weakN_iff henv hs hΔ'.toCtx W.toCtx).1 h1
    have hΔ'' : VLCtx.WF env Us.length ((none, .vlet (ty₀.liftN n k) (val₀.liftN n k)) :: _) :=
      ⟨hΔ', nofun, h1⟩
    obtain ⟨body₀, hbody₀, rfl⟩ := ih3 (W.cons (.vlet ty₀ val₀)) hΔ'' hc.2.2
    exact ⟨_, .letE h1' hty₀ hval₀ hbody₀, rfl⟩
  | lit h1 _ ih =>
    obtain ⟨_, h, rfl⟩ := ih W hΔ' Closed.toConstructor
    exact ⟨_, .lit h1 h, rfl⟩
  | mdata _ ih =>
    obtain ⟨_, h, rfl⟩ := ih W hΔ' hc
    exact ⟨_, .mdata h, rfl⟩
  | proj _ hp ih =>
    obtain ⟨s₀, hs₀, rfl⟩ := ih W hΔ' hc
    cases hp with | direct m t
    have m' := (VExpr.WF.weakN_iff henv hs hΔ'.toCtx W.toCtx).1 m
    have t' := (VExpr.WF.weakN_iff henv hs hΔ'.toCtx W.toCtx (e := .proj _ _ s₀)).1 t
    exact ⟨_, .proj hs₀ (.direct m' t'), rfl⟩

/-- A body under one bound variable that is closed translates to a lift. -/
theorem TrExprS.weakBV_inv₁ (henv : VEnv.WF env) (hs : env.Strengthening)
    (hΔ : VLCtx.WF env Us.length ((none, .vlam A) :: Δ))
    (H : TrExprS env Us ((none, .vlam A) :: Δ) e e') (hc : Closed e) :
    ∃ e₀, TrExprS env Us Δ e e₀ ∧ e' = e₀.lift :=
  H.weakBV_inv henv hs (.skip (.vlam A) .refl) hΔ hc

theorem Closed.of_closed_looseBVarRange {e : Expr} {k j : Nat}
    (hc : Closed e k) (hb : e.looseBVarRange' ≤ j) : Closed e j := by
  induction e generalizing k j with
  | bvar => simp [Closed, Expr.looseBVarRange'] at hc hb ⊢; omega
  | mvar => exact hc.elim
  | app _ _ ih1 ih2 =>
    simp only [Expr.looseBVarRange', Nat.max_le] at hb
    exact ⟨ih1 hc.1 hb.1, ih2 hc.2 hb.2⟩
  | lam _ _ _ _ ih1 ih2 | forallE _ _ _ _ ih1 ih2 =>
    simp only [Expr.looseBVarRange', Nat.max_le] at hb
    exact ⟨ih1 hc.1 hb.1, ih2 hc.2 (by omega)⟩
  | letE _ _ _ _ _ ih1 ih2 ih3 =>
    simp only [Expr.looseBVarRange', Nat.max_le] at hb
    exact ⟨ih1 hc.1 hb.1.1, ih2 hc.2.1 hb.1.2, ih3 hc.2.2 (by omega)⟩
  | proj _ _ _ ih | mdata _ _ ih => exact ih hc hb
  | _ => trivial

end Lean4Lean
