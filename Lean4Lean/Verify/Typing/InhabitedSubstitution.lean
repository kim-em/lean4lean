import Lean4Lean.Verify.Typing.LevelEquiv

/-!
# Substitution of an inhabitant for a binder

If the type `D` of a binder is inhabited, by `d₀`, in the context below it, then removing the
binder is substitution of `d₀`. A judgement about lifted terms holds in the smaller context: the
instantiation `(e.liftN 1 k).inst d₀ k` is `e` again. This needs no strengthening hypothesis on
the environment.

`TrExprS.weakBV_inv_inhabited` is the version of `TrExprS.weakBV_inv` for one inhabited binder.
-/

namespace Lean4Lean
open VEnv Lean

/-- `Γ'` is `Γ` with the binder `A` inserted beneath `k` binders, above the base `Γ₀`. -/
inductive Ctx.Inserted (Γ₀ : List VExpr) (A : VExpr) : Nat → List VExpr → List VExpr → Prop
  | zero : Ctx.Inserted Γ₀ A 0 Γ₀ (A :: Γ₀)
  | succ : Ctx.Inserted Γ₀ A k Γ Γ' → Ctx.Inserted Γ₀ A (k + 1) (B :: Γ) (B.liftN 1 k :: Γ')

theorem Ctx.Inserted.instN (e₀ : VExpr) : Ctx.Inserted Γ₀ A k Γ Γ' → Ctx.InstN Γ₀ e₀ A k Γ' Γ
  | .zero => .zero
  | @Ctx.Inserted.succ _ _ k' _ _ B h => by
    have := Ctx.InstN.succ (A := B.liftN 1 k') (h.instN e₀)
    rwa [VExpr.inst_liftN] at this

section
variable {env : VEnv} {U : Nat}
variable (henv : env.Ordered) (hI : Ctx.Inserted Γ₀ D k Γ Γ') (h₀ : env.HasType U Γ₀ d₀ D)
include henv hI h₀

theorem IsDefEqU.inhabited_inv (H : env.IsDefEqU U Γ' (e1.liftN 1 k) (e2.liftN 1 k)) :
    env.IsDefEqU U Γ e1 e2 := by
  obtain ⟨_, H⟩ := H
  have := IsDefEq.instN henv h₀ (hI.instN d₀) H
  simp only [VExpr.inst_liftN] at this
  exact ⟨_, this⟩

theorem HasType.inhabited_inv (H : env.HasType U Γ' (e.liftN 1 k) (A.liftN 1 k)) :
    env.HasType U Γ e A := by
  have := IsDefEq.instN henv h₀ (hI.instN d₀) H
  simp only [VExpr.inst_liftN] at this
  exact this

theorem IsType.inhabited_inv (H : env.IsType U Γ' (A.liftN 1 k)) : env.IsType U Γ A := by
  obtain ⟨u, H⟩ := H
  exact ⟨u, HasType.inhabited_inv henv hI h₀ (A := .sort u) H⟩

theorem VExpr.WF.inhabited_inv (H : VExpr.WF env U Γ' (e.liftN 1 k)) : VExpr.WF env U Γ e :=
  IsDefEqU.inhabited_inv henv hI h₀ H

theorem OnCtx.inhabited_inv (H : OnCtx Γ' (env.IsType U)) : OnCtx Γ (env.IsType U) :=
  ((hI.instN d₀).wf henv h₀ H).2

end

theorem TrExprS.weakBV_inv_inhabited (henv : VEnv.WF env)
    (h₀ : env.HasType Us.length Γ₀ d₀ D)
    (W : VLCtx.BVLift Δ Δ' dn dk 1 k) (hI : Ctx.Inserted Γ₀ D k Δ.toCtx Δ'.toCtx)
    (hΔ' : Δ'.WF env Us.length)
    (H : TrExprS env Us Δ' e e') (hc : Closed e dk) :
    ∃ e₀, TrExprS env Us Δ e e₀ ∧ e' = e₀.liftN 1 k := by
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
    obtain ⟨f₀, hf₀, rfl⟩ := ih1 W hI hΔ' hc.1
    obtain ⟨a₀, ha₀, rfl⟩ := ih2 W hI hΔ' hc.2
    have := VExpr.WF.inhabited_inv henv.ordered hI h₀ (e := .app f₀ a₀) ⟨_, h1.app h2⟩
    have ⟨_, _, h3, h4⟩ := this.app_inv henv.ordered (OnCtx.inhabited_inv henv.ordered hI h₀ hΔ'.toCtx)
    exact ⟨_, .app h3 h4 hf₀ ha₀, rfl⟩
  | lam h1 _ _ ih1 ih2 =>
    obtain ⟨ty₀, hty₀, rfl⟩ := ih1 W hI hΔ' hc.1
    have h1' := IsType.inhabited_inv henv.ordered hI h₀ h1
    have hΔ'' : VLCtx.WF env Us.length ((none, .vlam (ty₀.liftN 1 k)) :: _) := ⟨hΔ', nofun, h1⟩
    obtain ⟨body₀, hbody₀, rfl⟩ := ih2 (W.cons (.vlam ty₀)) (.succ hI) hΔ'' hc.2
    exact ⟨_, .lam h1' hty₀ hbody₀, rfl⟩
  | forallE h1 h2 _ _ ih1 ih2 =>
    obtain ⟨ty₀, hty₀, rfl⟩ := ih1 W hI hΔ' hc.1
    have h1' := IsType.inhabited_inv henv.ordered hI h₀ h1
    have hΔ'' : VLCtx.WF env Us.length ((none, .vlam (ty₀.liftN 1 k)) :: _) := ⟨hΔ', nofun, h1⟩
    obtain ⟨body₀, hbody₀, rfl⟩ := ih2 (W.cons (.vlam ty₀)) (.succ hI) hΔ'' hc.2
    have hΓ'' : OnCtx (ty₀.liftN 1 k :: _) (env.IsType Us.length) := ⟨hΔ'.toCtx, h1⟩
    have h2' := IsType.inhabited_inv henv.ordered (Ctx.Inserted.succ hI) h₀ h2
    exact ⟨_, .forallE h1' h2' hty₀ hbody₀, rfl⟩
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    obtain ⟨ty₀, hty₀, rfl⟩ := ih1 W hI hΔ' hc.1
    obtain ⟨val₀, hval₀, rfl⟩ := ih2 W hI hΔ' hc.2.1
    have h1' := HasType.inhabited_inv henv.ordered hI h₀ h1
    have hΔ'' : VLCtx.WF env Us.length ((none, .vlet (ty₀.liftN 1 k) (val₀.liftN 1 k)) :: _) :=
      ⟨hΔ', nofun, h1⟩
    obtain ⟨body₀, hbody₀, rfl⟩ := ih3 (W.cons (.vlet ty₀ val₀)) hI hΔ'' hc.2.2
    exact ⟨_, .letE h1' hty₀ hval₀ hbody₀, rfl⟩
  | lit h1 _ ih =>
    obtain ⟨_, h, rfl⟩ := ih W hI hΔ' Closed.toConstructor
    exact ⟨_, .lit h1 h, rfl⟩
  | mdata _ ih =>
    obtain ⟨_, h, rfl⟩ := ih W hI hΔ' hc
    exact ⟨_, .mdata h, rfl⟩
  | proj _ hp ih =>
    obtain ⟨s₀, hs₀, rfl⟩ := ih W hI hΔ' hc
    cases hp with | direct m t
    have m' := VExpr.WF.inhabited_inv henv.ordered hI h₀ m
    have t' := VExpr.WF.inhabited_inv henv.ordered hI h₀ (e := .proj _ _ s₀) t
    exact ⟨_, .proj hs₀ (.direct m' t'), rfl⟩


/-- A closed body under one binder whose type `D` is inhabited, by `d₀`, translates to a lift. -/
theorem TrExprS.weakBV_inv₁_inhabited {Δ : VLCtx} (henv : VEnv.WF env)
    (h₀ : env.HasType Us.length Δ.toCtx d₀ D)
    (hΔ : VLCtx.WF env Us.length ((none, .vlam D) :: Δ))
    (H : TrExprS env Us ((none, .vlam D) :: Δ) e e') (hc : Closed e) :
    ∃ e₀, TrExprS env Us Δ e e₀ ∧ e' = e₀.lift :=
  H.weakBV_inv_inhabited henv h₀ (.skip (.vlam D) .refl) .zero hΔ hc

end Lean4Lean
