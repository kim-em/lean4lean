import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.Typing.LevelEquiv
import Lean4Lean.WHNFCacheKey

namespace Lean4Lean
open VEnv Lean

def ConditionallyTyped
    (ngen : NameGenerator) (env : VEnv) (Us : List Name) (Δ : VLCtx) (e : Expr) : Prop :=
  Closed e ∧ FVarsIn ngen.Reserves e ∧ (FVarsIn (· ∈ Δ.fvars) e → ∃ e', TrExprS env Us Δ e e')

theorem ConditionallyTyped.mk {Δ : VLCtx}
    (noBV : Δ.NoBV) (r : FVarsIn ngen.Reserves e) (H : TrExprS env Us Δ e e') :
    ConditionallyTyped ngen env Us Δ e := ⟨noBV ▸ H.closed, r, fun _ => ⟨_, H⟩⟩

theorem ConditionallyTyped.mono (H : ngen₁ ≤ ngen₂) :
    ConditionallyTyped ngen₁ env Us Δ e → ConditionallyTyped ngen₂ env Us Δ e
  | ⟨h1, h2, h3⟩ => ⟨h1, h2.mono fun _ h => h.mono H, h3⟩

theorem ConditionallyTyped.fresh
    (henv : Ordered env) (hΔ : VLCtx.WF env Us.length ((some (⟨ngen.curr⟩, deps), d) :: Δ))
    (H : ConditionallyTyped ngen env Us Δ e) :
    ConditionallyTyped ngen env Us ((some (⟨ngen.curr⟩, deps), d) :: Δ) e := by
  refine have ⟨H1, H2, H3⟩ := H; ⟨H1, H2, fun H4 => ?_⟩
  refine have ⟨_, h⟩ := H3 (H4.mp ?_ H2); ⟨_, h.weakFV henv (.skip_fvar _ _ .refl) hΔ⟩
  intro _ h1 h2; simp at h1; rcases h1 with rfl | h1
  · cases Nat.lt_irrefl _ (h2 _ rfl)
  · exact h1

def ConditionallyHasType
    (ngen : NameGenerator) (env : VEnv) (Us : List Name) (Δ : VLCtx) (e A : Expr) : Prop :=
  Closed e ∧ FVarsIn ngen.Reserves e ∧ Closed A ∧ FVarsIn ngen.Reserves A ∧
    (FVarsIn (· ∈ Δ.fvars) e → ∃ e' A', TrTyping env Us Δ e A e' A')

theorem ConditionallyHasType.mk {Δ : VLCtx}
    (noBV : Δ.NoBV) (he : TrTyping env Us Δ e A e' A')
    (re : FVarsIn ngen.Reserves e) (rA : FVarsIn ngen.Reserves A) :
    ConditionallyHasType ngen env Us Δ e A := by
  refine ⟨noBV ▸ he.2.1.closed, re, noBV ▸ he.2.2.1.closed, rA, fun _ => ⟨_, _, he.1, he.2⟩⟩

theorem ConditionallyHasType.typed :
    ConditionallyHasType ngen env Us Δ e A → ConditionallyTyped ngen env Us Δ e
  | ⟨c1, f1, _, _, H⟩ => ⟨c1, f1, fun h => let ⟨_, _, _, h, _⟩ := H h; ⟨_, h⟩⟩

theorem ConditionallyHasType.mono (H : ngen₁ ≤ ngen₂) :
    ConditionallyHasType ngen₁ env Us Δ e A → ConditionallyHasType ngen₂ env Us Δ e A
  | ⟨c1, f1, c2, f2, h'⟩ => ⟨c1, f1.mono fun _ h => h.mono H, c2, f2.mono fun _ h => h.mono H, h'⟩

theorem ConditionallyHasType.fresh
    (henv : Ordered env)
    (hΔ : VLCtx.WF env Us.length ((some (⟨ngen.curr⟩, deps), d) :: Δ))
    (H : ConditionallyHasType ngen env Us Δ e A) :
    ConditionallyHasType ngen env Us ((some (⟨ngen.curr⟩, deps), d) :: Δ) e A := by
  refine have ⟨c1, f1, c2, f2, H⟩ := H; ⟨c1, f1, c2, f2, fun H4 => ?_⟩
  have ⟨_, _, h1, h2, h3, h4⟩ := H (H4.mp ?_ f1)
  · have W : VLCtx.FVLift Δ ((some (⟨ngen.curr⟩, deps), d) :: Δ) 0 (0 + d.depth) 0 :=
      .skip_fvar _ _ .refl
    exact ⟨_, _, fun P hP => h1 _ hP.1,
      h2.weakFV henv W hΔ, h3.weakFV henv W hΔ, h4.weakN henv W.toCtx⟩
  · intro _ h1 h2; simp at h1; rcases h1 with rfl | h1
    · cases Nat.lt_irrefl _ (h2 _ rfl)
    · exact h1

theorem whnfCacheKey_eqv {e e' : Expr} (h : e == e') :
    whnfCacheKey e = whnfCacheKey e' := by
  simp [(· == ·)] at h
  cases e <;> cases e' <;> first | rfl | (change false = true at h; cases h)

theorem TrExprS.cacheKey_not_forall (H : TrExprS env Us Δ e e')
    (hkey : whnfCacheKey e = true) : e' ≠ .forallE domain body := by
  cases H <;> simp only [whnfCacheKey] at hkey
  all_goals first | contradiction | (intro h; cases h)
  case proj hmajor hprojection => exact hprojection.target_not_forall rfl

/-- Cached inputs have heads whose translations cannot already be foralls.
The retained translation and equality remain valid under context changes;
no literal choice of a projection expansion is compared across witnesses. -/
def ConditionallyWHNF
    (ngen : NameGenerator) (env : VEnv) (Us : List Name) (Δ : VLCtx) (e e₁ : Expr) : Prop :=
  Closed e ∧ FVarsIn ngen.Reserves e ∧ Closed e₁ ∧ FVarsIn ngen.Reserves e₁ ∧
    (FVarsIn (· ∈ Δ.fvars) e → ∃ e',
      FVarsBelow Δ e e₁ ∧ TrExprS env Us Δ e e' ∧ TrExpr env Us Δ e₁ e' ∧
      whnfCacheKey e = true)

theorem ConditionallyWHNF.mk {Δ : VLCtx}
    (noBV : Δ.NoBV) (hb : FVarsBelow Δ e e₁)
    (he : TrExprS env Us Δ e e') (he₁ : TrExpr env Us Δ e₁ e')
    (hkey : whnfCacheKey e = true)
    (re : FVarsIn ngen.Reserves e) (re₁ : FVarsIn ngen.Reserves e₁) :
    ConditionallyWHNF ngen env Us Δ e e₁ := by
  refine ⟨noBV ▸ he.closed, re, noBV ▸ he₁.closed, re₁, fun _ => ⟨_, hb, he, he₁, hkey⟩⟩

theorem ConditionallyWHNF.mono (H : ngen₁ ≤ ngen₂) :
    ConditionallyWHNF ngen₁ env Us Δ e A → ConditionallyWHNF ngen₂ env Us Δ e A
  | ⟨c1, f1, c2, f2, h'⟩ => ⟨c1, f1.mono fun _ h => h.mono H, c2, f2.mono fun _ h => h.mono H, h'⟩

theorem ConditionallyWHNF.fresh
    (henv : env.WF)
    (hΔ : VLCtx.WF env Us.length ((some (⟨ngen.curr⟩, deps), d) :: Δ))
    (H : ConditionallyWHNF ngen env Us Δ e e₁) :
    ConditionallyWHNF ngen env Us ((some (⟨ngen.curr⟩, deps), d) :: Δ) e e₁ := by
  refine have ⟨c1, f1, c2, f2, H⟩ := H; ⟨c1, f1, c2, f2, fun H4 => ?_⟩
  have ⟨e', h1, h2, h3, h5⟩ := H (H4.mp ?_ f1)
  · have W : VLCtx.FVLift Δ ((some (⟨ngen.curr⟩, deps), d) :: Δ) 0 (0 + d.depth) 0 :=
      .skip_fvar _ _ .refl
    exact ⟨_, fun P hP => h1 _ hP.1, h2.weakFV henv W hΔ, h3.weakFV henv W hΔ, h5⟩
  · intro _ h1 h2; simp at h1; rcases h1 with rfl | h1
    · cases Nat.lt_irrefl _ (h2 _ rfl)
    · exact h1
