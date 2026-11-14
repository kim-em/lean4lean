import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.EqTyping

/-! # Strengthening reduces to one absurd binder

In a well-formed environment with canonical `Eq`, context strengthening of definitional
equality (the statement of `IsDefEqU.weakN_iff`) is equivalent to its special case for a single
binder of type `∀ p : Prop, p` at the front of the context (`AbsurdStrengthening`):

```text
z : ∀ p : Prop, p, Γ ⊢ e₁ ≡ e₂   implies   Γ ⊢ e₁ ≡ e₂      (e₁, e₂ not mentioning z)
```

The equivalence is `absurdStrengthening_iff`. The reduction has three steps.

* A hypothesis `z : ∀ p : Prop, p` inhabits every type `A : Sort u` (`exists_absurd_inhabitant`):
  cast the identity function along `z ((A → A) = A)`. So a derivation under a binder `x : A`
  becomes one under `z` by substituting the inhabitant for `x`, and this fixes every term that
  does not mention `x` (`AbsurdAt.map`).
* A binder `z` below `k` further binders moves to the front by abstracting those binders: the
  two sides become lambdas, and a definitional equality of lambdas over the same domain gives
  one of their bodies (`IsDefEqU.lam_body`).
* A block of `n` binders is removed one binder at a time (`Ctx.LiftN.split`). -/

namespace Lean4Lean
namespace VEnv
namespace Strengthening

open VExpr

variable {env : VEnv} {U : Nat}

/-- `∀ p : Prop, p`. -/
def absurd : VExpr := .forallE (.sort .zero) (.bvar 0)

/-- Strengthening for one binder of type `∀ p : Prop, p` at the front of the context. -/
def AbsurdStrengthening (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e1 e2 : VExpr}, OnCtx Γ (env.IsType U) →
    env.IsDefEqU U (absurd :: Γ) e1.lift e2.lift → env.IsDefEqU U Γ e1 e2

/-- Strengthening for every block of binders, at every depth: the statement of
`IsDefEqU.weakN_iff` for the environment `env` and `U` universe variables. -/
def FullStrengthening (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr},
    OnCtx Γ' (env.IsType U) → Ctx.LiftN n k Γ Γ' →
    (env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) ↔ env.IsDefEqU U Γ e1 e2)

theorem absurd_hasType : env.HasType U Γ absurd (.sort (.imax (.succ .zero) .zero)) :=
  .forallE (.sort (by exact trivial)) (.bvar .zero)

theorem absurd_isType : env.IsType U Γ absurd := ⟨_, absurd_hasType⟩

/-! ## An absurd hypothesis inhabits every type -/

/-- Under `z : ∀ p : Prop, p`, every type of the context below `z` is inhabited. -/
theorem exists_absurd_inhabitant (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (hA : env.IsType U Γ A) :
    ∃ e, env.HasType U (absurd :: Γ) e A.lift := by
  obtain ⟨u, hA⟩ := hA
  have hu : u.WF U := hA.sort_r henv.ordered hΓ
  have hX : env.HasType U (absurd :: Γ) A.lift (.sort u) := hA.weak henv.ordered
  have hX' : env.HasType U (A.lift :: absurd :: Γ) A.lift.lift (.sort u) := hX.weak henv.ordered
  -- `A → A : Sort u`
  have hXX : env.HasType U (absurd :: Γ) (.forallE A.lift A.lift.lift) (.sort u) :=
    (IsDefEq.sortDF (l := .imax u u) (l' := u) ⟨hu, hu⟩ hu VLevel.imax_self).defeq
      (.forallE hX hX')
  have hid : env.HasType U (absurd :: Γ) (.lam A.lift (.bvar 0)) (.forallE A.lift A.lift.lift) :=
    .lam hX (.bvar .zero)
  -- `z ((A → A) = A) : (A → A) = A`
  have hE : env.HasType U (absurd :: Γ)
      (eqApp (.succ u) (.sort u) (.forallE A.lift A.lift.lift) A.lift) (.sort .zero) :=
    HasType.eqApp heq (w := .succ u) hu (.sort hu) hXX hX
  have hz : env.HasType U (absurd :: Γ) (.bvar 0) absurd := by
    have : env.HasType U (absurd :: Γ) (.bvar 0) absurd.lift := .bvar .zero
    simpa [absurd, VExpr.liftN, liftVar] using this
  have hp := HasType.app' hz hE (B' := eqApp (.succ u) (.sort u)
    (.forallE A.lift A.lift.lift) A.lift) (by simp [VExpr.inst, instVar])
  exact ⟨_, HasType.typeCast henv.ordered heq hu hXX hX hp hid⟩

/-! ## One absurd binder at depth `k` -/

/-- `AbsurdAt k Γ Γ'`: the context `Γ'` is `Γ` with a binder of type `∀ p : Prop, p` inserted
below its first `k` binders. -/
inductive AbsurdAt : Nat → List VExpr → List VExpr → Prop where
  | zero : AbsurdAt 0 Γ (absurd :: Γ)
  | succ : AbsurdAt k Γ Γ' → AbsurdAt (k+1) (B :: Γ) (B.liftN 1 k :: Γ')

theorem AbsurdAt.liftN : AbsurdAt k Γ Γ' → Ctx.LiftN 1 k Γ Γ'
  | .zero => .one
  | .succ h => .succ h.liftN

theorem exists_absurdAt (W : Ctx.LiftN 1 k Γ Γ') : ∃ Γ'', AbsurdAt k Γ Γ'' := by
  induction W with
  | zero => exact ⟨_, .zero⟩
  | succ _ ih => let ⟨_, h⟩ := ih; exact ⟨_, .succ h⟩

/-- A term that does not mention the variable `k` is unchanged by weakening below that variable
and then instantiating it. -/
theorem liftN_liftN_inst (e e₀ : VExpr) (k : Nat) :
    ((e.liftN 1 k).liftN 1 (k+1)).inst e₀ k = e.liftN 1 k := by
  rw [liftN'_liftN' (Nat.le_succ k) (by omega), inst_liftN']

/-- Replacing the binder at depth `k` by an absurd one factors through the context with both
binders: a weakening followed by an instantiation. -/
theorem AbsurdAt.mid (Wa : AbsurdAt k Γ Γ'') (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ' : OnCtx Γ' (env.IsType U)) :
    ∃ A Γ₀, OnCtx Γ₀ (env.IsType U) ∧ env.IsType U Γ₀ A ∧ ∀ e₀, ∃ Γ₂,
      Ctx.LiftN 1 (k+1) Γ' Γ₂ ∧ Ctx.InstN (absurd :: Γ₀) e₀ A.lift k Γ₂ Γ'' := by
  induction Wa generalizing Γ' with
  | zero =>
    cases W with | zero As h =>
    match As, h with
    | [A], _ =>
      exact ⟨A, _, hΓ'.1, hΓ'.2, fun e₀ => ⟨_, .succ (A := A) (.zero [absurd]), .zero⟩⟩
  | @succ k Γ Γ'' B _ ih =>
    cases W with | succ W =>
    obtain ⟨A, Γ₀, h1, h2, h3⟩ := ih W hΓ'.1
    refine ⟨A, Γ₀, h1, h2, fun e₀ => ?_⟩
    obtain ⟨Γ₂, W₂, I⟩ := h3 e₀
    refine ⟨_, .succ W₂, ?_⟩
    have := Ctx.InstN.succ (A := (B.liftN 1 k).liftN 1 (k+1)) I
    rwa [liftN_liftN_inst] at this

/-- A derivation under a binder at depth `k` gives one with that binder replaced by an absurd
one, between the same terms when they do not mention the binder. -/
theorem AbsurdAt.map {e1 e2 T : VExpr} (henv : env.WF) (heq : env.HasCanonicalEq)
    (Wa : AbsurdAt k Γ Γ'') (W : Ctx.LiftN 1 k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U))
    (H : env.IsDefEq U Γ' (e1.liftN 1 k) (e2.liftN 1 k) T) :
    ∃ e₀, env.IsDefEq U Γ'' (e1.liftN 1 k) (e2.liftN 1 k) ((T.liftN 1 (k+1)).inst e₀ k) := by
  obtain ⟨A, Γ₀, hΓ₀, hA, h⟩ := Wa.mid W hΓ'
  obtain ⟨e₀, he₀⟩ := exists_absurd_inhabitant henv heq hΓ₀ hA
  obtain ⟨Γ₂, W₂, I⟩ := h e₀
  have := (H.weakN henv.ordered W₂).instN henv.ordered he₀ I
  refine ⟨e₀, ?_⟩
  simpa only [liftN_liftN_inst] using this

theorem AbsurdAt.onCtx (henv : env.WF) (heq : env.HasCanonicalEq)
    (Wa : AbsurdAt k Γ Γ'') (W : Ctx.LiftN 1 k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U)) :
    OnCtx Γ'' (env.IsType U) := by
  induction Wa generalizing Γ' with
  | zero =>
    cases W with | zero As h =>
    match As, h with
    | [A], _ => exact ⟨hΓ'.1, absurd_isType⟩
  | succ Wa ih =>
    cases W with | succ W =>
    obtain ⟨hΓ', u, hB⟩ := hΓ'
    obtain ⟨e₀, h⟩ := Wa.map henv heq W hΓ' (T := .sort u) hB
    exact ⟨ih W hΓ', u, by simpa [VEnv.HasType, VExpr.liftN, VExpr.inst] using h⟩

/-! ## Moving the absurd binder to the front -/

/-- Strengthening of typed equalities from strengthening of untyped ones. -/
theorem IsDefEq.of_weakN {e1 e2 A : VExpr} (henv : env.WF)
    (hΓ' : OnCtx Γ' (env.IsType U)) (hΓ : OnCtx Γ (env.IsType U)) (W : Ctx.LiftN n k Γ Γ')
    (str : ∀ {e1 e2 : VExpr}, env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) → env.IsDefEqU U Γ e1 e2)
    (h : env.IsDefEq U Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k)) :
    env.IsDefEq U Γ e1 e2 A := by
  have ⟨_, H⟩ := str ⟨_, h⟩
  refine IsDefEqU.defeqDF henv hΓ ?_ H
  exact str <| (H.weakN henv.ordered W).uniqU henv hΓ' h.symm

/-- Two lambdas over the same domain that are definitionally equal have definitionally equal
bodies. -/
theorem IsDefEqU.lam_body (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hB : env.IsType U Γ B)
    (H : env.IsDefEqU U Γ (.lam B e1) (.lam B e2)) : env.IsDefEqU U (B :: Γ) e1 e2 := by
  obtain ⟨T, H⟩ := H
  have hΓB : OnCtx (B :: Γ) (env.IsType U) := ⟨hΓ, hB⟩
  obtain ⟨B₁, hT₁, h1⟩ := HasType.lam_inv_forallE henv hΓ H.hasType.1
  obtain ⟨B₂, -, h2⟩ := HasType.lam_inv_forallE henv hΓ H.hasType.2
  have H' := (hT₁.symm.defeqDF henv hΓ H).weak henv.ordered (B := B)
  have hv : env.HasType U (B :: Γ) (.bvar 0) B.lift := .bvar .zero
  have W : Ctx.LiftN 1 1 (B :: Γ) (B.lift :: B :: Γ) := .succ .one
  -- the applications of the two weakened lambdas to the new variable
  have happ := IsDefEq.appDF H' hv
  have hb1 := IsDefEq.beta (h1.weakN henv.ordered W) hv
  have hb2 := IsDefEq.beta (h2.weakN henv.ordered W) hv
  simp only [instN_bvar0] at hb1 hb2
  exact (IsDefEqU.trans henv hΓB ⟨_, hb1.symm⟩ ⟨_, happ⟩).trans henv hΓB ⟨_, hb2⟩

/-- Strengthening for an absurd binder at any depth, from strengthening for one at the front. -/
theorem AbsurdAt.strengthening (henv : env.WF) (H : AbsurdStrengthening env U)
    (Wa : AbsurdAt k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U)) :
    OnCtx Γ (env.IsType U) ∧ ∀ {e1 e2 : VExpr},
      env.IsDefEqU U Γ' (e1.liftN 1 k) (e2.liftN 1 k) → env.IsDefEqU U Γ e1 e2 := by
  induction Wa with
  | zero => exact ⟨hΓ'.1, fun h => H hΓ'.1 h⟩
  | @succ k Γ Γ' B Wa ih =>
    obtain ⟨hΓ', u, hB'⟩ := hΓ'
    obtain ⟨hΓ, str⟩ := ih hΓ'
    have hB : env.HasType U Γ B (.sort u) :=
      IsDefEq.of_weakN henv hΓ' hΓ Wa.liftN str (A := .sort u) hB'
    refine ⟨⟨hΓ, u, hB⟩, fun ⟨T, h⟩ => ?_⟩
    exact IsDefEqU.lam_body henv hΓ ⟨u, hB⟩ <| str (e1 := .lam B _) (e2 := .lam B _)
      ⟨_, IsDefEq.lamDF hB' h⟩

/-! ## The reduction -/

/-- Strengthening for one binder at any depth. -/
theorem strengthening_one (henv : env.WF) (heq : env.HasCanonicalEq)
    (H : AbsurdStrengthening env U) (W : Ctx.LiftN 1 k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U)) :
    OnCtx Γ (env.IsType U) ∧ ∀ {e1 e2 : VExpr},
      env.IsDefEqU U Γ' (e1.liftN 1 k) (e2.liftN 1 k) → env.IsDefEqU U Γ e1 e2 := by
  obtain ⟨Γ'', Wa⟩ := exists_absurdAt W
  obtain ⟨hΓ, str⟩ := Wa.strengthening henv H (Wa.onCtx henv heq W hΓ')
  exact ⟨hΓ, fun ⟨_, h⟩ => let ⟨_, h⟩ := Wa.map henv heq W hΓ' h; str ⟨_, h⟩⟩

end Strengthening

/-- A block of `n + 1` binders is a block of `n` binders followed by one more. -/
theorem _root_.Lean4Lean.Ctx.LiftN.split (W : Ctx.LiftN (n+1) k Γ Γ') :
    ∃ Γ₁, Ctx.LiftN n k Γ Γ₁ ∧ Ctx.LiftN 1 k Γ₁ Γ' := by
  induction W with
  | zero As h =>
    match As, h with
    | A :: As, h => exact ⟨As ++ _, .zero As (by simpa using h), .zero [A]⟩
  | @succ k Γ Γ' B _ ih =>
    obtain ⟨Γ₁, W₁, W₂⟩ := ih
    refine ⟨_, .succ W₁, ?_⟩
    have := Ctx.LiftN.succ (A := B.liftN n k) W₂
    rwa [VExpr.liftN'_liftN' (Nat.le_refl _) (Nat.le_add_left _ _)] at this

theorem _root_.Lean4Lean.Ctx.LiftN.eq_of_zero (W : Ctx.LiftN 0 k Γ Γ') : Γ' = Γ := by
  induction W with
  | zero As h =>
    match As, h with
    | [], _ => rfl
  | succ _ ih => simp [ih]

namespace Strengthening

variable {env : VEnv} {U : Nat}

/-- **Strengthening reduces to one absurd binder**: in a well-formed environment with canonical
`Eq`, strengthening for a binder of type `∀ p : Prop, p` at the front of the context gives
strengthening for every block of binders at every depth. -/
theorem AbsurdStrengthening.full (henv : env.WF) (heq : env.HasCanonicalEq)
    (H : AbsurdStrengthening env U) : FullStrengthening env U := by
  suffices ∀ n {k Γ Γ'}, Ctx.LiftN n k Γ Γ' → OnCtx Γ' (env.IsType U) →
      OnCtx Γ (env.IsType U) ∧ ∀ {e1 e2 : VExpr},
        env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) → env.IsDefEqU U Γ e1 e2 by
    intro n k Γ Γ' e1 e2 hΓ' W
    exact ⟨(this _ W hΓ').2, fun h => h.weakN henv.ordered W⟩
  intro n
  induction n with
  | zero =>
    intro k Γ Γ' W hΓ'
    cases W.eq_of_zero
    exact ⟨hΓ', fun h => by simpa using h⟩
  | succ n ih =>
    intro k Γ Γ' W hΓ'
    obtain ⟨Γ₁, W₁, W₂⟩ := W.split
    obtain ⟨hΓ₁, str₁⟩ := strengthening_one henv heq H W₂ hΓ'
    obtain ⟨hΓ, str⟩ := ih W₁ hΓ₁
    refine ⟨hΓ, fun h => str (str₁ ?_)⟩
    simpa only [VExpr.liftN'_liftN' (Nat.le_refl _) (Nat.le_add_left _ _)] using h

/-- In a well-formed environment with canonical `Eq`, strengthening is equivalent to
strengthening for one binder of type `∀ p : Prop, p` at the front of the context. -/
theorem absurdStrengthening_iff (henv : env.WF) (heq : env.HasCanonicalEq) :
    AbsurdStrengthening env U ↔ FullStrengthening env U := by
  refine ⟨AbsurdStrengthening.full henv heq, fun H => ?_⟩
  intro Γ e1 e2 hΓ h
  have hΓ' : OnCtx (absurd :: Γ) (env.IsType U) := ⟨hΓ, absurd_isType⟩
  exact (H (n := 1) (k := 0) hΓ' .one).1 h

end Strengthening
end VEnv
end Lean4Lean
