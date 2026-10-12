import Lean4Lean.Theory.Typing.Strengthening.TypingFront
import Lean4Lean.Theory.Typing.Confluence.WFParams

/-! # The typing front along any single-binder insertion and its one-step closures

`TypingFrontN`: typing descent along any single-binder insertion `Ctx.LiftN 1 k Γ Γ'`
(equivalent to `TypingFront` and, under canonical `Eq`, to `Cancel`). The structural
induction on the term reduces it exactly to three one-step closures
(`typingFrontN_iff_closures`), each necessary:

* `AppFrontN`: an application of terms typable below, typable above, is typable below;
* `TypeFrontN`: two types of `Γ` with convertible lifts are convertible (`TypedFront` in
  `LiftN` form; the `λ`/`Π` cases need it as sort exposure, `TypeFrontN.sort`);
* `ProjFrontN`: the projection closure.

`AppFrontN` follows from existential `Π`-exposure `PiExposureN` and `TypeFrontN`
(`AppFrontN.of_piExposure`); conversely `AppFrontN.piExposure` is exposure for a lifted
inhabited domain. Under canonical `Eq`, exposure in conversion form follows from exposure in
reduction form `PiExposureRedN` (`exposure_reduces`: a type convertible to a `Π` reduces to a
`Π`, by `WF.church_rosser` and the `Π`-stability of `FullStep` and `NormalEqN`).

This is PR #53's `TypingFront.lean` (part 2) on the present calculus: there is no `.elim`
constructor and no case schema, so the eliminator closure `ElimFrontN` and the schema case of
the `Π`-stability lemmas disappear. -/

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean.VExpr
variable {env : VEnv} {U : Nat} {Γ : List VExpr}

/-! ## Typing descent along any single-binder insertion -/

def TypingFrontN (env : VEnv) : Prop :=
  ∀ ⦃U k Γ Γ' e T⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ' (e.liftN 1 k) T → ∃ T₀, env.HasType U Γ e T₀

theorem typingFront_of_typingFrontN (H : TypingFrontN env) : TypingFront env :=
  fun _ _ _ _ _ hΓ he => H Ctx.LiftN.one hΓ.1 hΓ he

theorem typingFrontN_of_cancel (henv : env.WF) (hc : Cancel env) : TypingFrontN env :=
  fun _ _ _ _ _ _ W _ hΓ' he => Strengthening.of_cancel henv hc W hΓ' ⟨_, he⟩

theorem typingFrontN_iff_cancel (henv : env.WF) (heq : env.HasCanonicalEq) :
    TypingFrontN env ↔ Cancel env :=
  ⟨fun H => cancel_of_typingFront henv heq (typingFront_of_typingFrontN H),
    typingFrontN_of_cancel henv⟩

/-! ## The one-step closures -/

def AppFrontN (env : VEnv) : Prop :=
  ∀ ⦃U k Γ Γ' f a F A T⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ f F → env.HasType U Γ a A →
    env.HasType U Γ' (.app (f.liftN 1 k) (a.liftN 1 k)) T → ∃ T₀, env.HasType U Γ (.app f a) T₀

def ProjFrontN (env : VEnv) : Prop :=
  ∀ ⦃U k Γ Γ' S i m M T⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ m M → env.HasType U Γ' (.proj S i (m.liftN 1 k)) T →
    ∃ T₀, env.HasType U Γ (.proj S i m) T₀

/-- Existential `Π`-exposure: the type of a function typed below whose lift is convertible
above to a `Π` is convertible below to some `Π`. -/
def PiExposureN (env : VEnv) : Prop :=
  ∀ ⦃U k Γ Γ' f F A B⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ f F → env.IsDefEqU U Γ' (F.liftN 1 k) (.forallE A B) →
    ∃ A₀ B₀, env.IsDefEqU U Γ F (.forallE A₀ B₀)

theorem lookup_append_inv : ∀ (As : List VExpr), Lookup (As ++ Γ) (As.length + i) A' →
    ∃ A, Lookup Γ i A
  | [], h => ⟨_, by simpa using h⟩
  | _ :: As, h => by
    rw [List.length_cons, Nat.add_right_comm] at h
    cases h with
    | succ h => exact lookup_append_inv As h

theorem Lookup.of_liftN (W : Ctx.LiftN n k Γ Γ') (H : Lookup Γ' (liftVar n i k) A') :
    ∃ A, Lookup Γ i A := by
  induction W generalizing i A' with
  | zero As hn =>
    subst hn
    rw [liftVar_base] at H
    exact lookup_append_inv As H
  | succ _ ih =>
    cases i with
    | zero => exact ⟨_, .zero⟩
    | succ i =>
      rw [liftVar_succ] at H
      cases H with
      | succ H =>
        obtain ⟨A, hA⟩ := ih H
        exact ⟨_, .succ hA⟩

/-- Sort exposure for a type of `Γ` whose lift is a sort above, from the type front. -/
theorem TypeFrontN.sort (henv : env.WF) (hTy : TypeFrontN env) (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    (hA : env.HasType U Γ A T) (hA' : env.HasType U Γ' (A.liftN 1 k) (.sort u)) :
    env.HasType U Γ A (.sort u) := by
  obtain ⟨w, hT⟩ := hA.isType henv.ordered hΓ
  have hu := hA'.sort_r henv.ordered hΓ'
  have h1 : env.IsDefEqU U Γ' (T.liftN 1 k) ((VExpr.sort u).liftN 1 k) :=
    (hA.weakN henv.ordered W).uniqU henv hΓ' hA'
  exact hA.defeqU_r henv hΓ (hTy W hΓ hΓ' hT (.sort hu) h1)

/-- The structural induction: the typing front follows from its one-step closures. -/
theorem typingFrontN_of_closures (henv : env.WF) (hApp : AppFrontN env) (hTy : TypeFrontN env)
    (hProj : ProjFrontN env) : TypingFrontN env := by
  intro U k Γ Γ' e T W hΓ hΓ' he
  induction e generalizing k Γ Γ' T with
  | bvar i =>
    obtain ⟨A', hA'⟩ := he.bvar_inv henv hΓ'
    obtain ⟨A, hA⟩ := Lookup.of_liftN W hA'
    exact ⟨_, .bvar hA⟩
  | sort u => exact ⟨_, .sort (he.sort_inv henv.ordered)⟩
  | const c ls =>
    obtain ⟨ci, h1, h2, h3⟩ := he.const_inv henv hΓ'
    exact ⟨_, .const h1 h2 h3⟩
  | app f a ihf iha =>
    obtain ⟨A, B, hf, ha⟩ := he.app_inv henv hΓ'
    obtain ⟨F, hF⟩ := ihf W hΓ hΓ' hf
    obtain ⟨A₀, hA₀⟩ := iha W hΓ hΓ' ha
    exact hApp W hΓ hΓ' hF hA₀ he
  | lam A b ihA ihb =>
    obtain ⟨⟨u, hA'⟩, _, hb'⟩ := he.lam_inv henv hΓ'
    obtain ⟨TA, hTA⟩ := ihA W hΓ hΓ' hA'
    have hA := TypeFrontN.sort henv hTy W hΓ hΓ' hTA hA'
    obtain ⟨Tb, hTb⟩ := ihb W.succ ⟨hΓ, u, hA⟩ ⟨hΓ', u, hA'⟩ hb'
    exact ⟨_, .lam hA hTb⟩
  | forallE A B ihA ihB =>
    obtain ⟨⟨u, hA'⟩, v, hB'⟩ := he.forallE_inv henv.ordered
    obtain ⟨TA, hTA⟩ := ihA W hΓ hΓ' hA'
    have hA := TypeFrontN.sort henv hTy W hΓ hΓ' hTA hA'
    have hΓA : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, u, hA⟩
    have hΓA' : OnCtx (A.liftN 1 k :: Γ') (env.IsType U) := ⟨hΓ', u, hA'⟩
    obtain ⟨TB, hTB⟩ := ihB W.succ hΓA hΓA' hB'
    have hB := TypeFrontN.sort henv hTy W.succ hΓA hΓA' hTB hB'
    exact ⟨_, .forallE hA hB⟩
  | proj S i m ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ'
    obtain ⟨M, hM⟩ := ih W hΓ hΓ' hm.hasType.2
    exact hProj W hΓ hΓ' hM he

/-! ### The closures are necessary -/

theorem AppFrontN.of_typingFrontN (H : TypingFrontN env) : AppFrontN env :=
  fun _ _ _ _ _ _ _ _ _ W hΓ hΓ' _ _ he => H W hΓ hΓ' he

theorem ProjFrontN.of_typingFrontN (H : TypingFrontN env) : ProjFrontN env :=
  fun _ _ _ _ _ _ _ _ _ W hΓ hΓ' _ he => H W hΓ hΓ' he

theorem liftN_lift_succ (e : VExpr) (k : Nat) : e.lift.liftN 1 (k+1) = (e.liftN 1 k).lift :=
  (lift_liftN' e k).symm

/-- The type front is the typing front at the ascription `(λ x : Π B. B↑. x) (λ x : A. x)`. -/
theorem TypeFrontN.of_typingFrontN (henv : env.WF) (H : TypingFrontN env) : TypeFrontN env := by
  intro U k Γ Γ' A B u v W hΓ hΓ' hA hB hAB
  have hid : env.HasType U Γ (.lam A (.bvar 0)) (.forallE A A.lift) := .lam hA (.bvar .zero)
  have hA' : env.HasType U Γ' (A.liftN 1 k) (.sort u) := hA.weakN henv.ordered W
  have hAB' := hAB.of_l henv hΓ' hA'
  have hPi : env.IsDefEq U Γ' (.forallE (A.liftN 1 k) (A.liftN 1 k).lift)
      (.forallE (B.liftN 1 k) (B.liftN 1 k).lift) (.sort (.imax u u)) :=
    .forallEDF hAB' (hAB'.weak henv.ordered)
  have hid' : env.HasType U Γ' ((VExpr.lam A (.bvar 0)).liftN 1 k)
      (.forallE (B.liftN 1 k) (B.liftN 1 k).lift) := by
    have := hid.weakN henv.ordered W
    simp only [liftN, liftVar_zero, liftN_lift_succ] at this ⊢
    exact hPi.defeq this
  have hasc := ascribe_typed henv.ordered hΓ' hid'
  have hasc' : env.HasType U Γ' ((ascribe (.lam A (.bvar 0)) (.forallE B B.lift)).liftN 1 k)
      (.forallE (B.liftN 1 k) (B.liftN 1 k).lift) := by
    simpa only [ascribe, liftN, liftVar_zero, liftN_lift_succ] using hasc
  obtain ⟨T₀, hT₀⟩ := H W hΓ hΓ' hasc'
  have hidB := ascribe_inv henv hΓ hT₀
  obtain ⟨_, h⟩ := ((hid.uniqU henv hΓ hidB).forallE_inv henv hΓ).1
  exact ⟨_, h⟩

theorem typingFrontN_iff_closures (henv : env.WF) :
    TypingFrontN env ↔ AppFrontN env ∧ TypeFrontN env ∧ ProjFrontN env :=
  ⟨fun H => ⟨AppFrontN.of_typingFrontN H, TypeFrontN.of_typingFrontN henv H,
    ProjFrontN.of_typingFrontN H⟩,
    fun h => typingFrontN_of_closures henv h.1 h.2.1 h.2.2⟩

theorem typeFrontN_of_typedFrontN (henv : env.WF) (H : TypedFrontN env) : TypeFrontN env := by
  intro U k Γ Γ' A B u v W hΓ hΓ' hA hB hAB
  have hA' : env.HasType U Γ' (A.liftN 1 k) (.sort u) := hA.weakN henv.ordered W
  have hB' : env.HasType U Γ' (B.liftN 1 k) (.sort v) := hB.weakN henv.ordered W
  have hd := hAB.of_l henv hΓ' hA'
  have huv := (hd.uniqU henv hΓ' hB').sort_inv henv hΓ'
  have hBu : env.HasType U Γ B (.sort u) :=
    (IsDefEq.sortDF (hB.sort_r henv.ordered hΓ) (hA.sort_r henv.ordered hΓ)
      (Eq.symm huv)).defeq hB
  exact ⟨_, H W hΓ hΓ' hA hBu hd⟩

/-- The type front gives the typed front along any single-binder insertion, by the `Eq`
encoding of `typedFront_of_typeFront`. -/
theorem typedFrontN_of_typeFrontN (henv : env.WF) (heq : env.HasCanonicalEq)
    (H : TypeFrontN env) : TypedFrontN env := by
  intro U k Γ Γ' a b T W hΓ hΓ' ha hb hab
  obtain ⟨u, hT⟩ := ha.isType henv.ordered hΓ
  have hu := hT.sort_r henv.ordered hΓ
  have hT' : env.HasType U Γ' (T.liftN 1 k) (.sort u) := hT.weakN henv.ordered W
  have ha' : env.HasType U Γ' (a.liftN 1 k) (T.liftN 1 k) := ha.weakN henv.ordered W
  have e1 := IsDefEq.eqApp_r heq hu hT' ha' hab
  have e2 : env.IsDefEqU U Γ' ((eqApp u T a a).liftN 1 k) ((eqApp u T a b).liftN 1 k) :=
    ⟨_, by simpa only [eqApp, liftN] using e1⟩
  have h := H W hΓ hΓ' (HasType.eqApp heq hu hT ha ha) (HasType.eqApp heq hu hT ha hb) e2
  exact (eqApp_injective henv heq hΓ hT ha hu h).of_l henv hΓ ha

theorem typedFrontN_iff_typeFrontN (henv : env.WF) (heq : env.HasCanonicalEq) :
    TypedFrontN env ↔ TypeFrontN env :=
  ⟨typeFrontN_of_typedFrontN henv, typedFrontN_of_typeFrontN henv heq⟩

/-! ### The application closure from exposure and domain agreement -/

theorem AppFrontN.of_piExposure (henv : env.WF) (hPi : PiExposureN env) (hTy : TypeFrontN env) :
    AppFrontN env := by
  intro U k Γ Γ' f a F A T W hΓ hΓ' hf ha he
  obtain ⟨A', B', hf', ha'⟩ := he.app_inv henv hΓ'
  have hF' := (hf.weakN henv.ordered W).uniqU henv hΓ' hf'
  obtain ⟨A₀, B₀, hFPi⟩ := hPi W hΓ hΓ' hf hF'
  have hfPi : env.HasType U Γ f (.forallE A₀ B₀) := hf.defeqU_r henv hΓ hFPi
  have h1 : env.IsDefEqU U Γ' ((VExpr.forallE A₀ B₀).liftN 1 k) (.forallE A' B') :=
    (hFPi.weakN henv.ordered W).symm.trans henv hΓ' hF'
  obtain ⟨⟨_, hdom⟩, _⟩ := h1.forallE_inv henv hΓ'
  have hAA₀ : env.IsDefEqU U Γ' (A.liftN 1 k) (A₀.liftN 1 k) :=
    ((ha.weakN henv.ordered W).uniqU henv hΓ' ha').trans henv hΓ' ⟨_, hdom.symm⟩
  obtain ⟨u, hAs⟩ := ha.isType henv.ordered hΓ
  obtain ⟨_, hPis⟩ := hfPi.isType henv.ordered hΓ
  obtain ⟨⟨v, hA₀s⟩, _⟩ := hPis.forallE_inv henv.ordered
  exact ⟨_, .app hfPi (ha.defeqU_r henv hΓ (hTy W hΓ hΓ' hAs hA₀s hAA₀))⟩

/-- Exposure with a lifted inhabited domain is the application closure. -/
theorem AppFrontN.piExposure (henv : env.WF) (hApp : AppFrontN env) (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    (hf : env.HasType U Γ f F) (ha : env.HasType U Γ a A₀)
    (hF : env.IsDefEqU U Γ' (F.liftN 1 k) (.forallE (A₀.liftN 1 k) B)) :
    ∃ A₁ B₁, env.IsDefEqU U Γ F (.forallE A₁ B₁) := by
  have hf' : env.HasType U Γ' (f.liftN 1 k) (.forallE (A₀.liftN 1 k) B) :=
    (hf.weakN henv.ordered W).defeqU_r henv hΓ' hF
  obtain ⟨T₀, hT₀⟩ := hApp W hΓ hΓ' hf ha (hf'.app (ha.weakN henv.ordered W))
  obtain ⟨A₁, B₁, hf₁, _⟩ := hT₀.app_inv henv hΓ
  exact ⟨A₁, B₁, hf.uniqU henv hΓ hf₁⟩

/-! ## Exposure through reduction -/

section Reduction
open VEnv.Params
variable [VEnv.Params]

theorem parRed_forallE_inv (H : ParRed Γ (.forallE A B) e') : ∃ A' B', e' = .forallE A' B' := by
  generalize he : VExpr.forallE A B = e at H
  cases H with
  | forallE => exact ⟨_, _, rfl⟩
  | extra hp hm =>
    obtain ⟨sp, rfl⟩ := pat_simple hp
    obtain ⟨name, hhead⟩ := SimplePattern.recursor_pattern_head hm
    rw [← he] at hhead
    cases hhead
  | _ => cases he

/-- A `Π` type steps only to a `Π`. -/
theorem fullStep_forallE_inv (hΓ : OnCtx Γ (Params.env.IsType univs))
    (ht : Params.env.HasType univs Γ (.forallE A B) (.sort u))
    (H : FullStep Γ (.forallE A B) e') : ∃ A' B', e' = .forallE A' B' := by
  generalize he : VExpr.forallE A B = e at H
  cases H with
  | core h => subst he; exact parRed_forallE_inv h
  | forallE _ _ => exact ⟨_, _, rfl⟩
  | delta h => exact False.elim (VExpr.mkApps_ne_forallE (by intros; intro h; cases h) _ he.symm)
  | quotDelta h =>
    exact False.elim (VExpr.mkApps_ne_forallE (by intros; intro h; cases h) _ he.symm)
  | structEta hi _ _ hs _ =>
    subst he
    exact False.elim (henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
      ((ht.uniqU henv hΓ hs).typeChain henv hΓ (.sort (ht.sort_r henv.ordered hΓ))))
  | funEta hf =>
    subst he
    exact False.elim (IsDefEqU.sort_forallE_inv henv hΓ (ht.uniqU henv hΓ hf))
  | _ => cases he

theorem fullReduction_forallE_inv (hΓ : OnCtx Γ (Params.env.IsType univs))
    (ht : Params.env.HasType univs Γ (.forallE A B) (.sort u))
    (H : FullReduction Γ (.forallE A B) e') : ∃ A' B', e' = .forallE A' B' := by
  induction H with
  | rfl => exact ⟨_, _, rfl⟩
  | tail hr hs ih =>
    obtain ⟨A', B', rfl⟩ := ih
    exact fullStep_forallE_inv hΓ (FullReduction.hasType hΓ hr ht) hs

/-- A term normally equal to a `Π` is a `Π`. -/
theorem normalEqN_forallE_inv_r (hΓ : OnCtx Γ (Params.env.IsType univs))
    (ht : Params.env.HasType univs Γ (.forallE A B) (.sort u))
    (H : NormalEqN η n Γ e (.forallE A B)) : ∃ A' B', e = .forallE A' B' := by
  generalize he : VExpr.forallE A B = r at H
  cases H with
  | refl _ => exact ⟨_, _, he.symm⟩
  | forallEDF => exact ⟨_, _, rfl⟩
  | etaL ht' _ =>
    subst he
    exact False.elim (IsDefEqU.sort_forallE_inv henv hΓ (ht.uniqU henv hΓ ht'))
  | etaBoth _ ht' _ =>
    subst he
    exact False.elim (IsDefEqU.sort_forallE_inv henv hΓ (ht.uniqU henv hΓ ht'))
  | proofIrrel hp _ hb =>
    subst he
    have h1 := (ht.uniqU henv hΓ hb).of_r henv hΓ hp
    have h2 := (HasType.sort (ht.sort_r henv.ordered hΓ) :
      Params.env.HasType univs Γ (.sort u) (.sort (.succ u))).uniqU henv hΓ h1.hasType.1
    have h3 := congrFun (h2.sort_inv henv hΓ) []
    simp [VLevel.eval] at h3
  | _ => cases he

end Reduction

/-- A type convertible to a `Π` reduces to a `Π` (canonical `Eq`, through Church-Rosser). -/
theorem exposure_reduces {E : VEnv} (hE : E.WF) (hEq : E.HasCanonicalEq)
    (hΓ : OnCtx Γ (E.IsType U)) (hT : E.HasType U Γ T (.sort u))
    (H : E.IsDefEqU U Γ T (.forallE A B)) :
    letI := hE.params U
    ∃ A' B', FullReduction Γ T (.forallE A' B') := by
  letI := hE.params U
  have hd := H.of_l hE hΓ hT
  obtain ⟨x, y, hx, hy, hn⟩ := hE.church_rosser hEq hΓ hd
  have hPi : E.HasType U Γ (.forallE A B) (.sort u) := hd.hasType.2
  obtain ⟨A', B', rfl⟩ := fullReduction_forallE_inv hΓ hPi hy
  obtain ⟨n, hn⟩ := hn
  obtain ⟨A'', B'', rfl⟩ := normalEqN_forallE_inv_r hΓ (hy.hasType hΓ hPi) hn
  exact ⟨_, _, hx⟩

/-- Existential `Π`-exposure in reduction form: a type of `Γ`, inhabited in `Γ`, whose lift
reduces above to a `Π`, reduces below to some `Π`. -/
def PiExposureRedN {E : VEnv} (hE : E.WF) : Prop :=
  ∀ ⦃U k Γ Γ' f F u A B⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (E.IsType U) → OnCtx Γ' (E.IsType U) →
    E.HasType U Γ f F → E.HasType U Γ F (.sort u) →
    (letI := hE.params U; FullReduction Γ' (F.liftN 1 k) (.forallE A B)) →
    ∃ A₀ B₀, letI := hE.params U; FullReduction Γ F (.forallE A₀ B₀)

theorem PiExposureN.of_red {E : VEnv} (hE : E.WF) (hEq : E.HasCanonicalEq)
    (H : PiExposureRedN hE) : PiExposureN E := by
  intro U k Γ Γ' f F A B W hΓ hΓ' hf hF
  obtain ⟨u, hFs⟩ := hf.isType hE.ordered hΓ
  have hFs' : E.HasType U Γ' (F.liftN 1 k) (.sort u) := hFs.weakN hE.ordered W
  obtain ⟨A', B', hred⟩ := exposure_reduces hE hEq hΓ' hFs' hF
  obtain ⟨A₀, B₀, hred₀⟩ := H W hΓ hΓ' hf hFs hred
  letI := hE.params U
  exact ⟨A₀, B₀, _, hred₀.defeq hΓ hFs⟩

/-- Under canonical `Eq`, reduction-form exposure with the type front and the projection
closure gives the typing front, hence `Cancel`. -/
theorem cancel_of_piExposureRed {E : VEnv} (hE : E.WF) (hEq : E.HasCanonicalEq)
    (hRed : PiExposureRedN hE) (hTy : TypeFrontN E) (hProj : ProjFrontN E) : Cancel E :=
  (typingFrontN_iff_cancel hE hEq).mp (typingFrontN_of_closures hE
    (AppFrontN.of_piExposure hE (PiExposureN.of_red hE hEq hRed) hTy) hTy hProj)

end Lean4Lean.VEnv.Strengthening
