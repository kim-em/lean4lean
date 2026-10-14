import Lean4Lean.Theory.Typing.Strengthening.NormalBetaReflection
import Lean4Lean.Theory.Typing.FullReduction

/-! # Spine exposure without adding eta reductions

An extensional comparison is retained as a strictly smaller comparison at a fresh
argument, instead of expanding its source to a lambda. This alternative is meant
to be consumed by applying an actual argument in a subsequent transport proof.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A

private theorem beta_type (hΓ : OnCtx Γ (env.IsType univs)) (R : BetaRed e e')
    (ht : Γ ⊢ e : T) : Γ ⊢ e' : T :=
  (R.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ ht).hasType.2

omit [Params] in
private theorem beta_spine (A e a : VExpr) (bs : List VExpr) :
    BetaRed (mkApps (.app (.lam A e) a) bs) (mkApps (e.inst a) bs) :=
  .mkApps .beta (BetaRed.forall₂_refl bs)

omit [Params] in
private theorem mkApps_ne_proj {fn : VExpr}
    (hf : ∀ n i e, fn ≠ .proj n i e) (args : List VExpr) :
    mkApps fn args ≠ .proj family index major := by
  induction args generalizing fn with
  | nil => exact hf _ _ _
  | cons _ _ ih => exact ih (fn := .app _ _) nofun

/-- Spine exposure by beta alone. The fourth alternative records an unexpanded
function and a strictly smaller extensional comparison. It is not a head-exposure
result by itself and makes no claim of strengthening or prefix coverage. -/
theorem normal_spine_expose_beta (hΓ : OnCtx Γ (env.IsType univs)) (hh : RigidHead h) :
    ∀ n {x targs bs bs' T}, NormalEqN true n Γ x (VExpr.mkApps h targs) →
      List.Forall₂ (NormalEq Γ) bs bs' → Γ ⊢ VExpr.mkApps x bs : T →
      (Γ ⊢ T : .sort .zero) ∨
      (∃ h' targs', HeadEquiv h' h ∧ BetaRed (VExpr.mkApps x bs) (VExpr.mkApps h' targs') ∧
        List.Forall₂ (NormalEq Γ) targs' (targs ++ bs')) ∨
      (∃ A g m targs₁ B, m < n ∧ BetaRed (VExpr.mkApps x bs) (.lam A g) ∧
        NormalEqN true m (A :: Γ) g (.app (VExpr.mkApps h targs₁).lift (.bvar 0)) ∧
        List.Forall₂ (NormalEq Γ) targs₁ (targs ++ bs') ∧
        Γ ⊢ VExpr.mkApps h targs₁ : .forallE A B) ∨
      (∃ z A B m targs₁, m < n ∧ BetaRed (VExpr.mkApps x bs) z ∧
        Γ ⊢ z : .forallE A B ∧
        NormalEqN true m (A :: Γ) (.app z.lift (.bvar 0))
          (.app (VExpr.mkApps h targs₁).lift (.bvar 0)) ∧
        List.Forall₂ (NormalEq Γ) targs₁ (targs ++ bs') ∧
        Γ ⊢ VExpr.mkApps h targs₁ : .forallE A B) := by
  intro n
  induction n using Nat.strongRecOn with | _ n ih => ?_
  intro x targs bs bs' T H hbs ht
  have hbs' := NormalEq.forall₂_typed_right hΓ hbs
  have htargsTyped : ∀ a ∈ targs, ∃ A, Γ ⊢ a : A := by
    obtain ⟨_, hd⟩ := H.defeq hΓ
    exact fun a ha => mkApps_arg_type hΓ hd.hasType.2 ha
  have hrefl := NormalEqF.forall₂_refl (η := true) htargsTyped
  generalize hR : VExpr.mkApps h targs = R at H
  cases H with
  | refl _ =>
    subst hR
    refine .inr (.inl ⟨h, targs ++ bs, hh.equiv_rfl, ?_, List.Forall₂.append' hrefl hbs⟩)
    rw [VExpr.mkApps_append]; exact .refl
  | proofIrrel l1 l2 _ => exact .inl (HasType.mkApps_proof hΓ l1 l2 ht)
  | constDF _ _ _ _ l5 =>
    cases hh with
    | const =>
      rcases List.eq_nil_or_snoc targs with rfl | ⟨_, _, rfl⟩
      · cases hR
        exact .inr (.inl ⟨_, bs, .const l5, .refl, hbs⟩)
      · rw [VExpr.mkApps_snoc] at hR; cases hR
  | appDF l1 l2 l3 l4 l5 l6 =>
    obtain ⟨targs₀, rfl, rfl⟩ := hh.mkApps_eq_app hR
    rcases ih _ (by omega) l5 (.cons ⟨_, l6⟩ hbs) ht with hp | ⟨h', targs', he, hr, hn⟩ |
        ⟨A, g, m, targs₁, B, hm, hr, hg, hn, hty⟩ |
        ⟨z, A, B, m, targs₁, hm, hr, hz, hg, hn, hty⟩
    · exact .inl hp
    · exact .inr (.inl ⟨h', targs', he, hr, by simpa using hn⟩)
    · exact .inr (.inr (.inl ⟨A, g, m, targs₁, B, by omega, hr, hg, by simpa using hn, hty⟩))
    · exact .inr (.inr (.inr ⟨z, A, B, m, targs₁, by omega, hr, hz, hg, by simpa using hn, hty⟩))
  | @etaL _ _ A0 _ _ g l1 l2 =>
    subst hR
    cases hbs with
    | nil => exact .inr (.inr (.inl ⟨_, _, _, targs, _, by omega, .refl, l2,
        by simpa using hrefl, l1⟩))
    | @cons b b' bs₀ bs₀' hb hbs₀ =>
      have hstep := beta_spine A0 g b bs₀
      have ht' := beta_type hΓ hstep ht
      obtain ⟨_, happ⟩ := mkApps_head_type hΓ (fn := .app (.lam A0 g) b) ht
      obtain ⟨_, _, hf, hbt⟩ := happ.app_inv henv hΓ
      have ⟨⟨_, c1⟩, _, c2⟩ := hf.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _⟩ := ((c1.lam c2).uniqU henv hΓ hf).forallE_inv henv hΓ
      have hb' := l2.instN (u1.symm.defeq hbt) .zero
      rw [inst_lift_spine] at hb'
      have hbs₁ : List.Forall₂ (NormalEq Γ) bs₀' bs₀' :=
        NormalEqF.forall₂_refl (η := true) fun a ha => hbs' a (List.mem_cons_of_mem _ ha)
      have hfix : List.Forall₂ (NormalEq Γ) ((targs ++ [b]) ++ bs₀') (targs ++ b' :: bs₀') := by
        rw [List.append_assoc, List.singleton_append]
        exact List.Forall₂.append' hrefl (.cons hb hbs₁)
      rcases ih _ (by omega) hb' hbs₀ ht' with hp | ⟨h', targs', he, hr, hn⟩ |
          ⟨A, g, m, targs₁, B, hm, hr, hg, hn, hty⟩ |
        ⟨z, A, B, m, targs₁, hm, hr, hz, hg, hn, hty⟩
      · exact .inl hp
      · exact .inr (.inl ⟨h', targs', he, hstep.trans hr, NormalEq.forall₂_trans hΓ hn hfix⟩)
      · exact .inr (.inr (.inl ⟨A, g, m, targs₁, B, by omega, hstep.trans hr, hg,
          NormalEq.forall₂_trans hΓ hn hfix, hty⟩))
      · exact .inr (.inr (.inr ⟨z, A, B, m, targs₁, by omega, hstep.trans hr, hz, hg,
          NormalEq.forall₂_trans hΓ hn hfix, hty⟩))
  | etaBoth l1 l2 l3 =>
    subst hR
    cases hbs with
    | nil => exact .inr (.inr (.inr ⟨_, _, _, _, targs, by omega, .refl, l1, l3,
        by simpa using hrefl, l2⟩))
    | @cons b b' bs₀ bs₀' hb hbs₀ =>
      obtain ⟨_, happ⟩ := mkApps_head_type hΓ (fn := .app _ b) ht
      obtain ⟨_, _, hf, hbt⟩ := happ.app_inv henv hΓ
      have ⟨⟨_, u1⟩, _⟩ := (hf.uniqU henv hΓ l1).forallE_inv henv hΓ
      have hb' := l3.instN (u1.defeq hbt) .zero
      simp only [VExpr.inst, VExpr.inst_lift] at hb'
      simp only [VExpr.instVar, Nat.lt_irrefl, if_false, VExpr.liftN_zero] at hb'
      rw [← VExpr.mkApps_snoc] at hb'
      have hbs₁ : List.Forall₂ (NormalEq Γ) bs₀' bs₀' :=
        NormalEqF.forall₂_refl (η := true) fun a ha => hbs' a (List.mem_cons_of_mem _ ha)
      have hfix : List.Forall₂ (NormalEq Γ) ((targs ++ [b]) ++ bs₀') (targs ++ b' :: bs₀') := by
        rw [List.append_assoc, List.singleton_append]
        exact List.Forall₂.append' hrefl (.cons hb hbs₁)
      rcases ih _ (by omega) hb' hbs₀ ht with hp | ⟨h', targs', he, hr, hn⟩ |
          ⟨A, g, m, targs₁, B, hm, hr, hg, hn, hty⟩ |
        ⟨z, A, B, m, targs₁, hm, hr, hz, hg, hn, hty⟩
      · exact .inl hp
      · exact .inr (.inl ⟨h', targs', he, hr, NormalEq.forall₂_trans hΓ hn hfix⟩)
      · exact .inr (.inr (.inl ⟨A, g, m, targs₁, B, by omega, hr, hg,
          NormalEq.forall₂_trans hΓ hn hfix, hty⟩))
      · exact .inr (.inr (.inr ⟨z, A, B, m, targs₁, by omega, hr, hz, hg,
          NormalEq.forall₂_trans hΓ hn hfix, hty⟩))
  | sortDF => exact absurd hR (VExpr.mkApps_ne_sort (by cases hh <;> nofun) _)
  | lamDF => exact absurd hR (VExpr.mkApps_ne_lam (by cases hh <;> nofun) _)
  | etaR => exact absurd hR (VExpr.mkApps_ne_lam (by cases hh <;> nofun) _)
  | forallEDF => exact absurd hR (VExpr.mkApps_ne_forallE (by cases hh <;> nofun) _)
  | projDF => exact absurd hR (mkApps_ne_proj (by cases hh <;> nofun) _)

end Lean4Lean.VEnv.Strengthening
