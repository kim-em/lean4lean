import Lean4Lean.Theory.Typing.Strengthening.FreshBetaReflection

/-! # Beta simulation without eta expansion

Ordinary normal comparison can transport a contracted beta redex using beta
reduction alone. Fresh-argument reflection removes the eta expansion otherwise
used by the extensionality case. Opaque domain equalities remain in NormalEq;
this result does not supply recursive domain certificates or strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A

private theorem beta_type (hΓ : OnCtx Γ (env.IsType univs))
    (R : BetaRed e e') (ht : Γ ⊢ e : T) : Γ ⊢ e' : T :=
  (R.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ ht).hasType.2

omit [Params] in
private theorem mkApps_app_isApp (g c : VExpr) (bs : List VExpr) :
    ∃ f a, VExpr.mkApps (.app g c) bs = .app f a := by
  rcases List.eq_nil_or_snoc bs with rfl | ⟨bs', b, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, VExpr.mkApps_snoc ..⟩

omit [Params] in
private theorem lift_beta_spine (A e a : VExpr) (bs : List VExpr) :
    VExpr.app (VExpr.mkApps (.app (.lam A e) a) bs).lift (.bvar 0) =
      VExpr.mkApps (.app (.lam A.lift (e.liftN 1 1)) a.lift)
        (bs.map VExpr.lift ++ [.bvar 0]) := by
  rw [VExpr.mkApps_snoc]; simp [VExpr.liftN]

omit [Params] in
private theorem lift_beta_spine_result (e a : VExpr) (bs : List VExpr) :
    VExpr.mkApps ((e.liftN 1 1).inst a.lift) (bs.map VExpr.lift ++ [.bvar 0]) =
      VExpr.app (VExpr.mkApps (e.inst a) bs).lift (.bvar 0) := by
  rw [VExpr.mkApps_snoc, ← lift_inst_hi]; simp

omit [Params] in
private theorem beta_spine (A e a : VExpr) (bs : List VExpr) :
    BetaRed (VExpr.mkApps (.app (.lam A e) a) bs) (VExpr.mkApps (e.inst a) bs) := by
  refine BetaRed.mkApps .beta ?_
  induction bs with
  | nil => exact .nil
  | cons _ _ ih => exact .cons .refl ih

private theorem normal_beta_aux (n : Nat) :
    (∀ {Γ A e a bs x T}, OnCtx Γ (env.IsType univs) →
      NormalEqN true n Γ x (VExpr.mkApps (.app (.lam A e) a) bs) → Γ ⊢ x : T →
      ∃ X, BetaRed x X ∧ NormalEq Γ X (VExpr.mkApps (e.inst a) bs)) ∧
    (∀ {Γ A e f c T}, OnCtx Γ (env.IsType univs) →
      NormalEqN true n Γ f (.lam A e) → Γ ⊢ .app f c : T →
      ∃ X, BetaRed (.app f c) X ∧ NormalEq Γ X (e.inst c)) := by
  induction n using Nat.strongRecOn with | _ n ih => ?_
  refine ⟨fun {Γ A e a bs x T} hΓ H hx => ?_, fun {Γ A e f c T} hΓ H hfc => ?_⟩
  · have hRt := hx.defeqU_l henv hΓ (H.defeq hΓ)
    have hred := beta_spine A e a bs
    have hrt := beta_type hΓ hred hRt
    generalize hR : VExpr.mkApps (.app (.lam A e) a) bs = R at H hRt hred
    have ⟨_, _, happ⟩ := mkApps_app_isApp (.lam A e) a bs
    cases H with
    | refl _ => exact ⟨_, hred, .refl hrt⟩
    | proofIrrel l1 l2 l3 => exact ⟨_, .refl, .proofIrrel l1 l2 (beta_type hΓ hred l3)⟩
    | sortDF | constDF | projDF | lamDF | forallEDF | etaR =>
      rw [happ] at hR; cases hR
    | appDF l1 l2 l3 l4 l5 l6 =>
      rcases List.eq_nil_or_snoc bs with rfl | ⟨bs', b, rfl⟩
      · cases hR
        obtain ⟨X, hX, hn⟩ := ((ih _ (by omega)).2 hΓ l5 hx)
        have ⟨⟨_, d1⟩, _, d2⟩ := l2.lam_inv henv hΓ
        have ⟨⟨_, u1⟩, _⟩ := ((d1.lam d2).uniqU henv hΓ l2).forallE_inv henv hΓ
        have hx2 := u1.symm.defeq l3
        exact ⟨X, hX, hn.trans hΓ (.instN_r (by exact ⟨hΓ, _, d1⟩) hx2 ⟨_, l6⟩ .zero d2)⟩
      · rw [VExpr.mkApps_snoc] at hR; cases hR
        obtain ⟨X, hX, hn⟩ := ((ih _ (by omega)).1 hΓ l5 l1)
        have hX' := beta_type hΓ hX l1
        rw [VExpr.mkApps_snoc]
        exact ⟨_, hX.app .refl, .appDF hX' ((hn.defeq hΓ).of_l henv hΓ hX').hasType.2 l3 l4
          hn ⟨_, l6⟩⟩
    | etaL l1 l2 =>
      subst hR
      have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
      have hΓ' : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
      have ⟨_, _, hg⟩ := hx.lam_inv henv hΓ
      rw [lift_beta_spine] at l2
      obtain ⟨Y, hY, hn⟩ := (ih _ (by omega)).1 hΓ' l2 hg
      rw [lift_beta_spine_result] at hn
      exact ⟨_, .lam .refl hY, .etaL (beta_type hΓ hred l1) hn⟩
    | etaBoth l1 l2 l3 =>
      subst hR
      have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
      have hΓ' : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
      rw [lift_beta_spine] at l3
      obtain ⟨Y, hY, hn⟩ := (ih _ (by omega)).1 hΓ' l3 ((l1.weakN henv .one).app (.bvar .zero))
      rw [lift_beta_spine_result] at hn
      obtain ⟨Z, RZ, HZ⟩ := beta_eta_body_reflection hΓ l1 hY
      exact ⟨Z, RZ, HZ.trans hΓ (.etaL (beta_type hΓ hred l2) hn)⟩
  · have ⟨_, _, hf, hc⟩ := hfc.app_inv henv hΓ
    have hbeta {A₁ g} : BetaRed (.app (.lam A₁ g) c) (g.inst c) := .beta
    generalize hL : VExpr.lam A e = L at H
    cases H with
    | refl _ =>
      subst hL
      exact ⟨_, hbeta, .refl (beta_type hΓ hbeta hfc)⟩
    | sortDF | constDF | projDF | forallEDF | appDF => cases hL
    | lamDF a1 a2 a3 =>
      cases hL
      have ⟨⟨_, H3⟩, _, H4⟩ := hf.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _⟩ := ((H3.lam H4).uniqU henv hΓ hf).forallE_inv henv hΓ
      exact ⟨_, hbeta,
        .instN (.defeq (.symm <| .trans_l henv hΓ a1 u1) hc) .zero ⟨_, a3⟩⟩
    | etaL a1 a2 =>
      subst hL
      have ⟨⟨_, c1⟩, _, c2⟩ := hf.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _⟩ := ((c1.lam c2).uniqU henv hΓ hf).forallE_inv henv hΓ
      have := a2.instN (u1.symm.defeq hc) .zero
      simp [VExpr.inst, inst_lift] at this
      obtain ⟨X, hX, hn⟩ := (ih _ (by omega)).1 (bs := []) hΓ this (beta_type hΓ hbeta hfc)
      exact ⟨X, hbeta.trans hX, hn⟩
    | etaR a1 a2 =>
      cases hL
      have ⟨⟨_, u1⟩, _⟩ := (hf.uniqU henv hΓ a1).forallE_inv henv hΓ
      have := a2.instN (.defeq u1 hc) .zero
      simp [VExpr.inst, inst_lift] at this
      exact ⟨_, .refl, ⟨_, this⟩⟩
    | etaBoth a1 a2 a3 =>
      subst hL
      have ⟨⟨_, u1⟩, _⟩ := (hf.uniqU henv hΓ a1).forallE_inv henv hΓ
      have := a3.instN (.defeq u1 hc) .zero
      simp [VExpr.inst, inst_lift] at this
      exact (ih _ (by omega)).1 (bs := []) hΓ this hfc
    | proofIrrel a1 a2 a3 =>
      subst hL
      have hf' := a2.uniqU henv hΓ hf; have := a1.defeqU_l henv hΓ hf'
      have ⟨⟨_, b1⟩, _, b2⟩ := this.forallE_inv henv
      have := ((b1.forallE b2).uniqU henv hΓ this).sort_inv henv hΓ
      have b3 := let ⟨_, h⟩ := b2.isType henv (by exact ⟨hΓ, _, b1⟩); h.sort_inv henv
      have b2 := IsDefEq.defeq (.sortDF b3 (by trivial) (VLevel.imax_eq_zero.1 this)) b2
      have ⟨⟨_, c1⟩, _, c2⟩ := a3.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _, u2⟩ := ((c1.lam c2).uniqU henv hΓ a3).trans henv hΓ hf' |>.forallE_inv henv hΓ
      exact ⟨_, .refl, .proofIrrel (b2.instN henv .zero hc) (hf.app hc)
        ((u2.defeq c2).instN henv .zero (u1.symm.defeq hc))⟩

/-- A function normally equal to a lambda computes, when applied, to the
instantiated lambda body up to normal equality. -/
theorem normal_lam_beta (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ f (.lam A e)) (ht : Γ ⊢ .app f c : T) :
    ∃ X, BetaRed (.app f c) X ∧ NormalEq Γ X (e.inst c) :=
  let ⟨n, H⟩ := H; (normal_beta_aux n).2 hΓ H ht

/-- Contracting the head beta redex of an arbitrary application spine can be
mirrored through ordinary normal equality by beta alone, including etaBoth
comparisons. This is a root-spine theorem, not yet general compatible simulation. -/
theorem normal_beta_spine (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ x (mkApps (.app (.lam A e) a) bs)) (ht : Γ ⊢ x : T) :
    ∃ X, BetaRed x X ∧ NormalEq Γ X (mkApps (e.inst a) bs) :=
  let ⟨n, H⟩ := H; (normal_beta_aux n).1 hΓ H ht

end Lean4Lean.VEnv.Strengthening
