import Lean4Lean.Theory.Typing.Strengthening.NormalHeadBetaExposure
import Lean4Lean.Theory.Typing.Strengthening.EtaSpineHeadBeta

/-! # Head beta transport at sort-typed applications

Pending arguments allow eta comparisons to be consumed without reducing under
lambdas. The whole application must have a sort type. This restriction excludes
unapplied extensional comparisons; no normalization assumption is made.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A

private theorem beta_type (hΓ : OnCtx Γ (env.IsType univs)) (R : HeadBetaRed e e')
    (ht : Γ ⊢ e : T) : Γ ⊢ e' : T :=
  (R.toBeta.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ ht).hasType.2

omit [Params] in
private theorem beta_spine (A e a : VExpr) (bs : List VExpr) :
    HeadBetaRed (mkApps (.app (.lam A e) a) bs) (mkApps (e.inst a) bs) :=
  .tail .rfl (HeadBetaStep.mkApps .beta bs)

private theorem extend_normal (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ a b) (ht : Γ ⊢ mkApps a cs : T) :
    NormalEq Γ (mkApps a cs) (mkApps b cs) :=
  NormalEq.mkApps_spine hΓ H
    (NormalEqF.forall₂_refl (η := true) fun _ hx => mkApps_arg_type hΓ ht hx) ht

private theorem normal_sort_head_beta_aux (n : Nat) :
    (∀ {Γ A e a bs x cs u}, OnCtx Γ (env.IsType univs) →
      NormalEqN true n Γ x (mkApps (.app (.lam A e) a) bs) →
      Γ ⊢ mkApps x cs : .sort u →
      ∃ X, HeadBetaRed (mkApps x cs) X ∧ NormalEq Γ X (mkApps (e.inst a) (bs ++ cs))) ∧
    (∀ {Γ A e f c cs u}, OnCtx Γ (env.IsType univs) →
      NormalEqN true n Γ f (.lam A e) → Γ ⊢ mkApps (.app f c) cs : .sort u →
      ∃ X, HeadBetaRed (mkApps (.app f c) cs) X ∧ NormalEq Γ X (mkApps (e.inst c) cs)) := by
  induction n using Nat.strongRecOn with | _ n ih => ?_
  refine ⟨fun {Γ A e a bs x cs u} hΓ H hx => ?_, fun {Γ A e f c cs u} hΓ H hfc => ?_⟩
  · have hRt := hx.defeqU_l henv hΓ ((extend_normal hΓ ⟨_, H⟩ hx).defeq hΓ)
    rw [← mkApps_append] at hRt
    have hred := beta_spine A e a (bs ++ cs)
    have hrt := beta_type hΓ hred hRt
    generalize hR : mkApps (.app (.lam A e) a) bs = R at H
    have happ : ∃ f arg, mkApps (.app (.lam A e) a) bs = .app f arg := by
      rcases List.eq_nil_or_snoc bs with rfl | ⟨bs', b, rfl⟩
      · exact ⟨_, _, rfl⟩
      · exact ⟨_, _, mkApps_snoc ..⟩
    cases H with
    | refl _ =>
      subst hR
      exact ⟨_, by simpa only [mkApps_append] using hred, .refl hrt⟩
    | proofIrrel l1 l2 _ =>
      exact (HasType.sort_not_proof hΓ hx (HasType.mkApps_proof hΓ l1 l2 hx)).elim
    | sortDF | constDF | projDF | lamDF | forallEDF | etaR =>
      obtain ⟨_, _, happ⟩ := happ
      rw [happ] at hR; cases hR
    | appDF l1 l2 l3 l4 l5 l6 =>
      rcases List.eq_nil_or_snoc bs with rfl | ⟨bs', b, rfl⟩
      · cases hR
        obtain ⟨X, hX, hn⟩ := (ih _ (by omega)).2 hΓ l5 hx
        have ⟨⟨_, d1⟩, _, d2⟩ := l2.lam_inv henv hΓ
        have ⟨⟨_, u1⟩, _⟩ := ((d1.lam d2).uniqU henv hΓ l2).forallE_inv henv hΓ
        have hx2 := u1.symm.defeq l3
        have hm := (hn.defeq hΓ).of_l henv hΓ (beta_type hΓ hX hx) |>.hasType.2
        exact ⟨X, hX, hn.trans hΓ (extend_normal hΓ
          (.instN_r (by exact ⟨hΓ, _, d1⟩) hx2 ⟨_, l6⟩ .zero d2) hm)⟩
      · rw [mkApps_snoc] at hR; cases hR
        obtain ⟨X, hX, hn⟩ := (ih _ (by omega)).1 (cs := _ :: cs) hΓ l5 hx
        have hm := (hn.defeq hΓ).of_l henv hΓ (beta_type hΓ hX hx) |>.hasType.2
        rw [List.append_assoc, List.singleton_append]
        have Hargs := NormalEqF.forall₂_refl (η := true)
          (fun z hz => mkApps_arg_type hΓ hx hz)
        have hm' := hm
        rw [mkApps_append] at hm'
        have hfix := NormalEq.mkApps_spine hΓ
          (.refl (mkApps_head_type hΓ hm').choose_spec) (.cons ⟨_, l6⟩ Hargs) hm'
        exact ⟨X, hX, hn.trans hΓ (by simpa only [mkApps_append] using hfix)⟩
    | @etaL _ _ A0 _ _ g l1 l2 =>
      subst hR
      cases cs with
      | nil => exact (HasType.sort_not_lam hΓ hx).elim
      | cons c cs =>
        have hstep := beta_spine A0 g c cs
        obtain ⟨_, happ⟩ := mkApps_head_type hΓ (fn := .app (.lam A0 g) c) hx
        obtain ⟨_, _, hf, hc⟩ := happ.app_inv henv hΓ
        have ⟨⟨_, c1⟩, _, c2⟩ := hf.lam_inv henv hΓ
        have ⟨⟨_, u1⟩, _⟩ := ((c1.lam c2).uniqU henv hΓ hf).forallE_inv henv hΓ
        have hb := l2.instN (u1.symm.defeq hc) .zero
        rw [inst_lift_spine] at hb
        obtain ⟨X, hX, hn⟩ := (ih _ (by omega)).1 hΓ hb (beta_type hΓ hstep hx)
        exact ⟨X, hstep.trans hX, by simpa only [List.append_assoc, List.singleton_append] using hn⟩
    | etaBoth l1 l2 l3 =>
      subst hR
      cases cs with
      | nil => exact ((hx.uniqU henv hΓ l1).sort_forallE_inv henv hΓ).elim
      | cons c cs =>
        obtain ⟨_, happ⟩ := mkApps_head_type hΓ (fn := .app _ c) hx
        obtain ⟨_, _, hf, hc⟩ := happ.app_inv henv hΓ
        have ⟨⟨_, u1⟩, _⟩ := (hf.uniqU henv hΓ l1).forallE_inv henv hΓ
        have hb := l3.instN (u1.defeq hc) .zero
        simp only [VExpr.inst, inst_lift, instVar, Nat.lt_irrefl, if_false, if_true, liftN_zero] at hb
        rw [← mkApps_snoc] at hb
        obtain ⟨X, hX, hn⟩ := (ih _ (by omega)).1 hΓ hb hx
        exact ⟨X, hX, by simpa only [List.append_assoc, List.singleton_append] using hn⟩
  · obtain ⟨_, happ⟩ := mkApps_head_type hΓ hfc
    have ⟨_, _, hf, hc⟩ := happ.app_inv henv hΓ
    generalize hL : VExpr.lam A e = L at H
    cases H with
    | refl _ =>
      subst hL
      exact ⟨_, beta_spine _ _ _ _, .refl (beta_type hΓ (beta_spine _ _ _ _) hfc)⟩
    | sortDF | constDF | projDF | forallEDF | appDF => cases hL
    | lamDF a1 a2 a3 =>
      cases hL
      have ⟨⟨_, H3⟩, _, H4⟩ := hf.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _⟩ := ((H3.lam H4).uniqU henv hΓ hf).forallE_inv henv hΓ
      exact ⟨_, beta_spine _ _ _ _, extend_normal hΓ
        (.instN (.defeq (.symm <| .trans_l henv hΓ a1 u1) hc) .zero ⟨_, a3⟩)
        (beta_type hΓ (beta_spine _ _ _ _) hfc)⟩
    | etaL a1 a2 =>
      subst hL
      have ⟨⟨_, c1⟩, _, c2⟩ := hf.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _⟩ := ((c1.lam c2).uniqU henv hΓ hf).forallE_inv henv hΓ
      have hb := a2.instN (u1.symm.defeq hc) .zero
      simp [VExpr.inst, inst_lift] at hb
      obtain ⟨X, hX, hn⟩ := (ih _ (by omega)).1 (bs := []) hΓ hb
        (beta_type hΓ (beta_spine _ _ _ _) hfc)
      exact ⟨X, (beta_spine _ _ _ _).trans hX, hn⟩
    | etaR a1 a2 =>
      cases hL
      have ⟨⟨_, u1⟩, _⟩ := (hf.uniqU henv hΓ a1).forallE_inv henv hΓ
      have hb := a2.instN (.defeq u1 hc) .zero
      simp [VExpr.inst, inst_lift] at hb
      exact ⟨_, .rfl, extend_normal hΓ ⟨_, hb⟩ hfc⟩
    | etaBoth a1 a2 a3 =>
      subst hL
      have ⟨⟨_, u1⟩, _⟩ := (hf.uniqU henv hΓ a1).forallE_inv henv hΓ
      have hb := a3.instN (.defeq u1 hc) .zero
      simp [VExpr.inst, inst_lift] at hb
      exact (ih _ (by omega)).1 (bs := []) hΓ hb hfc
    | proofIrrel a1 a2 _ =>
      exact (HasType.sort_not_proof hΓ hfc
        (HasType.mkApps_proof hΓ a1 a2 (bs := c :: cs) hfc)).elim

/-- A head beta contraction in a sort-typed normal comparison can be mirrored
by head beta alone. The statement does not apply to arbitrary function types. -/
theorem normal_sort_beta_spine (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ x (mkApps (.app (.lam A e) a) bs)) (ht : Γ ⊢ x : .sort u) :
    ∃ X, HeadBetaRed x X ∧ NormalEq Γ X (mkApps (e.inst a) bs) := by
  obtain ⟨n, H⟩ := H
  simpa using (normal_sort_head_beta_aux n).1 (cs := []) hΓ H ht

omit [Params] in
/-- Every head contraction is a beta redex with a finite pending argument stack. -/
theorem HeadBetaStep.spine (R : HeadBetaStep x y) :
    ∃ A e a bs, x = VExpr.mkApps (.app (.lam A e) a) bs ∧ y = VExpr.mkApps (e.inst a) bs := by
  induction R with
  | beta => exact ⟨_, _, _, [], rfl, rfl⟩
  | @appL f f' a R ih =>
    obtain ⟨A, e, c, bs, rfl, rfl⟩ := ih
    exact ⟨A, e, c, bs ++ [a], (mkApps_snoc ..).symm, (mkApps_snoc ..).symm⟩

/-- Transport one head beta step through a normal comparison of sort-typed terms. -/
theorem normal_sort_head_beta_step (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ x y) (ht : Γ ⊢ x : .sort u) (R : HeadBetaStep y z) :
    ∃ X, HeadBetaRed x X ∧ NormalEq Γ X z := by
  obtain ⟨A, e, a, bs, rfl, rfl⟩ := R.spine
  exact normal_sort_beta_spine hΓ H ht

/-- Finite head beta transport through ordinary normal equality at a sort.
Only the head spine computes on the left, even in extensional comparisons. -/
theorem normal_sort_head_beta_simulation (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ x y) (ht : Γ ⊢ x : .sort u) (R : HeadBetaRed y z) :
    ∃ X, HeadBetaRed x X ∧ NormalEq Γ X z := by
  induction R with
  | rfl => exact ⟨x, .rfl, H⟩
  | tail _ R ih =>
    obtain ⟨x', R', H'⟩ := ih
    obtain ⟨x'', R'', H''⟩ := normal_sort_head_beta_step hΓ H' (beta_type hΓ R' ht) R
    exact ⟨x'', R'.trans R'', H''⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
