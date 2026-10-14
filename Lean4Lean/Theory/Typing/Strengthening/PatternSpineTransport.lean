import Lean4Lean.Theory.Typing.Strengthening.FreshPatternReflection
import Lean4Lean.Theory.Typing.Strengthening.NormalSpineExposure

/-! # Transport at applied heads without eta reduction

A root rule that transports normally compared argument spines extends to every
normal comparison around its redex. Fresh-argument reflection and a smaller
extensional spine alternative eliminate the eta steps in this transport proof.
The root firing hypothesis remains explicit; this is not yet pattern completeness.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A

theorem PatternCompute.of_beta (R : BetaRed a b) : PatternCompute D a b :=
  .base (.base (.of_beta R))

theorem PatternCompute.mkApps (R : PatternCompute D f f')
    (HA : List.Forall₂ (PatternCompute D) args args') :
    PatternCompute D (mkApps f args) (mkApps f' args') := by
  induction HA generalizing f f' with
  | nil => exact R
  | cons H _ ih => exact ih (.app R H)

private theorem pattern_type (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (R : PatternCompute D a b) (ht : Γ ⊢ a : T) : Γ ⊢ b : T :=
  (R.simAt hs hΓ _ ht).hasType.2

private theorem pattern_forall₂_refl (args : List VExpr) :
    List.Forall₂ (PatternCompute D) args args := by
  induction args with
  | nil => exact .nil
  | cons _ _ ih => exact .cons .refl ih

omit [Params] in
private theorem lift_redex_spine (h : VExpr) (vs : List VExpr) (M : VExpr) (bs : List VExpr) :
    VExpr.app (VExpr.mkApps (.app (VExpr.mkApps h vs) M) bs).lift (.bvar 0) =
      VExpr.mkApps (.app (VExpr.mkApps h.lift (vs.map VExpr.lift)) M.lift)
        (bs.map VExpr.lift ++ [.bvar 0]) := by
  rw [VExpr.mkApps_snoc]; congr 1
  show VExpr.liftN 1 (VExpr.mkApps _ _) 0 = _
  rw [VExpr.liftN_mkApps]; congr 1
  show VExpr.app (VExpr.liftN 1 (VExpr.mkApps _ _) 0) _ = _
  rw [VExpr.liftN_mkApps]

omit [Params] in
private theorem forall₂_map_lift_lift' (vs : List VExpr) :
    (vs.map (·.lift' ρ)).map VExpr.lift = vs.map (·.lift' (.skip ρ)) := by
  simp [List.map_map, Function.comp_def, lift_lift'_skip]

omit [Params] in
private theorem mkApps_app_isApp (g c : VExpr) (bs : List VExpr) :
    ∃ f a, VExpr.mkApps (.app g c) bs = .app f a := by
  rcases List.eq_nil_or_snoc bs with rfl | ⟨bs', b, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, VExpr.mkApps_snoc ..⟩

/-- Transport of a specified redex below renamings and extra arguments using
pattern computation alone. General root-rule coverage remains to be established. -/
def PatternSpineTransport (D : Definitions) (Γ : List VExpr) (e e' : VExpr) (n : Nat) : Prop :=
  ∀ {ρ Γ' bs x}, OnCtx Γ' (env.IsType univs) → Ctx.Lift' ρ Γ Γ' →
    NormalEqN true n Γ' x (VExpr.mkApps (e.lift' ρ) bs) →
    ∃ X, PatternCompute D x X ∧ NormalEq Γ' X (VExpr.mkApps (e'.lift' ρ) bs)

/-- A root firing theorem for normally compared major and argument spines lifts
to arbitrary normal comparisons, without using function or structure eta steps.
This leaves the concrete root firing theorem as an explicit premise. -/
theorem pattern_redex_transport (hs : D.Sound env univs) {hd : List VLevel → VExpr} (hhd : ∀ ls, RigidHead (hd ls))
    (hlift : ∀ ls ρ, (hd ls).lift' ρ = hd ls)
    (hinv : ∀ {h' ls}, HeadEquiv h' (hd ls) → ∃ ls', h' = hd ls' ∧ List.Forall₂ (· ≈ ·) ls' ls)
    {ls₀ : List VLevel} {vs : List VExpr} {M tgt : VExpr}
    (fire : ∀ {ρ Γ' ls₁ vs₁ M₁ T Tℓ}, OnCtx Γ' (env.IsType univs) → Ctx.Lift' ρ Γ Γ' →
      List.Forall₂ (· ≈ ·) ls₁ ls₀ → List.Forall₂ (NormalEq Γ') vs₁ (vs.map (·.lift' ρ)) →
      NormalEq Γ' M₁ (M.lift' ρ) →
      Γ' ⊢ (VExpr.app (VExpr.mkApps (hd ls₀) vs) M).lift' ρ : Tℓ →
      Γ' ⊢ .app (VExpr.mkApps (hd ls₁) vs₁) M₁ : T →
      ∃ X, PatternCompute D (.app (VExpr.mkApps (hd ls₁) vs₁) M₁) X ∧
        NormalEq Γ' X (tgt.lift' ρ)) :
    ∀ n, PatternSpineTransport D Γ (.app (VExpr.mkApps (hd ls₀) vs) M) tgt n := by
  have main : ∀ n {ρ Γ' bs x ls₁ vs₁ M₁ Tℓ}, OnCtx Γ' (env.IsType univs) → Ctx.Lift' ρ Γ Γ' →
      List.Forall₂ (· ≈ ·) ls₁ ls₀ → List.Forall₂ (NormalEq Γ') vs₁ (vs.map (·.lift' ρ)) →
      NormalEq Γ' M₁ (M.lift' ρ) →
      Γ' ⊢ (VExpr.app (VExpr.mkApps (hd ls₀) vs)
        M).lift' ρ : Tℓ →
      NormalEqN true n Γ' x (VExpr.mkApps (.app (VExpr.mkApps (hd ls₁) vs₁) M₁) bs) →
      ∃ X, PatternCompute D x X ∧
        NormalEq Γ' X (VExpr.mkApps (tgt.lift' ρ) bs) := by
    intro n
    induction n using Nat.strongRecOn with | _ n ihn => ?_
    intro ρ Γ' bs x ls₁ vs₁ M₁ Tℓ hΓ W hls hvs hMr hEt H
    have hl : (hd ls₁).lift = hd ls₁ := by rw [VExpr.lift_eq_lift']; exact hlift _ _
    have ⟨_, hxd⟩ := H.defeq hΓ
    have hRt := hxd.hasType.2
    obtain ⟨_, hR₀t⟩ := mkApps_head_type hΓ hRt
    obtain ⟨X₀, hX₀r, hX₀n⟩ := fire hΓ W hls hvs hMr hEt hR₀t
    have hbsT : ∀ a ∈ bs, ∃ A, Γ' ⊢ a : A := fun a ha => mkApps_arg_type hΓ hRt ha
    have hspR := PatternCompute.mkApps hX₀r (pattern_forall₂_refl bs)
    have hspT := pattern_type hs hΓ hspR hRt
    have hspN := NormalEq.mkApps_spine hΓ hX₀n (NormalEqF.forall₂_refl (η := true) hbsT) hspT
    have htyT : ∀ {P}, Γ' ⊢ VExpr.mkApps (.app (VExpr.mkApps (hd ls₁) vs₁) M₁) bs : P →
        Γ' ⊢ VExpr.mkApps (tgt.lift' ρ) bs : P := fun h =>
      (pattern_type hs hΓ hspR h).defeqU_l henv hΓ (hspN.defeq hΓ)
    have lifted {A u} (hA : Γ' ⊢ A : .sort u) :
        OnCtx (A :: Γ') (env.IsType univs) ∧
        List.Forall₂ (NormalEq (A :: Γ')) (vs₁.map VExpr.lift) (vs.map (·.lift' (.skip ρ))) ∧
        NormalEq (A :: Γ') M₁.lift (M.lift' (.skip ρ)) ∧
        (A :: Γ') ⊢ (VExpr.app (VExpr.mkApps (hd ls₀) vs)
          M).lift' (.skip ρ) : Tℓ.lift := by
      refine ⟨⟨hΓ, _, hA⟩, ?_, ?_, ?_⟩
      · have := NormalEq.forall₂_weak (A := A) hvs
        rwa [forall₂_map_lift_lift'] at this
      · rw [← lift_lift'_skip]; exact hMr.weakN .one
      · rw [← lift_lift'_skip]; exact hEt.weakN henv .one
    generalize hRR : VExpr.mkApps (.app (VExpr.mkApps (hd ls₁) vs₁) M₁) bs = R at H
    cases H with
    | refl _ => subst hRR; exact ⟨_, hspR, hspN⟩
    | proofIrrel l1 l2 l3 => subst hRR; exact ⟨_, .refl, .proofIrrel l1 l2 (htyT l3)⟩
    | etaL l1 l2 =>
      subst hRR
      have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
      obtain ⟨hΓ', hvs', hMr', hEt'⟩ := lifted hA
      rw [lift_redex_spine, hl] at l2
      obtain ⟨Y, hY, hn⟩ := ihn _ (by omega) hΓ' W.skip hls hvs' hMr' hEt' l2
      rw [← lift_mkApps_lift'] at hn
      exact ⟨_, .lam .refl hY, .etaL (htyT l1) hn⟩
    | etaBoth l1 l2 l3 =>
      subst hRR
      have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
      obtain ⟨hΓ', hvs', hMr', hEt'⟩ := lifted hA
      rw [lift_redex_spine, hl] at l3
      obtain ⟨Y, hY, hn⟩ := ihn _ (by omega) hΓ' W.skip hls hvs' hMr' hEt' l3
      rw [← lift_mkApps_lift'] at hn
      obtain ⟨Z, RZ, HZ⟩ := hY.eta_body_reflection hs hΓ l1
      exact ⟨Z, RZ, HZ.trans hΓ (.etaL (htyT l2) hn)⟩
    | @appDF _ x1 _ _ _ x2 _ _ _ _ l1 l2 l3 l4 l5 l6 =>
      rcases List.eq_nil_or_snoc bs with rfl | ⟨bs₀, b, rfl⟩
      · cases hRR
        have hxT := hxd.hasType.1
        have hx2M : NormalEq Γ' _ _ := NormalEq.trans hΓ ⟨_, l6⟩ hMr
        rcases normal_spine_expose_beta hΓ (hhd _) _ l5 (bs := []) .nil l1 with
          hprop | ⟨h', vs₂, he, hred, hvs₂⟩ | ⟨A', g, m, targs₁, B', hm, hred, hg, hrel, _⟩ |
            ⟨z, A', B', m, targs₁, hm, hred, hz, hg, hrel, _⟩
        · have hP := HasType.mkApps_proof hΓ hprop l1 (bs := [_]) hxT
          exact ⟨_, .refl, .proofIrrel hP hxT (htyT hRt)⟩
        · obtain ⟨ls₂, rfl, hls₂⟩ := hinv he
          simp only [List.append_nil] at hvs₂
          have hred' : PatternCompute D (.app x1 x2) _ := PatternCompute.app (.of_beta hred) .refl
          have hR₂t := pattern_type hs hΓ hred' hxT
          obtain ⟨X, hX, hn⟩ := fire hΓ W
            (Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans h') hls₂ hls)
            (NormalEq.forall₂_trans hΓ hvs₂ hvs) hx2M hEt hR₂t
          exact ⟨_, hred'.trans hX, by simpa only [VExpr.mkApps, List.foldl] using hn⟩
        · have hred' : PatternCompute D (.app x1 x2) (.app (.lam A' g) x2) :=
            PatternCompute.app (.of_beta hred) .refl
          have happT := pattern_type hs hΓ hred' hxT
          have hx2A := HasType.app_lam_arg hΓ happT
          have hstepβ : PatternCompute D (.app (.lam A' g) x2) (g.inst x2) := .of_beta .beta
          have hg' := hg.instN hx2A .zero
          rw [inst_lift_spine, VExpr.mkApps_snoc] at hg'
          simp only [List.append_nil] at hrel
          obtain ⟨Y, hY, hn⟩ := ihn _ (by omega) hΓ W hls (NormalEq.forall₂_trans hΓ hrel hvs)
            hx2M hEt (bs := []) hg'
          exact ⟨_, (hred'.trans hstepβ).trans hY, hn⟩
        · have hred' : PatternCompute D (.app x1 x2) (.app z x2) := .app (.of_beta hred) .refl
          have happT := pattern_type hs hΓ hred' hxT
          obtain ⟨_, _, hz', ha⟩ := happT.app_inv henv hΓ
          obtain ⟨⟨_, hAA⟩, _⟩ := (hz'.uniqU henv hΓ hz).forallE_inv henv hΓ
          have hg' := hg.instN (hAA.defeq ha) .zero
          simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar, Nat.lt_irrefl,
            if_false, VExpr.liftN_zero] at hg'
          simp only [List.append_nil] at hrel
          obtain ⟨Y, hY, hn⟩ := ihn _ (by omega) hΓ W hls
            (NormalEq.forall₂_trans hΓ hrel hvs) hx2M hEt (bs := []) hg'
          exact ⟨Y, hred'.trans hY, hn⟩
      · rw [VExpr.mkApps_snoc] at hRR; cases hRR
        obtain ⟨X, hX, hn⟩ := ihn _ (by omega) hΓ W hls hvs hMr hEt l5
        have hX' := pattern_type hs hΓ hX l1
        rw [VExpr.mkApps_snoc]
        exact ⟨_, hX.app .refl, .appDF hX' ((hn.defeq hΓ).of_l henv hΓ hX').hasType.2 l3 l4
          hn ⟨_, l6⟩⟩
    | sortDF | constDF | projDF | lamDF | forallEDF | etaR =>
      obtain ⟨_, _, happ⟩ := mkApps_app_isApp (VExpr.mkApps (hd ls₁) vs₁) M₁ bs
      rw [happ] at hRR; cases hRR
  intro n ρ Γ' bs x hΓ W H
  have ⟨_, hxd⟩ := H.defeq hΓ
  obtain ⟨_, hEt⟩ := mkApps_head_type hΓ hxd.hasType.2
  have hEt' := hEt
  simp only [VExpr.lift', VExpr.lift'_mkApps, hlift] at hEt' H
  obtain ⟨_, _, hFt, hMt⟩ := hEt'.app_inv henv hΓ
  exact main n hΓ W (VLevel.forall₂_equiv_refl ls₀)
    (NormalEqF.forall₂_refl (η := true) fun a ha => mkApps_arg_type hΓ hFt ha) (.refl hMt) hEt H

end Lean4Lean.VEnv.Strengthening.PureObservation
