import Lean4Lean.Theory.Typing.Strengthening.CertifiedKComputation
import Lean4Lean.Theory.Typing.Strengthening.HybridSubstitution

/-! # Typed substitution for recursive K certificates

Homogeneous substitution preserves the computation and its certificate depth.
Source typing supplies well-formed binder contexts and intermediate typings.
This is a typed substitution theorem, not arbitrary raw substitution of guards.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params] {Cmp : List VExpr → VExpr → VExpr → Prop}

/-- At an unchanged context, descending guards give ordinary typed replay. -/
theorem GuardedKCompute.simAt (R : GuardedKCompute D Cmp Γ e out)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hc : EndpointDescent Cmp)
    (hΓ : OnCtx Γ (env.IsType univs)) : env.SimAt univs Γ e out :=
  R.simAt_below heq hs hc Ctx.Lift'.refl hΓ hΓ lift'_refl lift'_refl

/-- The matching relation's typed homogeneous substitution property. -/
def EndpointSubstitution (Cmp : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {Γ₀ e₀ A₀ k Γ₁ Γ a b α}, OnCtx Γ₁ (env.IsType univs) →
    env.HasType univs Γ₀ e₀ A₀ → Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ →
    env.HasType univs Γ₁ a α → env.HasType univs Γ₁ b α → Cmp Γ₁ a b →
    Cmp Γ (a.inst e₀ k) (b.inst e₀ k)

/-- Substitution may change the guard relation, as needed when a staged
argument requires a larger certificate depth. Replay types intermediate sources. -/
theorem GuardedKCompute.instN_to {Cmp' : List VExpr → VExpr → VExpr → Prop}
    (R : GuardedKCompute D Cmp Γ₁ e out)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hc : EndpointDescent Cmp)
    (hsub : ∀ {k Γ₁ Γ a b α}, OnCtx Γ₁ (env.IsType univs) →
      Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → env.HasType univs Γ₁ a α →
      env.HasType univs Γ₁ b α → Cmp Γ₁ a b →
      Cmp' Γ (a.inst e₀ k) (b.inst e₀ k))
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs))
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (ht : VExpr.WF env univs Γ₁ e) :
    GuardedKCompute D Cmp' Γ (e.inst e₀ k) (out.inst e₀ k) := by
  induction R generalizing k Γ with
  | base R =>
    apply GuardedKCompute.base
    simpa only [instN_eq] using R.subst (σ := .liftN (.one e₀) k)
  | eqRec H =>
    obtain ⟨_, _, _, ha, _, _, hb, _⟩ := eqRecApp_typings henv heq hΓ₁ ht
    exact .eqRec (hsub hΓ₁ W ha hb H)
  | trans R1 _ ih1 ih2 =>
    obtain ⟨T, ht⟩ := ht
    have hmid := (R1.simAt heq hs hc hΓ₁ T ht).hasType.2
    exact .trans (ih1 hΓ₁ W ⟨_, ht⟩) (ih2 hΓ₁ W ⟨_, hmid⟩)
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ₁
    exact .app (ih1 hΓ₁ W ⟨_, hf⟩) (ih2 hΓ₁ W ⟨_, ha⟩)
  | lam _ _ ih1 ih2 =>
    obtain ⟨hA, hb⟩ := ht.lam_inv henv hΓ₁
    exact .lam (ih1 hΓ₁ W (hA.elim fun _ h => ⟨_, h⟩)) (ih2 ⟨hΓ₁, hA⟩ W.succ hb)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨_, ht⟩ := ht
    obtain ⟨hA, hB⟩ := HasType.forallE_inv henv.ordered ht
    exact .forallE (ih1 hΓ₁ W (hA.elim fun _ h => ⟨_, h⟩))
      (ih2 ⟨hΓ₁, hA⟩ W.succ (hB.elim fun _ h => ⟨_, h⟩))
  | proj _ ih =>
    obtain ⟨_, ht⟩ := ht
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ :=
      HasType.proj_inv henv hΓ₁ ht
    exact .proj (ih hΓ₁ W ⟨_, hm.hasType.2⟩)

/-- Compatible computation inherits typed substitution of its guards. -/
theorem GuardedKCompute.instN (R : GuardedKCompute D Cmp Γ₁ e out)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hc : EndpointDescent Cmp)
    (hsub : EndpointSubstitution Cmp)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (h₀ : env.HasType univs Γ₀ e₀ A₀)
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (ht : VExpr.WF env univs Γ₁ e) :
    GuardedKCompute D Cmp Γ (e.inst e₀ k) (out.inst e₀ k) :=
  R.instN_to heq hs hc (fun hΓ W ha hb H => hsub hΓ h₀ W ha hb H) hΓ₁ W ht

/-- Homogeneous substitution preserves every finite certificate depth. A
HybridNormal comparison's own index may grow; it is existentially stored. -/
theorem KCertificate.substitution (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ depth, EndpointSubstitution (KCertificate D depth) := by
  intro depth
  induction depth with
  | zero =>
    intro Γ₀ e₀ A₀ k Γ₁ Γ a b α hΓ₁ h₀ W ha hb H
    obtain ⟨n, H⟩ := H
    exact H.instN hΓ₁ h₀ W
  | succ depth ih =>
    intro Γ₀ e₀ A₀ k Γ₁ Γ a b α hΓ₁ h₀ W ha hb H
    obtain ⟨a', b', n, Ra, Rb, H⟩ := H
    have Ra' := Ra.instN heq hs (KCertificate.descends heq hs depth) ih hΓ₁ h₀ W ⟨_, ha⟩
    have Rb' := Rb.instN heq hs (KCertificate.descends heq hs depth) ih hΓ₁ h₀ W ⟨_, hb⟩
    obtain ⟨n', H'⟩ := H.instN hΓ₁ h₀ W
    exact ⟨_, _, n', Ra', Rb', H'⟩

/-- Certified computation is stable under typed substitution, even when the
argument is a lambda and creates new redexes in the compared endpoints. -/
theorem CertifiedKCompute.instN (R : CertifiedKCompute D depth Γ₁ e out)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (h₀ : env.HasType univs Γ₀ e₀ A₀)
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (ht : VExpr.WF env univs Γ₁ e) :
    CertifiedKCompute D depth Γ (e.inst e₀ k) (out.inst e₀ k) :=
  GuardedKCompute.instN R heq hs (KCertificate.descends heq hs depth)
    (KCertificate.substitution heq hs depth) hΓ₁ h₀ W ht

end Lean4Lean.VEnv.Strengthening
