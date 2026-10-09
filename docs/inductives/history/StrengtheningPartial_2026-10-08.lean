import Lean4Lean.Theory.Typing.Confluence.WFParams

/-!
Partial results for declarative strengthening, 2026-10-08.

This file DOES NOT prove strengthening under canonical Eq. It proves that,
over a well-formed environment, full strengthening is equivalent to Cancel,
the cancellation of constant abstractions. It also proves the inhabited and
typed-retraction cases and gives a counterexample to support preservation by
the existing FullStep relation. No theorem below assumes Cancel implicitly.
-/

namespace Lean4Lean.StrengtheningPartial
open VEnv VExpr

theorem lam_body {env : VEnv} (henv : env.WF)
    {U : Nat} {Γ : List VExpr} {A b₁ b₂ : VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEqU U Γ (.lam A b₁) (.lam A b₂)) :
    env.IsDefEqU U (A :: Γ) b₁ b₂ := by
  obtain ⟨T, H⟩ := H
  obtain ⟨⟨u, hA⟩, B₁, hb₁⟩ := H.hasType.1.lam_inv henv.ordered hΓ
  obtain ⟨_, B₂, hb₂⟩ := H.hasType.2.lam_inv henv.ordered hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, u, hA⟩
  have hL : env.HasType U Γ (.lam A b₁) (.forallE A B₁) := .lamDF hA hb₁
  have hE := (IsDefEqU.of_l henv hΓ ⟨T, H⟩ hL).weakN henv.ordered (Ctx.LiftN.one (A := A))
  have hv : env.HasType U (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have hApp := IsDefEq.appDF hE hv
  have beta₁ := IsDefEq.beta (hb₁.weakN henv.ordered (Ctx.LiftN.succ Ctx.LiftN.one)) hv
  have beta₂ := IsDefEq.beta (hb₂.weakN henv.ordered (Ctx.LiftN.succ Ctx.LiftN.one)) hv
  have Hout := (IsDefEqU.trans henv hΓA ⟨_, beta₁.symm⟩ ⟨_, hApp⟩).trans henv hΓA ⟨_, beta₂⟩
  simpa only [lift, liftN, inst_liftN_bvar] using Hout

theorem inhabited {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} {Q q a b : VExpr}
    (hq : env.HasType U Γ q Q)
    (H : env.IsDefEqU U (Q :: Γ) a.lift b.lift) :
    env.IsDefEqU U Γ a b := by
  simpa only [inst_lift] using H.instN henv Ctx.InstN.zero hq

theorem lam_domain {env : VEnv} (henv : env.WF)
    {U : Nat} {Γ : List VExpr} {A₁ A₂ b₁ b₂ : VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEqU U Γ (.lam A₁ b₁) (.lam A₂ b₂)) :
    ∃ u, env.IsDefEq U Γ A₁ A₂ (.sort u) := by
  obtain ⟨T, H⟩ := H
  obtain ⟨⟨u₁, hA₁⟩, B₁, hb₁⟩ := H.hasType.1.lam_inv henv.ordered hΓ
  obtain ⟨⟨u₂, hA₂⟩, B₂, hb₂⟩ := H.hasType.2.lam_inv henv.ordered hΓ
  have hl : env.HasType U Γ (.lam A₁ b₁) (.forallE A₁ B₁) := .lamDF hA₁ hb₁
  have hr : env.HasType U Γ (.lam A₂ b₂) (.forallE A₂ B₂) := .lamDF hA₂ hb₂
  have e := IsDefEqU.of_l henv hΓ ⟨_, H⟩ hl
  exact ((e.uniqU henv hΓ hr).forallE_inv henv hΓ).1

def Front (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q a b⦄, OnCtx (Q :: Γ) (env.IsType U) →
    env.IsDefEqU U (Q :: Γ) a.lift b.lift → env.IsDefEqU U Γ a b

def Cancel (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q a b⦄, OnCtx Γ (env.IsType U) →
    env.IsDefEqU U Γ (.lam Q a.lift) (.lam Q b.lift) →
    env.IsDefEqU U Γ a b

theorem front_of_cancel {env : VEnv} (hc : Cancel env) : Front env := by
  intro U Γ Q a b hΓ H
  obtain ⟨hΓ, u, hQ⟩ := hΓ
  obtain ⟨T, H⟩ := H
  exact hc hΓ ⟨_, .lamDF hQ H⟩

theorem cancel_of_front {env : VEnv} (henv : env.WF) (hf : Front env) : Cancel env := by
  intro U Γ Q a b hΓ H
  obtain ⟨T, hT⟩ := H
  have hQ := (hT.hasType.1.lam_inv henv.ordered hΓ).1
  exact hf ⟨hΓ, hQ⟩ (lam_body henv hΓ ⟨T, hT⟩)

theorem front_block {env : VEnv} (hf : Front env)
    {U : Nat} {Γ As : List VExpr} {a b : VExpr}
    (hΓ : OnCtx (As ++ Γ) (env.IsType U))
    (H : env.IsDefEqU U (As ++ Γ) (a.liftN As.length) (b.liftN As.length)) :
    env.IsDefEqU U Γ a b := by
  induction As with
  | nil => simpa using H
  | cons Q As ih =>
    apply ih hΓ.1
    apply hf (a := a.liftN As.length) (b := b.liftN As.length) hΓ
    simpa [lift, liftN'_liftN_hi, Nat.add_comm] using H

def All (env : VEnv) : Prop :=
  ∀ ⦃U n k Γ Γ' a b⦄, Ctx.LiftN n k Γ Γ' → OnCtx Γ' (env.IsType U) →
    env.IsDefEqU U Γ' (a.liftN n k) (b.liftN n k) → env.IsDefEqU U Γ a b

theorem typed_of_untyped {env : VEnv} (henv : env.WF)
    {U n k : Nat} {Γ Γ' : List VExpr}
    (W : Ctx.LiftN n k Γ Γ') (hΓ : OnCtx Γ (env.IsType U))
    (hΓ' : OnCtx Γ' (env.IsType U))
    (down : ∀ {a b}, env.IsDefEqU U Γ' (a.liftN n k) (b.liftN n k) →
      env.IsDefEqU U Γ a b)
    {a b T : VExpr}
    (H : env.IsDefEq U Γ' (a.liftN n k) (b.liftN n k) (T.liftN n k)) :
    env.IsDefEq U Γ a b T := by
  obtain ⟨S, hS⟩ := down ⟨_, H⟩
  have hST := (hS.weakN henv.ordered W).uniqU henv hΓ' H.symm
  exact (down hST).defeqDF henv hΓ hS

theorem all_of_front {env : VEnv} (henv : env.WF) (hf : Front env) : All env := by
  intro U n k Γ Γ' a b W hΓ' H
  have aux : ∀ {k Γ Γ'}, Ctx.LiftN n k Γ Γ' → OnCtx Γ' (env.IsType U) →
      OnCtx Γ (env.IsType U) ∧
      (∀ {a b}, env.IsDefEqU U Γ' (a.liftN n k) (b.liftN n k) →
        env.IsDefEqU U Γ a b) := by
    intro k Γ Γ' W
    induction W with
    | zero As hn =>
      intro hΓ'
      subst n
      exact ⟨hΓ'.of_append, fun H => front_block hf hΓ' H⟩
    | @succ k Γ Γ' A W ih =>
      intro hΓ'
      obtain ⟨hΓ, down⟩ := ih hΓ'.1
      obtain ⟨u, hA'⟩ := hΓ'.2
      have hA : env.HasType U Γ A (.sort u) :=
        typed_of_untyped henv W hΓ hΓ'.1 down hA'
      refine ⟨⟨hΓ, u, hA⟩, ?_⟩
      intro a b H
      obtain ⟨T, H⟩ := H
      have HL : env.IsDefEqU U Γ (.lam A a) (.lam A b) :=
        down ⟨_, IsDefEq.lamDF hA' H⟩
      exact lam_body henv hΓ HL
  exact (aux W hΓ').2 H

theorem all_iff_cancel {env : VEnv} (henv : env.WF) : All env ↔ Cancel env := by
  constructor
  · intro hs
    apply cancel_of_front henv
    intro U Γ Q a b hΓ H
    exact hs Ctx.LiftN.one hΓ H
  · intro hc
    exact all_of_front henv (front_of_cancel hc)

theorem context_of_all {env : VEnv} (henv : env.WF) (hs : All env)
    {U n k : Nat} {Γ Γ' : List VExpr} (W : Ctx.LiftN n k Γ Γ')
    (hΓ' : OnCtx Γ' (env.IsType U)) : OnCtx Γ (env.IsType U) := by
  induction W with
  | zero As => exact hΓ'.of_append
  | succ W ih =>
    obtain ⟨hΔ', u, hA⟩ := hΓ'
    have hΔ := ih hΔ'
    exact ⟨hΔ, u, typed_of_untyped henv W hΔ hΔ' (hs W hΔ') hA⟩

theorem typed_of_all {env : VEnv} (henv : env.WF) (hs : All env)
    {U n k : Nat} {Γ Γ' : List VExpr} (W : Ctx.LiftN n k Γ Γ')
    (hΓ' : OnCtx Γ' (env.IsType U)) {a b T : VExpr}
    (H : env.IsDefEq U Γ' (a.liftN n k) (b.liftN n k) (T.liftN n k)) :
    env.IsDefEq U Γ a b T :=
  typed_of_untyped henv W (context_of_all henv hs W hΓ') hΓ' (hs W hΓ') H

theorem cancel_inhabited {env : VEnv} (henv : env.WF)
    {U : Nat} {Γ : List VExpr} {Q q a b : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (hq : env.HasType U Γ q Q)
    (H : env.IsDefEqU U Γ (.lam Q a.lift) (.lam Q b.lift)) :
    env.IsDefEqU U Γ a b :=
  inhabited henv.ordered hq (lam_body henv hΓ H)

theorem retract {env : VEnv} (henv : env.Ordered)
    {U n k : Nat} {Γ Γ' : List VExpr} {σ : VExpr.Subst} {a b : VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hσ : Ctx.SubstEq env U Γ σ σ Γ')
    (ha : (a.liftN n k).subst σ = a)
    (hb : (b.liftN n k).subst σ = b)
    (H : env.IsDefEqU U Γ' (a.liftN n k) (b.liftN n k)) :
    env.IsDefEqU U Γ a b := by
  simpa only [ha, hb] using H.subst henv hσ hΓ

section EtaSupport
open VEnv.Params
variable [VEnv.Params]

theorem compress_domain_equality {Γ : List VExpr} {A B : VExpr} {u : VLevel}
    (H : env.IsDefEq univs Γ A B (.sort u)) :
    NormalEqN false 1 Γ (.lam A (.sort .zero)) (.lam B (.sort .zero)) :=
  .lamDF H.hasType.1 H (.refl (.sort trivial))

def idProp : VExpr := .lam (.sort .zero) (.bvar 0)
def badDomain : VExpr := .app (.lam (.sort .zero) (.sort .zero)) (.bvar 0)

theorem eta_does_not_preserve_support :
    ∃ t, FullStep [.sort .zero] idProp.lift t ∧ ¬t.Skips 1 0 := by
  have hs {Δ : List VExpr} : env.HasType univs Δ (.sort .zero) (.sort (.succ .zero)) :=
    .sort trivial
  have hx : env.HasType univs [.sort .zero] (.bvar 0) (.sort .zero) := .bvar .zero
  have hd : env.IsDefEq univs [.sort .zero] badDomain (.sort .zero) (.sort (.succ .zero)) :=
    .beta hs hx
  have hf : env.HasType univs [.sort .zero] idProp (.forallE (.sort .zero) (.sort .zero)) :=
    .lamDF hs (.bvar .zero)
  have hp := IsDefEq.forallEDF hd.symm (hs (Δ := [.sort .zero, .sort .zero]))
  have hf' : env.HasType univs [.sort .zero] idProp (.forallE badDomain (.sort .zero)) :=
    .defeqDF hp hf
  refine ⟨.lam badDomain (.app idProp.lift (.bvar 0)), ?_, ?_⟩
  · simpa [idProp, lift, liftN, liftVar] using FullStep.funEta hf'
  · simp [VExpr.skips_iff, VExpr.Skips', badDomain]
end EtaSupport

#print axioms all_iff_cancel
#print axioms typed_of_all
#print axioms inhabited
#print axioms lam_domain
#print axioms compress_domain_equality
#print axioms eta_does_not_preserve_support
end Lean4Lean.StrengtheningPartial
