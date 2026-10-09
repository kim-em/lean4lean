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

end Lean4Lean.StrengtheningPartial

/-! Further investigation. The preceding partial results are reproduced so that this
file can be checked directly without installing an auxiliary module into the repository.
No result below claims the unresolved canonical-Eq cancellation theorem. -/
namespace Lean4Lean.StrengtheningContinuation
open VEnv VExpr StrengtheningPartial

/-- An uninhabited domain has no typed key in the observation model's target context. -/
theorem no_typed_key {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} {Q : VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hQ : ∀ q, ¬ env.HasType U Γ q Q) {c : VExpr → Prop} :
    ¬ Model.TypedElCls env U Γ (Model.TyCls env U Γ Q) c := by
  rintro ⟨q, X, hX, hq, _⟩
  exact hQ q (Model.TyCls.defeq henv hΓ hX hq)

/-- This is about a fixed target context, not about all Kripke extensions. -/
theorem no_lam_observation {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} {Q body : VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hQ : ∀ q, ¬ env.HasType U Γ q Q) :
    ∀ o, ¬ Model.OI env U Γ (.lam Q body) o := by
  intro o ho
  obtain ⟨c, K, x, τs, p, _, hc, _⟩ := Model.Obs.lam_iff.mp ho
  simp only [VExpr.subst_id] at hc
  exact no_typed_key henv hΓ hQ hc

/-- Fixed-target observations identify any two abstractions over an uninhabited domain. -/
theorem empty_domain_observation_eq {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} {Q a b : VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hQ : ∀ q, ¬ env.HasType U Γ q Q) :
    Model.OI env U Γ (.lam Q a) = Model.OI env U Γ (.lam Q b) := by
  funext o
  exact propext ⟨fun h => (no_lam_observation henv hΓ hQ o h).elim,
    fun h => (no_lam_observation henv hΓ hQ o h).elim⟩

/-- These two bodies have the same type Sort 1, but different type-former heads. -/
def bodySort : VExpr := .sort .zero
def bodyPi : VExpr := .forallE (.sort .zero) (.sort .zero)

theorem bodySort_typed {env : VEnv} {U : Nat} {Γ : List VExpr} :
    env.HasType U Γ bodySort (.sort (.succ .zero)) := .sort trivial

theorem bodyPi_typed {env : VEnv} {U : Nat} {Γ : List VExpr} :
    env.HasType U Γ bodyPi (.sort (.succ .zero)) := by
  have h : env.HasType U Γ bodyPi (.sort (.imax (.succ .zero) (.succ .zero))) :=
    .forallE (.sort trivial) (.sort trivial)
  exact .defeqDF (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero))
    (l' := .succ .zero) ⟨trivial, trivial⟩ trivial rfl) h

/-- A precise failure of reflection for the existing model at one fixed target.
The endpoints are typed at the SAME type; this is not a comparison of ill-typed terms.
The uninhabited-domain premise is explicit; no consistency theorem is assumed silently. -/
theorem fixed_target_not_reflecting {env : VEnv} (henv : env.WF)
    {U : Nat} {Γ : List VExpr} {Q : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (htQ : env.IsType U Γ Q)
    (hQ : ∀ q, ¬ env.HasType U Γ q Q) :
    ∃ a b T, env.HasType U Γ a T ∧ env.HasType U Γ b T ∧
      Model.OI env U Γ a = Model.OI env U Γ b ∧ ¬ env.IsDefEqU U Γ a b := by
  obtain ⟨u, htQ⟩ := htQ
  refine ⟨.lam Q bodySort, .lam Q bodyPi, .forallE Q (.sort (.succ .zero)),
    .lamDF htQ bodySort_typed, .lamDF htQ bodyPi_typed,
    empty_domain_observation_eq henv.ordered hΓ hQ, ?_⟩
  intro h
  have hΓQ : OnCtx (Q :: Γ) (env.IsType U) := ⟨hΓ, u, htQ⟩
  exact IsDefEqU.sort_forallE_inv henv hΓQ (lam_body henv hΓ h)

/-- Any substitution retraction with identity tail supplies an inhabitant of Q.
Thus a semantic anchor in the original target cannot evade the inhabited-binder case. -/
theorem retraction_requires_inhabitant {env : VEnv} {U : Nat} {Γ : List VExpr}
    {Q : VExpr} {σ : VExpr.Subst}
    (hσ : Ctx.SubstEq env U Γ σ σ (Q :: Γ)) (htail : σ.tail = .id) :
    env.HasType U Γ σ.head Q := by
  cases hσ with
  | cons _ _ h =>
    change env.IsDefEq U Γ σ.head σ.head Q
    simpa only [htail, VExpr.subst_id] using h

/-- The empty-domain obstruction is independent of the observation sets:
all valuations with identity anchor in this target context see no lambda output. -/
theorem empty_domain_all_sets {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} {Q a b : VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hQ : ∀ q, ¬ env.HasType U Γ q Q) (S : Model.ObSets) :
    Model.Obs env U Γ .id S (.lam Q a) = Model.Obs env U Γ .id S (.lam Q b) := by
  have hnone (body : VExpr) (o : Model.Ob) :
      ¬ Model.Obs env U Γ .id S (.lam Q body) o := by
    intro ho
    obtain ⟨c, K, x, τs, p, _, hc, _⟩ := Model.Obs.lam_iff.mp ho
    simp only [VExpr.subst_id] at hc
    exact no_typed_key henv hΓ hQ hc
  funext o
  exact propext ⟨fun h => (hnone a o h).elim, fun h => (hnone b o h).elim⟩

/-- An unconditional limitation of OI: its variable observation sets are empty.
The two variables are unequal, as witnessed by substitution of Sort 0 and a Pi.
This is valid for every WF environment, including any with canonical Eq. -/
theorem fixed_oi_counterexample {env : VEnv} (henv : env.WF) (U : Nat) :
    ∃ Γ a b T, OnCtx Γ (env.IsType U) ∧
      env.HasType U Γ a T ∧ env.HasType U Γ b T ∧
      Model.OI env U Γ a = Model.OI env U Γ b ∧ ¬ env.IsDefEqU U Γ a b := by
  let S : VExpr := .sort (.succ .zero)
  let Γ : List VExpr := [S, S]
  have hs {Δ : List VExpr} : env.HasType U Δ S (.sort (.succ (.succ .zero))) :=
    .sort trivial
  have hΓ : OnCtx Γ (env.IsType U) := ⟨⟨trivial, _, hs⟩, _, hs⟩
  refine ⟨Γ, .bvar 0, .bvar 1, S, hΓ, .bvar .zero, .bvar (.succ .zero), ?_, ?_⟩
  · funext o
    apply propext
    simp [Model.OI, Model.Obs.bvar_iff, Model.ObSets.empty]
  · intro H
    have H₁ := H.instN henv.ordered Ctx.InstN.zero
      (bodySort_typed (env := env) (U := U) (Γ := [S]))
    have H₂ := H₁.instN henv.ordered Ctx.InstN.zero
      (bodyPi_typed (env := env) (U := U) (Γ := []))
    have H₃ : env.IsDefEqU U [] (.sort .zero) (.forallE (.sort .zero) (.sort .zero)) := by
      simpa [bodySort, bodyPi, VExpr.inst, VExpr.instVar] using H₂
    exact IsDefEqU.sort_forallE_inv henv (show OnCtx [] (env.IsType U) from trivial) H₃

/-! The eta counterexample does admit a repaired witness. This is deliberately
an actual pair of reductions, not only a declarative equality of the endpoints. -/
section EtaRepair
open VEnv.Params
variable [VEnv.Params]

def etaGood : VExpr := .lam (.sort .zero) (.app idProp.lift (.bvar 0))
def etaBad : VExpr := .lam badDomain (.app idProp.lift (.bvar 0))

theorem eta_good_step : FullStep [] idProp etaGood := by
  have hs : env.HasType univs [] (.sort .zero) (.sort (.succ .zero)) := .sort trivial
  exact .funEta (IsDefEq.lamDF hs (.bvar .zero))

theorem eta_bad_repair_step : FullStep [.sort .zero] etaBad etaGood.lift := by
  have h : FullStep [.sort .zero] etaBad etaGood :=
    .lam (.core (.beta .rfl .rfl)) .rfl
  simpa [etaGood, idProp, lift, liftN, liftVar] using h

omit [Params] in
theorem eta_good_supported : etaGood.lift.Skips 1 0 := by
  simp [VExpr.skips_iff, VExpr.Skips', etaGood, idProp, lift, liftN, liftVar]

/-- Repair of the precise support counterexample from the previous attempt. -/
theorem eta_obstruction_repaired :
    ∃ t, FullStep [] idProp t ∧ FullStep [.sort .zero] etaBad t.lift ∧ t.lift.Skips 1 0 :=
  ⟨etaGood, eta_good_step, eta_bad_repair_step, eta_good_supported⟩
end EtaRepair

/-! A support-preserving reduction with every side condition already certified
in the smaller context. The parameter `W` records where the context was inserted.
It is not enough to require only that both endpoints skip the inserted variables. -/
section CertifiedRepair
open VEnv.Params
variable [VEnv.Params]

inductive DescendingStep {n k : Nat} {Γ Γ' : List VExpr}
    (W : Ctx.LiftN n k Γ Γ') : VExpr → VExpr → Prop where
  | lift {a b} : FullStep Γ a b →
      DescendingStep W (a.liftN n k) (b.liftN n k)

theorem DescendingStep.full {W : Ctx.LiftN n k Γ Γ'}
    {a b : VExpr} (h : DescendingStep W a b) : FullStep Γ' a b := by
  cases h with | lift h => exact h.weakN W

/-- Exact descent of certified steps uses only injectivity of syntax lifting. -/
theorem DescendingStep.down {W : Ctx.LiftN n k Γ Γ'} {a : VExpr}
    {b' : VExpr} (h : DescendingStep W (a.liftN n k) b') :
    ∃ b, b' = b.liftN n k ∧ FullStep Γ a b := by
  generalize hs : a.liftN n k = a' at h
  cases h with
  | @lift a₀ b h =>
    have : a₀ = a := VExpr.liftN_inj.mp hs.symm
    subst a₀
    exact ⟨b, rfl, h⟩

/-- Finite-path descent. The induction measure is the length of the path;
no induction on declarative equality is hidden here. -/
theorem descending_path_down {W : Ctx.LiftN n k Γ Γ'} {a : VExpr}
    {b' : VExpr} (h : ReflTransGen (DescendingStep W) (a.liftN n k) b') :
    ∃ b, b' = b.liftN n k ∧ FullReduction Γ a b := by
  induction h with
  | rfl => exact ⟨a, rfl, .rfl⟩
  | tail _ hs ih =>
    obtain ⟨b, rfl, hb⟩ := ih
    obtain ⟨c, rfl, hc⟩ := hs.down
    exact ⟨c, rfl, hb.tail hc⟩

theorem descending_path_up {W : Ctx.LiftN n k Γ Γ'} {a b : VExpr}
    (H : FullReduction Γ a b) :
    ReflTransGen (DescendingStep W) (a.liftN n k) (b.liftN n k) := by
  induction H with
  | rfl => exact .rfl
  | tail _ hs ih => exact ih.tail (.lift hs)

/-- Substitution of an actual inhabitant acts on ALL full steps, including
singleton/quotient unfolding and both eta rules. The induction is on the step
constructor; under binders Ctx.InstN.succ increases the insertion depth. -/
theorem fullStep_instN {Γ₀ Γ₁ Γ : List VExpr} {q Q a b : VExpr} {k : Nat}
    (W : Ctx.InstN Γ₀ q Q k Γ₁ Γ) (hq : env.HasType univs Γ₀ q Q)
    (H : FullStep Γ₁ a b) : FullStep Γ (a.inst q k) (b.inst q k) := by
  induction H generalizing Γ k with
  | core h => exact .core (ParRed.instN .rfl hq W h)
  | delta h =>
    simpa only [VExpr.inst_mkApps, VExpr.inst] using FullStep.delta (h.instN henv W hq)
  | quotDelta h =>
    simpa only [VExpr.inst_mkApps, VExpr.inst] using FullStep.quotDelta (h.instN henv W hq)
  | projIota hi hs hf ht =>
    have hs' := hs.instN henv W hq
    simp only [VExpr.inst_mkApps, VExpr.inst] at hs' ⊢
    exact .projIota hi hs' (by simp [hf]) (ht.instN henv W hq)
  | structEta hi hl hn hs ht =>
    have hs' := hs.instN henv W hq
    have ht' := ht.instN henv W hq
    simp only [VExpr.inst_mkApps, VExpr.inst, List.map_append, List.map_map,
      Function.comp_def] at hs' ht' ⊢
    exact .structEta hi (by simpa using hl) hn hs' ht'
  | funEta ht =>
    simpa only [VExpr.inst, ← VExpr.lift_instN_lo, VExpr.instVar_lower] using
      FullStep.funEta (ht.instN henv W hq)
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | proj _ ih => exact .proj (ih W)
  | lam _ _ ihd ihb => exact .lam (ihd W) (ihb W.succ)
  | forallE _ _ ihd ihb => exact .forallE (ihd W) (ihb W.succ)

/-- The path length is unchanged by substitution. -/
theorem fullReduction_instN {Γ₀ Γ₁ Γ : List VExpr} {q Q a b : VExpr} {k : Nat}
    (W : Ctx.InstN Γ₀ q Q k Γ₁ Γ) (hq : env.HasType univs Γ₀ q Q)
    (H : FullReduction Γ₁ a b) : FullReduction Γ (a.inst q k) (b.inst q k) := by
  induction H with
  | rfl => exact .rfl
  | tail _ hs ih => exact ih.tail (fullStep_instN W hq hs)

/-- Witness repair is complete for an inhabited removed binder: the new
endpoint is t[q], and every step carries its certificates in the smaller context.
This makes no claim that the old target t was supported. -/
theorem repair_reduction_inhabited {Γ : List VExpr} {q Q a t : VExpr}
    (hq : env.HasType univs Γ q Q) (H : FullReduction (Q :: Γ) a.lift t) :
    FullReduction Γ a (t.inst q) := by
  simpa only [VExpr.inst_lift] using fullReduction_instN Ctx.InstN.zero hq H

/-- A repaired join includes source typing. FullReduction alone does not
certify typing (it even has reflexive paths at arbitrary raw expressions). -/
def TypedJoin (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ A B x y, env.HasType univs Γ a A ∧ env.HasType univs Γ b B ∧
    FullReduction Γ a x ∧ FullReduction Γ b y ∧ NormalEq Γ x y

theorem TypedJoin.defeq {Γ : List VExpr} {a b : VExpr}
    (hΓ : OnCtx Γ (env.IsType univs)) (h : TypedJoin Γ a b) :
    env.IsDefEqU univs Γ a b := by
  obtain ⟨A, B, x, y, ha, hb, hx, hy, hn⟩ := h
  exact (IsDefEqU.trans henv hΓ ⟨A, hx.defeq hΓ ha⟩ (hn.defeq hΓ)).trans
    henv hΓ ⟨B, (hy.defeq hΓ hb).symm⟩

/-- This is the completeness interface actually needed by witness repair.
It replaces a JOIN, not an arbitrary terminal expression by the same expression.
Both original source typings may have types depending on the deleted binder. -/
def JoinRepair : Prop :=
  ∀ {Γ Q a b A B x y}, OnCtx (Q :: Γ) (env.IsType univs) →
    env.HasType univs (Q :: Γ) a.lift A →
    env.HasType univs (Q :: Γ) b.lift B →
    FullReduction (Q :: Γ) a.lift x → FullReduction (Q :: Γ) b.lift y →
    NormalEq (Q :: Γ) x y → TypedJoin Γ a b
end CertifiedRepair

/-- The base equation-coverage obligation admits fully supported witnesses.
Canonical Eq is used by Church-Rosser for zero-source singleton equations.
This does NOT repair a contextual alignment witness of an arbitrary redex. -/
theorem installed_equation_supported_join {env : VEnv} (henv : env.WF)
    (heq : env.HasCanonicalEq) {U n k : Nat} {Γ Γ' : List VExpr}
    (W : Ctx.LiftN n k Γ Γ') (hΓ : OnCtx Γ (env.IsType U))
    {df : VDefEq} {ls : List VLevel} (hdf : env.defeqs df)
    (hw : ∀ l ∈ ls, l.WF U) (hl : ls.length = df.uvars) :
    letI := henv.params U
    ∃ x y : VExpr,
      ReflTransGen (DescendingStep W) ((df.lhs.instL ls).liftN n k) (x.liftN n k) ∧
      ReflTransGen (DescendingStep W) ((df.rhs.instL ls).liftN n k) (y.liftN n k) ∧
      NormalEq Γ' (x.liftN n k) (y.liftN n k) := by
  letI := henv.params U
  have H : env.IsDefEq U Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) :=
    .extra hdf hw hl
  obtain ⟨x, y, hx, hy, hn⟩ := henv.church_rosser heq hΓ H
  exact ⟨x, y, descending_path_up hx, descending_path_up hy, hn.weakN W⟩

/-- Every use of canonical Eq here is explicit: it supplies existing
Church-Rosser. This theorem DOES NOT prove the JoinRepair premise. -/
theorem front_of_joinRepair {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq)
    (repair : ∀ U, @JoinRepair (henv.params U)) : Front env := by
  intro U Γ Q a b hΓ H
  letI := henv.params U
  obtain ⟨T, H⟩ := H
  obtain ⟨x, y, hx, hy, hn⟩ := henv.church_rosser heq hΓ H
  exact TypedJoin.defeq hΓ.1 (repair U hΓ H.hasType.1 H.hasType.2 hx hy hn)

/-- The converse establishes the exact logical strength of this repair
interface; it is not a weaker replacement for the unresolved theorem. -/
theorem joinRepair_of_front {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq)
    (hf : Front env) (U : Nat) : @JoinRepair (henv.params U) := by
  letI := henv.params U
  intro Γ Q a b A B x y hΓ ha hb hx hy hn
  have h : env.IsDefEqU U (Q :: Γ) a.lift b.lift :=
    TypedJoin.defeq hΓ ⟨A, B, x, y, ha, hb, hx, hy, hn⟩
  obtain ⟨T, h⟩ := hf hΓ h
  obtain ⟨x, y, hx, hy, hn⟩ := henv.church_rosser heq hΓ.1 h
  exact ⟨T, T, x, y, h.hasType.1, h.hasType.2, hx, hy, hn⟩

theorem cancel_iff_joinRepair {env : VEnv} (henv : env.WF)
    (heq : env.HasCanonicalEq) :
    Cancel env ↔ ∀ U, @JoinRepair (henv.params U) := by
  constructor
  · exact fun hc => joinRepair_of_front henv heq (front_of_cancel hc)
  · exact fun hr => cancel_of_front henv (front_of_joinRepair henv heq hr)

/-- Exact conditional completion through the new interface. The repair
hypothesis is explicit; the theorem is not advertised as strengthening from Eq. -/
theorem all_of_joinRepair {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq)
    (repair : ∀ U, @JoinRepair (henv.params U)) : All env :=
  all_of_front henv (front_of_joinRepair henv heq repair)

/-! A local test of approach A. Merely counting the new comparisons is not
"deep" certification when the typing premises retain unrestricted conversion.
The following candidate records both requested comparisons, and its soundness
and remaining compression bug are checked below. It is a fragment, not a new
complete presentation or a claimed confluence theorem. -/
section DomainCounting
open VEnv.Params
variable [VEnv.Params]

inductive DomainCountedN : Nat → List VExpr → VExpr → VExpr → Prop where
  | refl : env.HasType univs Γ e A → DomainCountedN 0 Γ e e
  | lam : env.HasType univs Γ A (.sort u) →
      DomainCountedN n Γ A B → DomainCountedN m (A :: Γ) a b →
      DomainCountedN (n + m + 1) Γ (.lam A a) (.lam B b)
  | proofIrrel : env.HasType univs Γ P (.sort .zero) →
      env.HasType univs Γ Q (.sort .zero) →
      env.HasType univs Γ a P → env.HasType univs Γ b Q →
      DomainCountedN n Γ P Q → DomainCountedN (n + 1) Γ a b

theorem DomainCountedN.toNormal {Γ : List VExpr} {a b : VExpr}
    (hΓ : OnCtx Γ (env.IsType univs)) (H : DomainCountedN n Γ a b) :
    NormalEq Γ a b := by
  induction H with
  | refl h => exact .refl h
  | lam hA _ _ ihA ihb =>
    have hd := ((ihA hΓ).defeq hΓ).of_l henv hΓ hA
    exact .lamDF hA hd (ihb ⟨hΓ, _, hA⟩)
  | proofIrrel hP _ ha hb _ ih =>
    have hPQ := ((ih hΓ).defeq hΓ).of_l henv hΓ hP
    exact .proofIrrel hP ha (.defeqDF hPQ.symm hb)

/-- Context transport preserves this candidate's rank only because the
transported typing witnesses remain opaque, uncounted declarative derivations. -/
theorem DomainCountedN.defeqDFC {Γ₀ Γ₁ Γ₂ : List VExpr}
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    {a b : VExpr} (H : DomainCountedN n Γ₁ a b) : DomainCountedN n Γ₂ a b := by
  induction H generalizing Γ₂ with
  | refl h => exact .refl (h.defeqDFC henv W)
  | lam hA _ _ ihA ihb =>
    exact .lam (hA.defeqDFC henv W) (ihA W) (ihb (.succ W hA))
  | proofIrrel hP hQ ha hb _ ih =>
    exact .proofIrrel (hP.defeqDFC henv W) (hQ.defeqDFC henv W)
      (ha.defeqDFC henv W) (hb.defeqDFC henv W) (ih W)

/-- Transitivity of the candidate fragment, by n₁+n₂. Both lambda domain
composition and body composition decrease that sum. This does not supply a
rank for recursively certified typing or reduction-side certificates. -/
theorem DomainCountedN.trans (hΓ : OnCtx Γ (env.IsType univs)) :
    DomainCountedN n₁ Γ a b → DomainCountedN n₂ Γ b c →
    ∃ n, DomainCountedN n Γ a c
  | .refl _, H => ⟨_, H⟩
  | H, .refl _ => ⟨_, H⟩
  | .proofIrrel hP hQ ha hb hPQ, H => by
    have hBP : env.HasType univs Γ _ _ :=
      IsDefEq.defeqDF (((hPQ.toNormal hΓ).defeq hΓ).of_l henv hΓ hP).symm hb
    have hCP := hBP.defeqU_l henv hΓ ((H.toNormal hΓ).defeq hΓ)
    exact ⟨1, .proofIrrel hP hP ha hCP (.refl hP)⟩
  | H, .proofIrrel hP hQ hb hc hPQ => by
    have hAP := hb.defeqU_l henv hΓ ((H.toNormal hΓ).defeq hΓ).symm
    exact ⟨_, .proofIrrel hP hQ hAP hc hPQ⟩
  | .lam hA hAB hab, .lam hB hBC hbc => by
    obtain ⟨nd, hd⟩ := hAB.trans hΓ hBC
    have hBA := (((hAB.toNormal hΓ).defeq hΓ).of_l henv hΓ hA).symm
    have hbc' := hbc.defeqDFC (.succ (.zero (Γ₀ := Γ)) hBA)
    obtain ⟨nb, hb⟩ := hab.trans (Γ := _ :: Γ) ⟨hΓ, _, hA⟩ hbc'
    exact ⟨nd + nb + 1, .lam hA hd hb⟩
termination_by n₁ + n₂

/-- The lambda domain really is charged, instead of using NormalEqN.lamDF's
opaque domain equality. -/
theorem domain_counted {Γ : List VExpr} {A B : VExpr} {u : VLevel}
    (hA : env.HasType univs Γ A (.sort u)) (h : DomainCountedN n Γ A B) :
    DomainCountedN (n + 1) Γ (.lam A (.sort .zero)) (.lam B (.sort .zero)) := by
  exact .lam hA h (.refl (HasType.sort (l := .zero) trivial))

/-- Yet arbitrary type agreement can still be hidden at index ONE, by
moving the conversion into the right-hand typing witness and choosing P=P.
Thus witnessed agreement of two freely chosen types is insufficient. -/
theorem alignment_can_be_hidden {Γ : List VExpr} {P Q a b : VExpr}
    (H : env.IsDefEq univs Γ P Q (.sort .zero))
    (ha : env.HasType univs Γ a P) (hb : env.HasType univs Γ b Q) :
    DomainCountedN 1 Γ a b :=
  .proofIrrel H.hasType.1 H.hasType.1 ha
    (.defeqDF H.symm hb) (.refl H.hasType.1)
end DomainCounting

/-! If typing certificates are also made structural, their size cannot stay
bounded under arbitrary typed substitution by a function of the source size
alone. The example below keeps the source term, source type and both contexts
fixed. Only the substitution witness varies. -/

def typeTower : Nat → VExpr
  | 0 => .sort .zero
  | n + 1 => .forallE (.sort .zero) (typeTower n)

/-- Counts nested displayed binders on the body's path; defined on all syntax. -/
def binderDepth : VExpr → Nat
  | .lam _ b | .forallE _ b => binderDepth b + 1
  | _ => 0

theorem typeTower_depth (n : Nat) : binderDepth (typeTower n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [typeTower, binderDepth, ih]

theorem typeTower_typed {env : VEnv} {U : Nat} (n : Nat) (Γ : List VExpr) :
    env.HasType U Γ (typeTower n) (.sort (.succ .zero)) := by
  induction n generalizing Γ with
  | zero => exact .sort trivial
  | succ n ih =>
    have h : env.HasType U Γ (typeTower (n + 1))
        (.sort (.imax (.succ .zero) (.succ .zero))) :=
      .forallE (.sort trivial) (ih _)
    exact .defeqDF (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero))
      (l' := .succ .zero) ⟨trivial, trivial⟩ trivial rfl) h

/-- A fixed, typed variable has substitutions of unbounded displayed depth.
This refutes a source-only size bound, not every possible cut-elimination rank. -/
theorem typed_substitution_unbounded {env : VEnv} {U : Nat} (N : Nat) :
    ∃ σ : VExpr.Subst,
      Ctx.SubstEq env U [] σ σ [.sort (.succ .zero)] ∧
      env.HasType U [.sort (.succ .zero)] (.bvar 0) (.sort (.succ .zero)) ∧
      N < binderDepth ((.bvar 0 : VExpr).subst σ) := by
  let σ : VExpr.Subst := VExpr.Subst.id.cons (typeTower (N + 1))
  have hσ : Ctx.SubstEq env U [] σ σ [.sort (.succ .zero)] :=
    .cons .nil (HasType.sort trivial) (typeTower_typed (N + 1) [])
  refine ⟨σ, hσ, .bvar .zero, ?_⟩
  change N < binderDepth (typeTower (N + 1))
  rw [typeTower_depth]
  omega

/-- No substitution-independent numeric bound exists even for this fixed source. -/
theorem no_source_only_substitution_bound {env : VEnv} {U : Nat} :
    ¬ ∃ N, ∀ σ : VExpr.Subst,
      Ctx.SubstEq env U [] σ σ [.sort (.succ .zero)] →
      binderDepth ((.bvar 0 : VExpr).subst σ) ≤ N := by
  rintro ⟨N, hN⟩
  obtain ⟨σ, hσ, _, hlt⟩ := typed_substitution_unbounded (env := env) (U := U) N
  have := hN σ hσ
  omega

#print axioms fixed_oi_counterexample
#print axioms empty_domain_all_sets
#print axioms fixed_target_not_reflecting
#print axioms retraction_requires_inhabitant
#print axioms eta_obstruction_repaired
#print axioms descending_path_down
#print axioms fullStep_instN
#print axioms repair_reduction_inhabited
#print axioms installed_equation_supported_join
#print axioms cancel_iff_joinRepair
#print axioms all_of_joinRepair
#print axioms DomainCountedN.toNormal
#print axioms DomainCountedN.trans
#print axioms alignment_can_be_hidden
#print axioms no_source_only_substitution_bound
end Lean4Lean.StrengtheningContinuation

namespace Lean4Lean.StrengtheningKripke
open VEnv VExpr StrengtheningPartial StrengtheningContinuation
open VEnv.Model

/-- All well-formed targets, all typed anchors, and all backed, typed variable
observations. Equality here is mutual subsumption, not equality of raw sets. -/
def KEq (env : VEnv) (U : Nat) (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∀ (Δ : List VExpr) (σ : VExpr.Subst) (S : ObSets),
    OnCtx Δ (env.IsType U) → Ctx.SubstEq env U Δ σ σ Γ →
    TV env U Δ Γ σ S →
    Ob.Sub (Obs env U Δ σ S a) (Obs env U Δ σ S b) ∧
    Ob.Sub (Obs env U Δ σ S b) (Obs env U Δ σ S a)

theorem KEq.sound {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (H : env.IsDefEqU U Γ a b) :
    KEq env U Γ a b := by
  obtain ⟨T, H⟩ := H
  intro Δ σ S hΔ hσ hS
  have Hs := (henv.soundEnv hΔ (H.strong henv.ordered hΓ)).1 σ σ S hσ hS hS
  exact ⟨Hs.1, Hs.2.1⟩

theorem KEq.symm (H : KEq env U Γ a b) : KEq env U Γ b a :=
  fun Δ σ S hΔ hσ hS => (H Δ σ S hΔ hσ hS).symm

theorem KEq.trans (H : KEq env U Γ a b) (H' : KEq env U Γ b c) :
    KEq env U Γ a c := by
  intro Δ σ S hΔ hσ hS
  have h := H Δ σ S hΔ hσ hS
  have h' := H' Δ σ S hΔ hσ hS
  exact ⟨h.1.trans h'.1, h'.2.trans h.2⟩

theorem proof_no_observations {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (hP : env.HasType U Γ P (.sort .zero))
    (ha : env.HasType U Γ a P) (hΔ : OnCtx Δ (env.IsType U))
    (hσ : Ctx.SubstEq env U Δ σ σ Γ) (hS : TV env U Δ Γ σ S) :
    ∀ o, ¬ Obs env U Δ σ S a o := by
  have ihP := (henv.soundEnv hΔ (hP.strong henv.ordered hΓ)).1 σ σ S hσ hS hS
  have iha := (henv.soundEnv hΔ (ha.strong henv.ordered hΓ)).1 σ σ S hσ hS hS
  intro o ho
  obtain ⟨τs, hτs, ht⟩ := iha.2.2.1 o ho
  exact ht.not_prop fun τ hτ => ⟨_, typedAt_sort_iff.1 (ihP.2.2.1 τ (hτs τ hτ))⟩

/-- KEq forgets proof TYPES: common typing must be retained in reflection. -/
theorem KEq.proofs {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (hP : env.HasType U Γ P (.sort .zero))
    (hQ : env.HasType U Γ Q (.sort .zero))
    (ha : env.HasType U Γ a P) (hb : env.HasType U Γ b Q) : KEq env U Γ a b := by
  intro Δ σ S hΔ hσ hS
  exact ⟨fun o ho => (proof_no_observations henv hΓ hP ha hΔ hσ hS o ho).elim,
    fun o ho => (proof_no_observations henv hΓ hQ hb hΔ hσ hS o ho).elim⟩

/-- Fresh target keys exist without a term of Q in the source context. -/
theorem fresh_key {env : VEnv} {U : Nat} (Γ : List VExpr) (Q : VExpr) :
    TypedElCls env U (Q :: Γ) (TyCls env U (Q :: Γ) Q.lift)
      (ElCls env U (Q :: Γ) (TyCls env U (Q :: Γ) Q.lift) (.bvar 0)) :=
  TypedElCls.of_hasType (show env.HasType U (Q :: Γ) (.bvar 0) Q.lift from .bvar .zero)

/-- This one observation suffices to distinguish the first variable from a
second variable with the SAME type. No identity/name observation is needed here. -/
def distinguishSets : ObSets :=
  fun i o => i = 0 ∧ o = .sort (fun _ => 0)

theorem distinguishSets_typed {env : VEnv} {U : Nat} {Δ : List VExpr}
    (σ : VExpr.Subst) :
    TV env U Δ [.sort (.succ .zero), .sort (.succ .zero)] σ distinguishSets := by
  constructor
  · intro i o ho w hw
    obtain ⟨_, rfl⟩ := ho
    cases hw
  · intro i A hL o ho
    obtain ⟨rfl, rfl⟩ := ho
    cases hL with
    | zero =>
      refine ⟨[.sort (fun _ => 1)], ?_, ?_⟩
      · intro τ hτ
        simp only [List.mem_singleton] at hτ
        subst τ
        exact .sort
      · exact .sort (by simp)

theorem KEq.separates_variables {env : VEnv} (henv : env.WF) (U : Nat) :
    ¬ KEq env U [.sort (.succ .zero), .sort (.succ .zero)] (.bvar 0) (.bvar 1) := by
  let Γ : List VExpr := [.sort (.succ .zero), .sort (.succ .zero)]
  have hs {Δ : List VExpr} : env.IsType U Δ (.sort (.succ .zero)) :=
    ⟨_, .sort trivial⟩
  have hΓ : OnCtx Γ (env.IsType U) := ⟨⟨trivial, hs⟩, hs⟩
  intro H
  obtain ⟨o, ho, _⟩ := (H Γ .id distinguishSets hΓ
    (Ctx.SubstEq.id henv.ordered hΓ) (distinguishSets_typed .id)).1
      _ (.bvar ⟨rfl, rfl⟩)
  have := (Obs.bvar_iff.mp ho).1
  contradiction

/-- Observing only the variable's type (or a chain computed from that type)
necessarily loses this distinction. This applies to ANY such observation set F. -/
theorem type_only_sets_collapse (F : VExpr → Ob → Prop)
    {env : VEnv} {U : Nat} {Δ : List VExpr} (σ : VExpr.Subst) :
    Obs env U Δ σ (fun _ => F (.sort (.succ .zero))) (.bvar 0) =
    Obs env U Δ σ (fun _ => F (.sort (.succ .zero))) (.bvar 1) := by
  funext o
  simp only [Obs.bvar_iff]

/-- In the fresh target, a lambda with constant Sort 0 body has an application
observation whose result is sort 0. The finite key list may be empty. -/
theorem fresh_lam_sort_observation {env : VEnv} {U : Nat} (Γ : List VExpr) (Q : VExpr) :
    Obs env U (Q :: Γ) (fun i => .bvar (i + 1)) .empty
      (.lam Q bodySort)
      (.app (TyCls env U (Q :: Γ) Q.lift)
        (ElCls env U (Q :: Γ) (TyCls env U (Q :: Γ) Q.lift) (.bvar 0))
        [] (.sort (fun _ => 0))) := by
  have he : Q.subst (fun i => .bvar (i + 1)) = Q.lift := by
    change Q.subst (.lift_r .id (.skip .refl)) = Q.lift
    rw [← VExpr.lift'_subst, VExpr.subst_id, ← VExpr.lift_eq_lift']
  rw [← he]
  apply Obs.lam (τs := []) (x := .bvar 0)
  · rw [he]
    exact fresh_key Γ Q
  · simp
  · simp
  · intro o ho
    cases ho
  · exact ElCls.self
  · exact .sort

/-- Any target admitting a typed anchor for Γ and a key for Q distinguishes
these abstractions. We choose the target Q::Γ, so no inhabitant in Γ is used. -/
theorem KEq.separates_empty_domain_lambdas {env : VEnv} (henv : env.WF)
    {U : Nat} {Γ : List VExpr} {Q : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (hQ : env.IsType U Γ Q) :
    ¬ KEq env U Γ (.lam Q bodySort) (.lam Q bodyPi) := by
  intro H
  have hΔ : OnCtx (Q :: Γ) (env.IsType U) := ⟨hΓ, hQ⟩
  have hσ : Ctx.SubstEq env U (Q :: Γ) (fun i => .bvar (i + 1))
      (fun i => .bvar (i + 1)) Γ := by
    exact (Ctx.SubstEq.id henv.ordered hΓ).skip henv.ordered
  obtain ⟨o, ho, hl⟩ := (H (Q :: Γ) _ .empty hΔ hσ TV.empty).1
    _ (fresh_lam_sort_observation Γ Q)
  obtain ⟨K, p, rfl, _, hp⟩ := hl.app_inv
  rw [hp.sort_inv] at ho
  obtain ⟨c, K', x, τs, p', he, _, _, _, _, _, hb⟩ := Obs.lam_iff.mp ho
  have hp' := (Ob.app.inj he).2.2.2
  rw [← hp'] at hb
  exact Model.forallE_not_sort hb

/-- The obstruction to transporting class-valued keys back is already a
restricted strengthening theorem, not an untyped injectivity fact. -/
def KeyFaithful (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q a b T⦄, OnCtx Γ (env.IsType U) → env.IsType U Γ Q →
    env.HasType U Γ a T → env.HasType U Γ b T →
    ElCls env U (Q :: Γ) (TyCls env U (Q :: Γ) T.lift) a.lift =
      ElCls env U (Q :: Γ) (TyCls env U (Q :: Γ) T.lift) b.lift →
    ElCls env U Γ (TyCls env U Γ T) a = ElCls env U Γ (TyCls env U Γ T) b

def TypedFront (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q a b T⦄, OnCtx Γ (env.IsType U) → env.IsType U Γ Q →
    env.HasType U Γ a T → env.HasType U Γ b T →
    env.IsDefEq U (Q :: Γ) a.lift b.lift T.lift → env.IsDefEq U Γ a b T

theorem keyFaithful_iff_typedFront {env : VEnv} (henv : env.WF) :
    KeyFaithful env ↔ TypedFront env := by
  constructor
  · intro hk U Γ Q a b T hΓ hQ ha hb H
    have he := hk hΓ hQ ha hb (ElCls.eq_of_defeq TyCls.self H)
    have hm : ElCls env U Γ (TyCls env U Γ T) a b := by
      rw [he]; exact ElCls.self
    exact ElCls.collapse henv.ordered hΓ ha TyCls.self hm
  · intro hf U Γ Q a b T hΓ hQ ha hb he
    have hm : ElCls env U (Q :: Γ) (TyCls env U (Q :: Γ) T.lift) a.lift b.lift := by
      rw [he]; exact ElCls.self
    have H := ElCls.collapse henv.ordered (show OnCtx (Q :: Γ) (env.IsType U) from ⟨hΓ, hQ⟩)
      (ha.weakN henv.ordered Ctx.LiftN.one) TyCls.self hm
    exact ElCls.eq_of_defeq TyCls.self (hf hΓ hQ ha hb H)

/-- A small reflecting fragment: the two closed type-former bodies, even when
observed only through constant abstractions over an arbitrary domain Q. -/
def testBody : Bool → VExpr
  | false => bodySort
  | true => bodyPi

theorem reflect_test_lambdas {env : VEnv} (henv : env.WF)
    {U : Nat} {Γ : List VExpr} {Q : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (hQ : env.IsType U Γ Q)
    (i j : Bool) (H : KEq env U Γ (.lam Q (testBody i)) (.lam Q (testBody j))) :
    env.IsDefEq U Γ (testBody i) (testBody j) (.sort (.succ .zero)) := by
  cases i <;> cases j
  · exact bodySort_typed
  · exact (KEq.separates_empty_domain_lambdas henv hΓ hQ H).elim
  · exact (KEq.separates_empty_domain_lambdas henv hΓ hQ H.symm).elim
  · exact bodyPi_typed

/-- A second reflecting fragment: independent variables at Sort 1. -/
theorem reflect_test_variables {env : VEnv} (henv : env.WF)
    (U : Nat) (i j : Fin 2)
    (H : KEq env U [.sort (.succ .zero), .sort (.succ .zero)] (.bvar i) (.bvar j)) :
    env.IsDefEq U [.sort (.succ .zero), .sort (.succ .zero)] (.bvar i) (.bvar j)
      (.sort (.succ .zero)) := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  have hi' : i = 0 ∨ i = 1 := by omega
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
  · exact .bvar .zero
  · exact (KEq.separates_variables henv U H).elim
  · exact (KEq.separates_variables henv U H.symm).elim
  · exact .bvar (.succ .zero)

def propId : VExpr := .forallE (.sort .zero) (.forallE (.bvar 0) (.bvar 1))
def propIdArrow : VExpr := .forallE propId propId.lift

theorem propId_typed {env : VEnv} {U : Nat} (Γ : List VExpr) :
    env.HasType U Γ propId (.sort .zero) := by
  have hinner : env.HasType U (.sort .zero :: Γ) (.forallE (.bvar 0) (.bvar 1))
      (.sort (.imax .zero .zero)) := .forallE (.bvar .zero) (.bvar (.succ .zero))
  have hi : env.HasType U (.sort .zero :: Γ) (.forallE (.bvar 0) (.bvar 1))
      (.sort .zero) := .defeqDF (IsDefEq.sortDF (l := .imax .zero .zero) (l' := .zero)
        ⟨trivial, trivial⟩ trivial rfl) hinner
  exact .defeqDF (IsDefEq.sortDF (l := .imax (.succ .zero) .zero) (l' := .zero)
    ⟨trivial, trivial⟩ trivial rfl) (HasType.forallE (HasType.sort trivial) hi)

theorem propIdArrow_typed {env : VEnv} (henv : env.Ordered) {U : Nat} (Γ : List VExpr) :
    env.HasType U Γ propIdArrow (.sort .zero) := by
  have hp := propId_typed (env := env) (U := U) Γ
  exact .defeqDF (IsDefEq.sortDF (l := .imax .zero .zero) (l' := .zero)
    ⟨trivial, trivial⟩ trivial rfl)
    (HasType.forallE hp (hp.weakN henv Ctx.LiftN.one))

/-- Even all targets and rich valuations do not reflect HETEROGENEOUS proof
equality. The failure is unconditional for every WF environment. -/
theorem heterogeneous_reflection_false {env : VEnv} (henv : env.WF) (U : Nat) :
    ∃ Γ a b P Q, OnCtx Γ (env.IsType U) ∧
      env.HasType U Γ a P ∧ env.HasType U Γ b Q ∧
      KEq env U Γ a b ∧ ¬ env.IsDefEqU U Γ a b := by
  let Γ := [propIdArrow, propId]
  have hΓ : OnCtx Γ (env.IsType U) :=
    ⟨⟨trivial, _, propId_typed []⟩, _, propIdArrow_typed henv.ordered [propId]⟩
  have ha : env.HasType U Γ (.bvar 1) propId := by
    simpa [Γ, propId, propIdArrow, lift, liftN, liftVar] using
      (HasType.bvar (env := env) (U := U) (Lookup.succ (A := propIdArrow)
        (Lookup.zero (Γ := []) (ty := propId))))
  have hb : env.HasType U Γ (.bvar 0) propIdArrow := by
    simpa [Γ, propId, propIdArrow, lift, liftN, liftVar] using
      (HasType.bvar (env := env) (U := U) (Lookup.zero (Γ := [propId]) (ty := propIdArrow)))
  refine ⟨Γ, .bvar 1, .bvar 0, propId, propIdArrow, hΓ, ha, hb,
    KEq.proofs henv hΓ (propId_typed Γ) (propIdArrow_typed henv.ordered Γ) ha hb, ?_⟩
  intro H
  have htypes := (IsDefEqU.of_l henv hΓ H ha).uniqU henv hΓ hb
  obtain ⟨u, hd⟩ := (htypes.forallE_inv henv hΓ).1
  exact IsDefEqU.sort_forallE_inv henv hΓ ⟨_, hd⟩

/-- The exact remaining semantic reflection obligation. Source terms need not
already be typed below; their COMMON larger-context type may use Q. -/
def FreshReflection (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q a b T⦄,
    OnCtx (Q :: Γ) (env.IsType U) →
    env.HasType U (Q :: Γ) a.lift T →
    env.HasType U (Q :: Γ) b.lift T →
    KEq env U (Q :: Γ) a.lift b.lift →
    env.IsDefEqU U Γ a b

theorem cancel_of_freshReflection {env : VEnv} (henv : env.WF)
    (hr : FreshReflection env) : Cancel env := by
  apply cancel_of_front henv
  intro U Γ Q a b hΓ H
  obtain ⟨T, H⟩ := H
  exact hr hΓ H.hasType.1 H.hasType.2 (KEq.sound henv hΓ ⟨T, H⟩)

theorem joinRepair_of_freshReflection {env : VEnv} (henv : env.WF)
    (heq : env.HasCanonicalEq) (hr : FreshReflection env) :
    ∀ U, @JoinRepair (henv.params U) :=
  (cancel_iff_joinRepair henv heq).mp (cancel_of_freshReflection henv hr)

#print axioms joinRepair_of_freshReflection
#print axioms heterogeneous_reflection_false
#print axioms KEq.proofs
#print axioms reflect_test_lambdas
#print axioms reflect_test_variables
#print axioms keyFaithful_iff_typedFront
#print axioms KEq.sound
#print axioms fresh_key
#print axioms KEq.separates_variables
#print axioms type_only_sets_collapse
#print axioms KEq.separates_empty_domain_lambdas
#print axioms cancel_of_freshReflection
end Lean4Lean.StrengtheningKripke

namespace Lean4Lean.StrengtheningOpaque
open VEnv VExpr VEnv.Model StrengtheningKripke

/-- Registration conditions of an opaque constant, excluding constructors and
projection families. No condition on inhabitation or equality is included. -/
structure OpaqueHead (env : VEnv) (c : Name) : Prop where
  rigid : env.Rigid c
  notCtor : ¬ IsCtor env c
  notProjCtor : ¬ IsProjCtor env c
  notFamily : ∀ info, ¬ env.projections c info

theorem rigid_typed_wrap_absurd {env : VEnv} {U : Nat} {Δ : List VExpr}
    {I c : Name} {ls lsI : List VLevel} {args : List VExpr}
    {τs : List Ob} {cv : VExpr → Prop} {keys : List Key} {r : Ob}
    (hI : env.Rigid I)
    (hτ : ∀ τ ∈ τs, Obs env U Δ .id .empty (.mkApps (.const I lsI) args) τ)
    (ht : TypedOb env U Δ cv (wrap keys r) τs)
    (hr : RigidEnd c (ls.map (·.eval)) keys r) : False := by
  cases keys with
  | nil =>
    rcases hr with ⟨s, rfl⟩ | ⟨i, hi, _⟩
    · cases ht with
      | rigid hm => exact rigid_spine_not_pi hI (hτ _ hm) (.inl ⟨_, rfl⟩)
    · simp at hi
  | cons key keys =>
    cases ht with
    | app hm => exact rigid_spine_not_pi hI (hτ _ hm) (.inr (.inl ⟨_, rfl⟩))

theorem opaque_no_observations {env : VEnv} {U : Nat} {Δ : List VExpr}
    {σ : VExpr.Subst} {S : ObSets} {c I : Name} {ls lsI : List VLevel}
    {ci : VConstant} {args : List VExpr}
    (hc : OpaqueHead env c) (hI : env.Rigid I)
    (hci : env.constants c = some ci)
    (hty : ci.type.instL ls = .mkApps (.const I lsI) args)
    {o : Ob} (h : Obs env U Δ σ S (.const c ls) o) : False := by
  cases h with
  | const _ hci' hτ ht hr =>
    have ee := Option.some.inj (hci'.symm.trans hci)
    subst_vars
    exact rigid_typed_wrap_absurd hI (by simpa [hty] using hτ) ht hr
  | delta hdf hlhs =>
    exact hc.rigid _ hdf _ (by rw [hlhs]; rfl)
  | ctor hctor => exact hc.notCtor hctor
  | projCtor hp hn => exact hc.notProjCtor ⟨_, _, hp, hn⟩
  | famTy _ _ hp => exact hc.notFamily _ hp
  | famDom _ _ hp => exact hc.notFamily _ hp
  | rule hdf hlhs =>
    exact hc.rigid _ hdf _ (by rw [hlhs]; exact VExpr.stripLams_wrapLams_mkApps_head)

#print axioms rigid_typed_wrap_absurd
#print axioms opaque_no_observations

/-- The all-target model identifies any two such opaque inhabitants. -/
theorem opaque_KEq {env : VEnv} {U : Nat} {Γ : List VExpr}
    {a b I : Name} {lsA lsB lsI : List VLevel}
    {ciA ciB : VConstant} {args : List VExpr}
    (ha : OpaqueHead env a) (hb : OpaqueHead env b) (hI : env.Rigid I)
    (hca : env.constants a = some ciA) (hcb : env.constants b = some ciB)
    (hA : ciA.type.instL lsA = .mkApps (.const I lsI) args)
    (hB : ciB.type.instL lsB = .mkApps (.const I lsI) args) :
    KEq env U Γ (.const a lsA) (.const b lsB) := by
  intro Δ σ S _ _ _
  constructor
  · intro o ho
    exact False.elim (opaque_no_observations ha hI hca hA ho)
  · intro o ho
    exact False.elim (opaque_no_observations hb hI hcb hB ho)

/-- FreshReflection would force these constants to be definitionally equal,
provided the declaration typings and a well-formed binder are supplied.
This is a consequence, not a proof that the declarations are unequal. -/
theorem freshReflection_collapses_opaque {env : VEnv}
    (hF : FreshReflection env) {U : Nat} {Γ : List VExpr} {Q T : VExpr}
    {a b I : Name} {lsA lsB lsI : List VLevel}
    {ciA ciB : VConstant} {args : List VExpr}
    (ha : OpaqueHead env a) (hb : OpaqueHead env b) (hI : env.Rigid I)
    (hca : env.constants a = some ciA) (hcb : env.constants b = some ciB)
    (hA : ciA.type.instL lsA = .mkApps (.const I lsI) args)
    (hB : ciB.type.instL lsB = .mkApps (.const I lsI) args)
    (hΓ : OnCtx (Q :: Γ) (env.IsType U))
    (hta : env.HasType U (Q :: Γ) (.const a lsA) T)
    (htb : env.HasType U (Q :: Γ) (.const b lsB) T) :
    env.IsDefEqU U Γ (.const a lsA) (.const b lsB) := by
  exact hF hΓ hta htb (opaque_KEq ha hb hI hca hcb hA hB)

#print axioms opaque_KEq
#print axioms freshReflection_collapses_opaque

section
open Params
variable [Params]

def NonFunctionNonProof (Γ : List VExpr) (e : VExpr) : Prop :=
  (∀ A B, ¬ env.HasType univs Γ e (.forallE A B)) ∧
  (∀ P, env.HasType univs Γ P (.sort .zero) → ¬ env.HasType univs Γ e P)

def Stationary (Γ : List VExpr) (e : VExpr) : Prop :=
  ∀ t, FullReduction Γ e t → t = e

theorem normalEq_const_name {Γ : List VExpr} {a b : Name} {lsA lsB : List VLevel}
    (ha : NonFunctionNonProof Γ (.const a lsA))
    (h : NormalEq Γ (.const a lsA) (.const b lsB)) : a = b := by
  obtain ⟨n, hn⟩ := h
  cases hn with
  | refl => rfl
  | constDF => rfl
  | etaBoth ht => exact False.elim (ha.1 _ _ ht)
  | proofIrrel hp ht => exact False.elim (ha.2 _ hp ht)


theorem parRed_const_stable {Γ : List VExpr} {c : Name} {ls : List VLevel}
    (hr : env.Rigid c) {t : VExpr} (h : ParRed Γ (.const c ls) t) :
    t = .const c ls := by
  generalize he : VExpr.const c ls = e at h
  cases h with
  | const => cases he; rfl
  | schema h =>
    have hh := congrArg (fun e : VExpr => e.getAppFnArgs.1) he
    rw [InductiveSignature.CaseSchema.Application.head] at hh
    cases hh
  | extra hp hm =>
    exact False.elim (Params.not_rigid_match (constHeadRigid_iff.mpr hr) hp hm
      (by rw [← he]; rfl))
  | _ => cases he

theorem fullStep_const_stable {Γ : List VExpr} {c : Name} {ls : List VLevel}
    (hr : env.Rigid c) (hreg : recursorData c = none) (hq : c ≠ ``Quot.lift)
    (hf : ∀ A B, ¬ env.HasType univs Γ (.const c ls) (.forallE A B))
    (hs : ∀ family info levels args, env.projections family info →
      ¬ env.HasType univs Γ (.const c ls) (.mkApps (.const family levels) args))
    {t : VExpr} (h : FullStep Γ (.const c ls) t) : t = .const c ls := by
  generalize he : VExpr.const c ls = e at h
  cases h with
  | core h => subst e; exact parRed_const_stable hr h
  | delta h =>
    have hh := congrArg (fun e : VExpr => e.getAppFnArgs.1) he
    rw [InductiveSignature.spine_mkApps_exact _ _ rfl] at hh
    simp only [getAppFnArgs] at hh
    cases hh
    cases h with
    | intro hl => simp [hreg] at hl
  | quotDelta =>
    have hh := congrArg (fun e : VExpr => e.getAppFnArgs.1) he
    rw [InductiveSignature.spine_mkApps_exact _ _ rfl] at hh
    simp only [getAppFnArgs] at hh
    cases hh
    exact False.elim (hq rfl)
  | structEta hp _ _ ht => subst e; exact False.elim (hs _ _ _ _ hp ht)
  | funEta ht => subst e; exact False.elim (hf _ _ ht)
  | _ => cases he

theorem stationary_of_step_stable {Γ : List VExpr} {e : VExpr}
    (hs : ∀ t, FullStep Γ e t → t = e) : Stationary Γ e := by
  intro t h
  induction h with
  | rfl => rfl
  | tail h hstep ih => subst_vars; exact hs _ hstep

end

/-- Confluence separates distinct stationary opaque inhabitants when they are
neither functions nor proofs. The hypotheses concern typing and reduction,
not the definitional inequality being concluded. -/
theorem stationary_constants_not_defeq {env : VEnv} (henv : env.WF)
    (heq : env.HasCanonicalEq) {U : Nat} {Γ : List VExpr}
    {a b : Name} {lsA lsB : List VLevel}
    (hΓ : OnCtx Γ (env.IsType U)) (hne : a ≠ b)
    (ha : @NonFunctionNonProof (henv.params U) Γ (.const a lsA))
    (hsa : @Stationary (henv.params U) Γ (.const a lsA))
    (hsb : @Stationary (henv.params U) Γ (.const b lsB)) :
    ¬ env.IsDefEqU U Γ (.const a lsA) (.const b lsB) := by
  intro ⟨T, H⟩
  letI := henv.params U
  obtain ⟨x, y, hx, hy, hn⟩ := henv.church_rosser heq hΓ H
  cases hsa x hx
  cases hsb y hy
  exact hne (normalEq_const_name ha hn)

#print axioms normalEq_const_name
#print axioms stationary_constants_not_defeq
theorem opaque_type_exclusions {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (hr : env.Rigid I) (hn : ∀ info, ¬ env.projections I info)
    (hI : env.HasType U Γ (.const I lsI) (.sort (.succ .zero)))
    (he : env.HasType U Γ e (.const I lsI)) :
    (∀ A B, ¬ env.HasType U Γ e (.forallE A B)) ∧
    (∀ P, env.HasType U Γ P (.sort .zero) → ¬ env.HasType U Γ e P) ∧
    (∀ family info levels args, env.projections family info →
      ¬ env.HasType U Γ e (.mkApps (.const family levels) args)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B hf
    exact IsDefEqU.rigidApp_forallE_inv (args := []) henv hΓ hr hI (he.uniqU henv hΓ hf)
  · intro P hP hp
    have hIP := (he.uniqU henv hΓ hp).of_r henv hΓ hP
    have hl := (hI.uniqU henv hΓ hIP.hasType.1).sort_inv henv hΓ
    have hz := congrFun hl []
    simp [VLevel.eval] at hz
  · intro family info levels args hf hs
    have hne : I ≠ family := by intro hh; subst family; exact hn info hf
    exact IsDefEqU.rigidApp_ne (args := []) henv hΓ hr (henv.projectionRigid hf)
      hne hI (he.uniqU henv hΓ hs)




theorem opaque_stationary {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {c I : Name} {ls lsI : List VLevel}
    (hc : env.Rigid c) (hq : c ≠ ``Quot.lift)
    (hI : env.Rigid I) (hn : ∀ info, ¬ env.projections I info)
    (htI : env.HasType U Γ (.const I lsI) (.sort (.succ .zero)))
    (htc : env.HasType U Γ (.const c ls) (.const I lsI)) :
    @Stationary (henv.params U) Γ (.const c ls) := by
  letI := henv.params U
  obtain ⟨hf, _, hs⟩ := opaque_type_exclusions henv hΓ hI hn htI htc
  apply stationary_of_step_stable
  intro t ht
  exact fullStep_const_stable hc (henv.registry_contract.rigid c hc).recursor hq hf hs ht

theorem opaque_constants_not_defeq {env : VEnv} (henv : env.WF)
    (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType U))
    {a b I : Name} {lsA lsB lsI : List VLevel}
    (ha : env.Rigid a) (hb : env.Rigid b) (hI : env.Rigid I)
    (hn : ∀ info, ¬ env.projections I info)
    (hne : a ≠ b) (haq : a ≠ ``Quot.lift) (hbq : b ≠ ``Quot.lift)
    (htI : env.HasType U Γ (.const I lsI) (.sort (.succ .zero)))
    (hta : env.HasType U Γ (.const a lsA) (.const I lsI))
    (htb : env.HasType U Γ (.const b lsB) (.const I lsI)) :
    ¬ env.IsDefEqU U Γ (.const a lsA) (.const b lsB) := by
  obtain ⟨hf, hp, _⟩ := opaque_type_exclusions henv hΓ hI hn htI hta
  exact stationary_constants_not_defeq henv heq hΓ hne ⟨hf, hp⟩
    (opaque_stationary henv hΓ ha haq hI hn htI hta)
    (opaque_stationary henv hΓ hb hbq hI hn htI htb)

/-- A concrete declaration-pattern obstruction: every environment with these
ordinary opaque declarations refutes FreshReflection. No definitional inequality
or reflection failure occurs among the hypotheses. -/
theorem opaque_not_freshReflection {env : VEnv} (henv : env.WF)
    (heq : env.HasCanonicalEq) {U : Nat} {a b I : Name}
    {ciA ciB : VConstant}
    (ha : OpaqueHead env a) (hb : OpaqueHead env b) (hI : env.Rigid I)
    (hn : ∀ info, ¬ env.projections I info)
    (hne : a ≠ b) (haq : a ≠ ``Quot.lift) (hbq : b ≠ ``Quot.lift)
    (hca : env.constants a = some ciA) (hcb : env.constants b = some ciB)
    (hA : ciA.type.instL [] = .const I [])
    (hB : ciB.type.instL [] = .const I [])
    (htI : env.HasType U [] (.const I []) (.sort (.succ .zero)))
    (hta : env.HasType U [] (.const a []) (.const I []))
    (htb : env.HasType U [] (.const b []) (.const I [])) :
    ¬ FreshReflection env := by
  intro hF
  have he := freshReflection_collapses_opaque hF ha hb hI hca hcb
    (args := []) hA hB (Q := .sort .zero) (Γ := [])
    ⟨trivial, _, .sort trivial⟩
    (hta.weakN henv.ordered Ctx.LiftN.one)
    (htb.weakN henv.ordered Ctx.LiftN.one)
  exact opaque_constants_not_defeq (Γ := []) henv heq trivial ha.rigid hb.rigid hI hn
    hne haq hbq htI hta htb he

#print axioms parRed_const_stable
#print axioms fullStep_const_stable
#print axioms stationary_of_step_stable
#print axioms opaque_type_exclusions
#print axioms opaque_stationary
#print axioms opaque_constants_not_defeq
#print axioms opaque_not_freshReflection
end Lean4Lean.StrengtheningOpaque




namespace Lean4Lean.StrengtheningOpaqueExtension
open VEnv VExpr VEnv.Model StrengtheningOpaque

def addAxiom (env : VEnv) (c : Name) (T : VExpr) : VEnv :=
  { env with constants := fun n => if c = n then some ⟨0, T⟩ else env.constants n }

theorem addAxiom_installed (fresh : env.constants c = none) :
    env.addConst c ⟨0, T⟩ = some (addAxiom env c T) := by
  simp [VEnv.addConst, fresh, addAxiom]

theorem addAxiom_wf (henv : env.WF) (fresh : env.constants c = none)
    (ht : env.IsType 0 [] T) : (addAxiom env c T).WF := by
  obtain ⟨ds, hds⟩ := henv
  exact ⟨.axiom ⟨⟨0, T⟩, c⟩ :: ds,
    .decl (.axiom ht (addAxiom_installed fresh)) hds⟩

def extension (env : VEnv) (I a b : Name) : VEnv :=
  addAxiom (addAxiom (addAxiom env I (.sort (.succ .zero))) a (.const I []))
    b (.const I [])

/-- Names are absent from the base constant table and pairwise distinct.
The semantic metadata tables are never changed by this construction. -/
structure FreshNames (env : VEnv) (I a b : Name) : Prop where
  freshI : env.constants I = none
  freshA : env.constants a = none
  freshB : env.constants b = none
  IA : I ≠ a
  IB : I ≠ b
  AB : a ≠ b

theorem extension_properties (henv : env.WF) (heq : env.HasCanonicalEq)
    (hf : FreshNames env I a b) :
    (extension env I a b).WF ∧
    (extension env I a b).HasCanonicalEq ∧
    (extension env I a b).constants I = some ⟨0, .sort (.succ .zero)⟩ ∧
    (extension env I a b).constants a = some ⟨0, .const I []⟩ ∧
    (extension env I a b).constants b = some ⟨0, .const I []⟩ := by
  have freshA : (addAxiom env I (.sort (.succ .zero))).constants a = none := by
    simp [addAxiom, hf.IA, hf.freshA]
  have freshB : (addAxiom (addAxiom env I (.sort (.succ .zero))) a (.const I [])).constants b = none := by
    simp [addAxiom, hf.AB, hf.IB, hf.freshB]
  have h1 := addAxiom_installed (T := .sort (.succ .zero)) hf.freshI
  have h2 := addAxiom_installed (T := .const I []) freshA
  have h3 := addAxiom_installed (T := .const I []) freshB
  have hw1 := addAxiom_wf henv hf.freshI (T := .sort (.succ .zero)) ⟨_, HasType.sort (by trivial)⟩
  have hI : (addAxiom env I (.sort (.succ .zero))).HasType 0 []
      (.const I []) (.sort (.succ .zero)) := by
    simpa [instL, VLevel.inst] using HasType.const (U := 0) (Γ := []) (ls := [])
      (VEnv.addConst_self h1) (by simp) rfl
  have hw2 := addAxiom_wf hw1 freshA ⟨_, hI⟩
  have hI2 := hI.mono (VEnv.addConst_le h2)
  refine ⟨addAxiom_wf hw2 freshB ⟨_, hI2⟩,
    heq.mono ((VEnv.addConst_le h1).trans ((VEnv.addConst_le h2).trans (VEnv.addConst_le h3))), ?_⟩
  simp [extension, addAxiom, Ne.symm hf.IA, Ne.symm hf.IB, Ne.symm hf.AB]

theorem extension_opaque (h : OpaqueHead env c) :
    OpaqueHead (extension env I a b) c :=
  ⟨h.rigid, h.notCtor, h.notProjCtor, h.notFamily⟩

theorem extension_rigid (h : env.Rigid c) :
    (extension env I a b).Rigid c := h


theorem opaque_of_absent (henv : env.WF) (fresh : env.constants c = none) :
    OpaqueHead env c := by
  refine ⟨henv.ordered.rigid_of_absent fresh, ?_, ?_, ?_⟩
  · intro hc
    obtain ⟨ci, hi⟩ := henv.isCtor_const hc
    rw [fresh] at hi
    contradiction
  · rintro ⟨fam, info, hp, rfl⟩
    have hi := henv.ordered.projectionConstructor hp
    rw [fresh] at hi
    contradiction
  · intro info hp
    obtain ⟨decl, type, ctor, _, _, _, _, _, _, _, _, _, _, hi, _⟩ :=
      henv.ordered.projectionShape hp
    rw [fresh] at hi
    contradiction

/-- Ordinary fresh axiom declarations realize the opaque-head hypotheses;
no equality or reduction assertion is assumed. -/
theorem extension_opaque_heads (henv : env.WF) (hf : FreshNames env I a b) :
    OpaqueHead (extension env I a b) I ∧
    OpaqueHead (extension env I a b) a ∧
    OpaqueHead (extension env I a b) b :=
  ⟨extension_opaque (opaque_of_absent henv hf.freshI),
   extension_opaque (opaque_of_absent henv hf.freshA),
   extension_opaque (opaque_of_absent henv hf.freshB)⟩


theorem extension_not_freshReflection (henv : env.WF) (heq : env.HasCanonicalEq)
    (hf : FreshNames env I a b) (haq : a ≠ ``Quot.lift) (hbq : b ≠ ``Quot.lift) :
    ¬ StrengtheningKripke.FreshReflection (extension env I a b) := by
  obtain ⟨hw, he, hI, ha, hb⟩ := extension_properties henv heq hf
  obtain ⟨hOI, hOA, hOB⟩ := extension_opaque_heads henv hf
  apply opaque_not_freshReflection (U := 0) hw he hOA hOB hOI.rigid hOI.notFamily
    hf.AB haq hbq ha hb rfl rfl
  · simpa [instL, VLevel.inst] using
      HasType.const (U := 0) (Γ := []) (ls := []) hI (by simp) rfl
  · simpa [instL] using HasType.const (U := 0) (Γ := []) (ls := []) ha (by simp) rfl
  · simpa [instL] using HasType.const (U := 0) (Γ := []) (ls := []) hb (by simp) rfl

#print axioms extension_not_freshReflection

#print axioms opaque_of_absent
#print axioms extension_opaque_heads

#print axioms addAxiom_installed
#print axioms addAxiom_wf
#print axioms extension_properties
#print axioms extension_opaque
#print axioms extension_rigid
end Lean4Lean.StrengtheningOpaqueExtension
