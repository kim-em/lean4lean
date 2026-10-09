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


/-! A fully counted nondependent Pi fragment used to test the proposed
size-first rank. This is NOT a complete certified equality calculus. -/
namespace Lean4Lean.StrengtheningRank
open VEnv VExpr

def S1 : VExpr := .sort (.succ .zero)
def arr (a b : VExpr) : VExpr := .forallE a b.lift

/-- No declarative typing/equality premises or conversion escape hatch.
The sort equivalence imax 1 1 = 1 is built into the pi rule. -/
inductive Cert : Nat → List VExpr → VExpr → VExpr → Prop where
  | var : Lookup Γ i S1 → Cert 1 Γ (.bvar i) S1
  | prop : Cert 1 Γ (.sort .zero) S1
  | pi : Cert n Γ a S1 → Cert m Γ b S1 → Cert (n + m + 1) Γ (arr a b) S1

/-- Certified reflexivity and beta for this fragment; every typing premise
is a Cert. This deliberately omits the full calculus's conversion and rules. -/
inductive CertEq : Nat → List VExpr → VExpr → VExpr → VExpr → Prop where
  | refl : Cert n Γ e A → CertEq (n+1) Γ e e A
  | beta : Cert n (S1 :: Γ) b S1 → Cert m Γ a S1 →
      CertEq (n+m+1) Γ (.app (.lam S1 b) a) (b.inst a) S1

def nodes : VExpr → Nat
  | .app a b | .lam a b | .forallE a b => nodes a + nodes b + 1
  | .proj _ _ e => nodes e + 1
  | _ => 1

theorem nodes_lift (e : VExpr) (n k : Nat) : nodes (e.liftN n k) = nodes e := by
  induction e generalizing k <;> simp [VExpr.liftN, nodes, *]

theorem Cert.exact_size (h : Cert n Γ e A) : nodes e = n := by
  induction h with
  | var => rfl
  | prop => rfl
  | pi _ _ ha hb => simp [arr, nodes, lift, nodes_lift, ha, hb]

theorem Cert.positive (h : Cert n Γ e A) : 0 < n := by
  cases h <;> omega

theorem Cert.sound {env : VEnv} (henv : env.Ordered) (h : Cert n Γ e A) :
    env.HasType U Γ e A := by
  induction h with
  | var h => exact .bvar h
  | prop => exact .sort trivial
  | pi _ _ ha hb =>
    have ht := HasType.forallE ha (hb.weakN henv (Ctx.LiftN.one (A := _)))
    exact .defeqDF (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero))
      (l' := .succ .zero) ⟨trivial, trivial⟩ trivial rfl) ht

theorem CertEq.sound {env : VEnv} (henv : env.Ordered) (h : CertEq n Γ a b A) :
    env.IsDefEq U Γ a b A := by
  cases h with
  | refl h => exact h.sound henv
  | beta hb ha => exact .beta (hb.sound henv) (ha.sound henv)

theorem arr_subst (a b : VExpr) (σ : VExpr.Subst) :
    (arr a b).subst σ = arr (a.subst σ) (b.subst σ) := by
  simp only [arr, VExpr.subst, VExpr.lift_subst_lift]

theorem arr_lift (a b : VExpr) (n k : Nat) :
    (arr a b).liftN n k = arr (a.liftN n k) (b.liftN n k) := by
  simp only [arr, VExpr.liftN]
  rw [VExpr.lift_liftN']

theorem Cert.weakN (W : Ctx.LiftN p k Γ Δ) (h : Cert n Γ e A) :
    Cert n Δ (e.liftN p k) (A.liftN p k) := by
  induction h with
  | var h => exact .var (h.weakN W)
  | prop => exact .prop
  | pi _ _ ha hb => rw [arr_lift]; exact .pi (ha W) (hb W)

/-- The substitution budget includes every possible substituted variable
certificate. The output bound is n*M, not a bound depending only on n. -/
def SubBudget (M : Nat) (Γ Δ : List VExpr) (σ : VExpr.Subst) : Prop :=
  ∀ i, Lookup Γ i S1 → ∃ m, m ≤ M ∧ Cert m Δ (σ i) S1

theorem Cert.subst (h : Cert n Γ e S1) (hM : 1 ≤ M)
    (hσ : SubBudget M Γ Δ σ) :
    ∃ r, r ≤ n * M ∧ Cert r Δ (e.subst σ) S1 := by
  generalize hA : S1 = A at h
  induction h with
  | var h => simpa using hσ _ h
  | prop => exact ⟨1, by simpa using hM, .prop⟩
  | @pi n Γ a m b ha hb iha ihb =>
    obtain ⟨r, hr, ha'⟩ := iha hσ rfl
    obtain ⟨s, hs, hb'⟩ := ihb hσ rfl
    refine ⟨r + s + 1, ?_, ?_⟩
    · calc
        r + s + 1 ≤ n * M + m * M + M := Nat.add_le_add (Nat.add_le_add hr hs) hM
        _ = (n + m + 1) * M := by simp [Nat.add_mul]
    · rw [arr_subst]; exact .pi ha' hb'

def tower : Nat → VExpr
  | 0 => .sort .zero
  | n + 1 => arr (.sort .zero) (tower n)

theorem tower_cert (n : Nat) (Γ : List VExpr) : Cert (2*n+1) Γ (tower n) S1 := by
  induction n with
  | zero => exact .prop
  | succ n ih =>
    have hn : 2*(n+1)+1 = 1+(2*n+1)+1 := by omega
    rw [hn]; exact .pi .prop ih

def twice : VExpr := arr (.bvar 0) (.bvar 0)

theorem twice_cert : Cert 3 [S1] twice S1 := .pi (.var .zero) (.var .zero)

theorem twice_subst (q : VExpr) : twice.subst (Subst.id.cons q) = arr q q := rfl

theorem duplication_exact (N : Nat) :
    Cert (4*N+3) [] (twice.subst (Subst.id.cons (tower N))) S1 ∧
    ∀ r, Cert r [] (twice.subst (Subst.id.cons (tower N))) S1 → r = 4*N+3 := by
  have h : Cert (4*N+3) [] (arr (tower N) (tower N)) S1 := by
    have hn : 4*N+3 = (2*N+1)+(2*N+1)+1 := by omega
    rw [hn]; exact .pi (tower_cert N []) (tower_cert N [])
  constructor
  · exact h
  · intro r hr
    exact hr.exact_size.symm.trans h.exact_size

/-- Principal substitution can exceed source + argument + ANY FIXED overhead.
This rules out a decrease on that size component, regardless of the secondary
component. It does not rule out a cut-rank-first or ordinal termination proof. -/
theorem no_additive_size_decrease (C : Nat) :
    ∃ n m r q,
      Cert n [S1] twice S1 ∧ Cert m [] q S1 ∧
      Cert r [] (twice.subst (Subst.id.cons q)) S1 ∧
      n + m + C < r ∧
      ∀ s, Cert s [] (twice.subst (Subst.id.cons q)) S1 → s = r := by
  refine ⟨3, 2*(C+2)+1, 4*(C+2)+3, tower (C+2), twice_cert,
    tower_cert _ [], (duplication_exact _).1, ?_, (duplication_exact _).2⟩
  omega

/-- The duplication is the contractum of an actual certified beta rule. -/
theorem beta_duplication (N : Nat) :
    CertEq (2*N+5) [] (.app (.lam S1 twice) (tower N))
      (twice.inst (tower N)) S1 := by
  have hn : 2*N+5 = 3+(2*N+1)+1 := by omega
  rw [hn]; exact .beta twice_cert (tower_cert N [])

theorem beta_contractum_size (N r : Nat)
    (h : Cert r [] (twice.inst (tower N)) S1) : r = 4*N+3 := by
  rw [VExpr.inst_eq] at h
  exact (duplication_exact N).2 r h

theorem beta_size_increases (N r : Nat) (hN : 2 ≤ N)
    (h : Cert r [] (twice.inst (tower N)) S1) : 2*N+5 < r := by
  have := beta_contractum_size N r h
  omega

theorem no_size_first_lex_decrease (C x y : Nat) :
    ¬ Prod.Lex (· < ·) (· < ·)
      (4*(C+2)+3, x) (3 + (2*(C+2)+1) + C, y) := by
  generalize hn : 4*(C+2)+3 = n
  generalize hm : 3 + (2*(C+2)+1) + C = m
  intro h
  cases h <;> omega

#print axioms beta_contractum_size
#print axioms beta_size_increases
#print axioms CertEq.sound
#print axioms beta_duplication
#print axioms Cert.sound
#print axioms Cert.weakN
#print axioms Cert.subst
#print axioms duplication_exact
#print axioms no_additive_size_decrease
#print axioms no_size_first_lex_decrease
end Lean4Lean.StrengtheningRank

namespace Lean4Lean.StrengtheningRound4
open VEnv VExpr VEnv.Model StrengtheningPartial StrengtheningContinuation
open StrengtheningKripke StrengtheningRank

/-- The semantic domain comparison is genuinely recursive, without class reflection. -/
theorem KEq_pi_domain (H : KEq env U Γ (.forallE A B) (.forallE A' B')) :
    KEq env U Γ A A' := by
  have one {A B A' B' : VExpr} {Δ σ S}
      (h : Ob.Sub (Obs env U Δ σ S (.forallE A B))
        (Obs env U Δ σ S (.forallE A' B'))) :
      Ob.Sub (Obs env U Δ σ S A) (Obs env U Δ σ S A') := by
    intro o ho
    obtain ⟨p, hp, hl⟩ := h _ (.piDomOb ho)
    obtain ⟨q, rfl, hq⟩ := hl.piDomOb_inv
    cases hp with
    | piDomOb hp => exact ⟨q, hp, hq⟩
  intro Δ σ S hΔ hσ hS
  have h := H Δ σ S hΔ hσ hS
  exact ⟨one h.1, one h.2⟩

theorem fresh_sort_reflection {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx (Q :: Γ) (env.IsType U))
    (ha : env.HasType U (Q :: Γ) (.sort u) T)
    (hb : env.HasType U (Q :: Γ) (.sort v) T)
    (H : KEq env U (Q :: Γ) (.sort u) (.sort v)) :
    env.IsDefEqU U Γ (.sort u) (.sort v) := by
  obtain ⟨o, ho, hl⟩ := (H (Q :: Γ) .id .empty hΓ
    (Ctx.SubstEq.id henv.ordered hΓ) TV.empty).1 _ .sort
  have he : u.eval = v.eval := by
    rw [hl.sort_inv] at ho
    exact Ob.sort.inj (Obs.sort_iff.mp ho)
  exact ⟨_, .sortDF (ha.sort_inv henv.ordered) (hb.sort_inv henv.ordered) he⟩

/-- Proof irrelevance closes this head case only once the typings exist below. -/
theorem common_proofs_below {env : VEnv} (hP : env.HasType U Γ P (.sort .zero))
    (ha : env.HasType U Γ a P) (hb : env.HasType U Γ b P) :
    env.IsDefEqU U Γ a b := ⟨_, .proofIrrel hP ha hb⟩

section
variable [Params]
open Params

/-- Ignore reflexive steps: FullStep itself contains reflexivity. -/
def Terminal (Γ : List VExpr) (e : VExpr) : Prop :=
  ∀ t, FullStep Γ e t → t = e

theorem function_has_strict_eta (he : env.HasType univs Γ e (.forallE A B)) :
    ∃ t, FullStep Γ e t ∧ nodes e < nodes t := by
  refine ⟨.lam A (.app e.lift (.bvar 0)), .funEta he, ?_⟩
  simp only [nodes, lift, nodes_lift]
  omega

theorem function_no_terminal_reduct (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e (.forallE A B)) :
    ¬ ∃ t, FullReduction Γ e t ∧ Terminal Γ t := by
  rintro ⟨t, hr, ht⟩
  obtain ⟨s, hs, hn⟩ := function_has_strict_eta (hr.hasType hΓ he)
  have := ht s hs
  subst s
  omega

theorem normalEq_is_not_terminality (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e (.forallE A B)) :
    NormalEq Γ e e ∧ ¬ ∃ t, FullReduction Γ e t ∧ Terminal Γ t :=
  ⟨NormalEqN.normalEq (.refl he), function_no_terminal_reduct hΓ he⟩

/-- Even the literal endpoint-support property fails for a NormalEq join. -/
theorem confluence_join_can_be_unsupported :
    ∃ x y, FullReduction [.sort .zero] idProp.lift x ∧
      FullReduction [.sort .zero] idProp.lift y ∧
      NormalEq [.sort .zero] x y ∧ ¬ x.Skips 1 0 := by
  obtain ⟨x, hs, hx⟩ := eta_does_not_preserve_support
  have hΓ : OnCtx [.sort .zero] (env.IsType univs) := ⟨trivial, _, .sort trivial⟩
  have hi : env.HasType univs [] idProp (.forallE (.sort .zero) (.sort .zero)) :=
    .lam (.sort trivial) (.bvar .zero)
  have hi' := hi.weakN henv.ordered (Ctx.LiftN.one (A := .sort .zero))
  exact ⟨x, x, .tail .rfl hs, .tail .rfl hs,
    NormalEqN.normalEq (.refl (hs.hasType hΓ hi')), hx⟩
end

/-- A semantic input requires a supported join, not just installed-equation coverage. -/
def SemanticJoinRepair (env : VEnv) (henv : env.WF) : Prop :=
  ∀ ⦃U Γ Q a b T⦄,
    OnCtx (Q :: Γ) (env.IsType U) →
    env.HasType U (Q :: Γ) a.lift T →
    env.HasType U (Q :: Γ) b.lift T →
    KEq env U (Q :: Γ) a.lift b.lift →
    @TypedJoin (henv.params U) Γ a b

theorem freshReflection_iff_semanticJoinRepair {env : VEnv} (henv : env.WF)
    (heq : env.HasCanonicalEq) :
    FreshReflection env ↔ SemanticJoinRepair env henv := by
  constructor
  · intro h U Γ Q a b T hΓ ha hb hK
    obtain ⟨A, H⟩ := h hΓ ha hb hK
    obtain ⟨x, y, hx, hy, hn⟩ := henv.church_rosser heq hΓ.1 H
    exact ⟨A, A, x, y, H.hasType.1, H.hasType.2, hx, hy, hn⟩
  · intro h U Γ Q a b T hΓ ha hb hK
    letI := henv.params U
    exact TypedJoin.defeq hΓ.1 (h hΓ ha hb hK)

#print axioms KEq_pi_domain
#print axioms fresh_sort_reflection
#print axioms common_proofs_below
#print axioms function_has_strict_eta
#print axioms function_no_terminal_reduct
#print axioms normalEq_is_not_terminality
#print axioms confluence_join_can_be_unsupported
#print axioms freshReflection_iff_semanticJoinRepair
end Lean4Lean.StrengtheningRound4

namespace Lean4Lean.StrengtheningRound4
open VEnv VExpr StrengtheningRank

/-- A pair (c,n) represents omega*c+n. Lexicographic order compares c first. -/
abbrev CutRank := Nat × Nat
def RankLT : CutRank → CutRank → Prop := Prod.Lex (· < ·) (· < ·)
def RankLE (r s : CutRank) : Prop := r.1 ≤ s.1 ∧ r.2 ≤ s.2

/-- Fully certified S1 terms, including nested beta sources. The first index
counts beta crossings outside binders. Pi codomains and beta bodies are under
binders, so their crossings do not contribute to that first index. The second
index counts ALL certificate nodes, including both of these premises. -/
inductive CutCert : Nat → Nat → List VExpr → VExpr → Prop where
  | var : Lookup Γ i S1 → CutCert 0 1 Γ (.bvar i)
  | prop : CutCert 0 1 Γ (.sort .zero)
  | pi : CutCert c n Γ a → CutCert d m Γ b →
      CutCert c (n+m+1) Γ (arr a b)
  | beta : CutCert d n (S1 :: Γ) b → CutCert c m Γ a →
      CutCert (c+1) (n+m+1) Γ (.app (.lam S1 b) a)

def CutSubBudget (K M : Nat) (Γ Δ : List VExpr) (σ : VExpr.Subst) : Prop :=
  ∀ i, Lookup Γ i S1 → ∃ c n, RankLE (c,n) (K,M) ∧ CutCert c n Δ (σ i)

theorem CutCert.sound {env : VEnv} (henv : env.Ordered) (h : CutCert c n Γ e) :
    env.HasType U Γ e S1 := by
  induction h with
  | var h => exact .bvar h
  | prop => exact .sort trivial
  | pi _ _ ha hb =>
    have ht := HasType.forallE ha (hb.weakN henv (Ctx.LiftN.one (A := _)))
    exact .defeqDF (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero))
      (l' := .succ .zero) ⟨trivial, trivial⟩ trivial rfl) ht
  | beta _ _ hb ha => exact (IsDefEq.beta hb ha).hasType.1

theorem Cert.toCutCert (h : Cert n Γ e S1) : CutCert 0 n Γ e := by
  generalize hA : S1 = A at h
  induction h with
  | var h => exact .var h
  | prop => exact .prop
  | pi _ _ ha hb => exact .pi (ha rfl) (hb rfl)

theorem CutCert.weakN (h : CutCert c n Γ e) (W : Ctx.LiftN p k Γ Δ) :
    CutCert c n Δ (e.liftN p k) := by
  induction h generalizing k Δ with
  | var h => exact .var (h.weakN W)
  | prop => exact .prop
  | pi _ _ ha hb => rw [arr_lift]; exact .pi (ha W) (hb W)
  | beta _ _ hb ha => exact .beta (hb W.succ) (ha W)

theorem CutSubBudget.lift (h : CutSubBudget K M Γ Δ σ) (hM : 1 ≤ M) :
    CutSubBudget K M (S1 :: Γ) (S1 :: Δ) σ.lift := by
  intro i hi
  cases i with
  | zero => exact ⟨0, 1, ⟨Nat.zero_le _, hM⟩, .var .zero⟩
  | succ i =>
    have hi' : Lookup Γ i S1 := (Lookup.weakN_iff (Ctx.LiftN.one (A := S1))).mp (by simpa [S1, liftVar, liftN, Nat.add_comm] using hi)
    obtain ⟨c, n, hn, hc⟩ := h _ hi'
    exact ⟨c, n, hn, hc.weakN (Ctx.LiftN.one (A := S1))⟩

/-- Both components have substitution-aware bounds, even with nested cuts.
This is a growth bound, not a principal-contraction decrease theorem. -/
theorem CutCert.subst (h : CutCert c n Γ e) (hM : 1 ≤ M)
    (hσ : CutSubBudget K M Γ Δ σ) :
    ∃ d r, RankLE (d,r) (c+n*K,n*M) ∧ CutCert d r Δ (e.subst σ) := by
  induction h generalizing Δ σ with
  | var hi =>
    obtain ⟨d, r, hr, hc⟩ := hσ _ hi
    exact ⟨d, r, by simpa [RankLE] using hr, hc⟩
  | prop => exact ⟨0, 1, ⟨by simp, by simpa using hM⟩, .prop⟩
  | @pi c n Γ a d m b ha hb iha ihb =>
    obtain ⟨c', n', hn, ha'⟩ := iha hσ
    obtain ⟨d', m', hm, hb'⟩ := ihb hσ
    refine ⟨c', n'+m'+1, ⟨?_, ?_⟩, ?_⟩
    · dsimp [RankLE] at hn hm ⊢
      have : n*K ≤ (n+m+1)*K := Nat.mul_le_mul_right K (by omega)
      omega
    · calc
        n'+m'+1 ≤ n*M+m*M+M := Nat.add_le_add (Nat.add_le_add hn.2 hm.2) hM
        _ = (n+m+1)*M := by simp [Nat.add_mul]
    · rw [arr_subst]; exact .pi ha' hb'
  | @beta d n Γ b c m a hb ha ihb iha =>
    obtain ⟨d', n', hn, hb'⟩ := ihb (hσ.lift hM)
    obtain ⟨c', m', hm, ha'⟩ := iha hσ
    refine ⟨c'+1, n'+m'+1, ⟨?_, ?_⟩, .beta hb' ha'⟩
    · dsimp [RankLE] at hn hm ⊢
      have : m*K ≤ (n+m+1)*K := Nat.mul_le_mul_right K (by omega)
      omega
    · calc
        n'+m'+1 ≤ n*M+m*M+M := Nat.add_le_add (Nat.add_le_add hn.2 hm.2) hM
        _ = (n+m+1)*M := by simp [Nat.add_mul]

/-- The requested old-fragment substitution theorem in the new rank. -/
theorem Cert.subst_rank (h : Cert n Γ e S1) (hM : 1 ≤ M)
    (hσ : SubBudget M Γ Δ σ) :
    ∃ r, RankLE (0,r) (0,n*M) ∧ Cert r Δ (e.subst σ) S1 := by
  obtain ⟨r, hr, hc⟩ := h.subst hM hσ
  exact ⟨r, ⟨Nat.le_refl _, hr⟩, hc⟩

theorem tower_cutcert (N : Nat) (Γ : List VExpr) :
    CutCert 0 (2*N+1) Γ (tower N) := Cert.toCutCert (tower_cert N Γ)

theorem twice_cutcert : CutCert 0 3 [S1] twice := Cert.toCutCert twice_cert

theorem duplication_cut_rank_decreases (N : Nat) :
    CutCert 1 (2*N+5) [] (.app (.lam S1 twice) (tower N)) ∧
    CutCert 0 (4*N+3) [] (twice.inst (tower N)) ∧
    RankLT (0,4*N+3) (1,2*N+5) := by
  constructor
  · have h := CutCert.beta twice_cutcert (tower_cutcert N [])
    have he : 3+(2*N+1)+1 = 2*N+5 := by omega
    simpa only [he] using h
  constructor
  · simpa [VExpr.inst_eq] using Cert.toCutCert (duplication_exact N).1
  · exact Prod.Lex.left _ _ (by omega)

/-- Arbitrarily many crossings can be hidden in a beta body. -/
def nested : Nat → VExpr
  | 0 => .sort .zero
  | n+1 => .app (.lam S1 (.bvar 0)) (nested n)

theorem nested_cert (N : Nat) (Γ : List VExpr) :
    CutCert N (2*N+1) Γ (nested N) := by
  induction N with
  | zero => exact .prop
  | succ N ih =>
    have h := CutCert.beta (CutCert.var (Γ := S1 :: Γ) Lookup.zero) ih
    have he : 1+(2*N+1)+1 = 2*(N+1)+1 := by omega
    simpa only [he, nested] using h

theorem hidden_crossings_exposed (N : Nat) :
    CutCert 1 (2*N+3) [] (.app (.lam S1 (nested N).lift) (.sort .zero)) ∧
    (nested N).lift.inst (.sort .zero) = nested N ∧
    CutCert N (2*N+1) [] (nested N) := by
  refine ⟨?_, VExpr.inst_lift .., nested_cert N []⟩
  have h := CutCert.beta ((nested_cert N []).weakN (Ctx.LiftN.one (A := S1))) CutCert.prop
  have he : 2*N+1+1+1 = 2*N+3 := by omega
  simpa only [he] using h

/-- Failure is in the FIRST rank component, regardless of size savings. -/
theorem hidden_crossings_rank_increases (N : Nat) (hN : 2 ≤ N) :
    RankLT (1,2*N+3) (N,2*N+1) ∧
    ¬ RankLT (N,2*N+1) (1,2*N+3) := by
  constructor
  · exact Prod.Lex.left _ _ (by omega)
  · intro h; cases h <;> omega

/-- The exposed contractum is actual object-language beta equality. -/
theorem hidden_crossings_beta {env : VEnv} (henv : env.Ordered) (N : Nat) :
    env.IsDefEq U [] (.app (.lam S1 (nested N).lift) (.sort .zero)) (nested N) S1 := by
  have hb := ((nested_cert N []).weakN (Ctx.LiftN.one (A := S1))).sound (U := U) henv
  have h := IsDefEq.beta hb (show env.HasType U [] (.sort .zero) S1 from .sort trivial)
  simpa only [VExpr.inst_lift, S1, VExpr.inst] using h

#print axioms CutCert.sound
#print axioms Cert.toCutCert
#print axioms CutCert.weakN
#print axioms CutSubBudget.lift
#print axioms CutCert.subst
#print axioms Cert.subst_rank
#print axioms tower_cutcert
#print axioms twice_cutcert
#print axioms duplication_cut_rank_decreases
#print axioms nested_cert
#print axioms hidden_crossings_exposed
#print axioms hidden_crossings_rank_increases
#print axioms hidden_crossings_beta
end Lean4Lean.StrengtheningRound4

namespace Lean4Lean.StrengtheningRound4
open VEnv VExpr StrengtheningRank

theorem rank_wellFounded : WellFounded RankLT :=
  (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

def exposedCuts : VExpr → Nat
  | .app (.lam A _) a => exposedCuts A + exposedCuts a + 1
  | .app f a => exposedCuts f + exposedCuts a
  | .lam A _ | .forallE A _ => exposedCuts A
  | .proj _ _ e => exposedCuts e
  | _ => 0

theorem CutCert.exact_crossings (h : CutCert c n Γ e) : exposedCuts e = c := by
  induction h with
  | var => rfl
  | prop => rfl
  | pi _ _ ha _ => exact ha
  | beta _ _ _ ha => simp [exposedCuts, S1, ha]

theorem hidden_crossings_no_smaller_certificate (N : Nat) (hN : 2 ≤ N)
    (h : CutCert c n [] ((nested N).lift.inst (.sort .zero))) :
    ¬ RankLT (c,n) (1,2*N+3) := by
  rw [VExpr.inst_lift] at h
  have hc : c = N := h.exact_crossings.symm.trans (nested_cert N []).exact_crossings
  subst c
  intro hlt
  cases hlt <;> omega

#print axioms rank_wellFounded
#print axioms CutCert.exact_crossings
#print axioms hidden_crossings_no_smaller_certificate
end Lean4Lean.StrengtheningRound4

namespace Lean4Lean.StrengtheningRound4
open VEnv VExpr VEnv.Model StrengtheningKripke

theorem KEq_sort_pi_false {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) :
    ¬ KEq env U Γ (.sort u) (.forallE A B) := by
  intro H
  obtain ⟨o, ho, hl⟩ := (H Γ .id .empty hΓ
    (Ctx.SubstEq.id henv.ordered hΓ) TV.empty).1 _ .sort
  rw [hl.sort_inv] at ho
  exact Model.forallE_not_sort ho

/-- Same-target type-class extraction is allowed: no key is pulled backwards. -/
theorem KEq_pi_domain_typed {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (ha : env.HasType U Γ A (.sort u))
    (H : KEq env U Γ (.forallE A B) (.forallE A' B')) :
    env.IsDefEq U Γ A A' (.sort u) := by
  obtain ⟨o, ho, hl⟩ := (H Γ .id .empty hΓ
    (Ctx.SubstEq.id henv.ordered hΓ) TV.empty).1 _ .piDom
  rw [hl.piDom_inv] at ho
  have he := Obs.piDom_mem ho
  simp only [VExpr.subst_id] at he
  have hm : TyCls env U Γ A A' := by rw [he]; exact TyCls.self
  have hc := (TyCls.mem_iff_chain henv.ordered hΓ ha).mp hm
  exact hc.collapse_of_chainHeadInjectivity henv henv.chainHeadInjectivity hΓ ha

#print axioms KEq_sort_pi_false
#print axioms KEq_pi_domain_typed
end Lean4Lean.StrengtheningRound4

namespace Lean4Lean.StrengtheningRound4
open VEnv VExpr StrengtheningRank

/-- Inhabitants of an opaque Type are neither functions, proofs nor structures.
All exclusions are derived from ordinary typing and head inversion. -/
theorem opaque_type_exclusions {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (hr : env.Rigid I) (hn : ∀ info, ¬ env.projections I info)
    (hI : env.HasType U Γ (.const I lsI) S1)
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

#print axioms opaque_type_exclusions
end Lean4Lean.StrengtheningRound4
