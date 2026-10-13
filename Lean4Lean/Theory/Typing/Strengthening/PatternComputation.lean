import Lean4Lean.Theory.Typing.Strengthening.ProjectionComputation
import Lean4Lean.Theory.Typing.Strengthening.PatternTypingChecks

/-! # Context-independent pattern computation

All concrete core parallel steps embed in this compatible computational relation.
Uniform check certificates allow purely syntactic lift inversion; typing is replayed
only in the smaller context. This extends the operational side of the head model,
without asserting eta elimination or observation adequacy for the new rules.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

/-- Closed declaration computation survives arbitrary raw substitution. -/
theorem Compute.subst (R : Compute D e out) : Compute D (e.subst σ) (out.subst σ) := by
  induction R generalizing σ with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | beta => simp only [VExpr.subst, subst_inst]; exact .beta
  | delta hd => simpa only [VExpr.subst, (D.closed hd).subst_eq .zero] using Compute.delta hd
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | proj _ ih => exact .proj ih

variable [Params]

/-- Saturated projection computation survives arbitrary raw substitution. -/
theorem ProjectionCompute.subst (R : ProjectionCompute D e out) :
    ProjectionCompute D (e.subst σ) (out.subst σ) := by
  induction R generalizing σ with
  | base h => exact .base h.subst
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | projIota hi hl hg =>
    simp only [VExpr.subst, subst_mkApps]
    apply ProjectionCompute.projIota hi (by simpa using hl)
    simp only [List.getElem?_map, hg, Option.map_some]
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | proj _ ih => exact .proj ih

/-- Context-independent computation with registered patterns. The check certificate
is uniform over matching typed sources, and is preserved unchanged when lowering. -/
inductive PatternCompute (D : Definitions) : VExpr → VExpr → Prop where
  | base : ProjectionCompute D e out → PatternCompute D e out
  | trans : PatternCompute D a b → PatternCompute D b c → PatternCompute D a c
  | pattern {p : Pattern} {r : p.RHS × p.Check} {levels : List VLevel}
      {captures : p.Path → VExpr} :
      Pat p r → p.Matches e levels captures →
      CheckFromTyping env univs p r levels → PatternCompute D e (r.1.apply levels captures)
  | app : PatternCompute D f f' → PatternCompute D a a' →
      PatternCompute D (.app f a) (.app f' a')
  | lam : PatternCompute D A A' → PatternCompute D b b' →
      PatternCompute D (.lam A b) (.lam A' b')
  | forallE : PatternCompute D A A' → PatternCompute D B B' →
      PatternCompute D (.forallE A B) (.forallE A' B')
  | proj : PatternCompute D m m' → PatternCompute D (.proj s i m) (.proj s i m')

/-- Identity computation. -/
theorem PatternCompute.refl : PatternCompute D e e := .base (.base .refl)

/-- Computing captures computes an instantiated pattern RHS. -/
theorem PatternCompute.apply_pat {p : Pattern} (r : p.RHS)
    {levels : List VLevel} {captures captures' : p.Path → VExpr}
    (H : ∀ a, PatternCompute D (captures a) (captures' a)) :
    PatternCompute D (r.apply levels captures) (r.apply levels captures') := by
  induction r with
  | fixed => exact .refl
  | var => exact H _
  | app _ _ ihf iha => exact .app ihf iha

omit [Params] in
/-- Every actual core parallel step embeds, including quotient and guarded
recursor rules and parallel computation of all captures. No source typing or
ambient context well-formedness is needed for this syntactic embedding. -/
theorem PatternCompute.of_parRed {env : VEnv} (henv : env.WF)
    (H : @ParRed (henv.params U) Γ e out) :
    @PatternCompute (henv.params U) D e out := by
  letI := henv.params U
  induction H with
  | bvar | sort | const => exact .refl
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | proj _ ih => exact .proj ih
  | beta _ _ ihb iha =>
    exact (PatternCompute.app (.lam .refl ihb) iha).trans (.base (.base .beta))
  | extra hp hm hc _ ih =>
    exact (PatternCompute.pattern hp hm (ConcretePattern.checkFromTyping henv hp hc)).trans
      (PatternCompute.apply_pat _ ih)

/-- Pattern computation survives arbitrary substitution, without checking or
typing that substitution: each rule's certificate is uniform over all occurrences. -/
theorem PatternCompute.subst (R : PatternCompute D e out) :
    PatternCompute D (e.subst σ) (out.subst σ) := by
  induction R generalizing σ with
  | base h => exact .base h.subst
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | pattern hp hm hc =>
    rw [Pattern.RHS.subst_apply]
    exact .pattern hp (Pattern.matches_subst hm) hc
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | proj _ ih => exact .proj ih

/-- Reconstruct intermediate typings from source typing alone. Pattern checks
are established in each replay context using the uniform certificate. -/
theorem PatternCompute.simAt (R : PatternCompute D e out)
    (hD : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs)) : env.SimAt univs Γ e out := by
  induction R generalizing Γ with
  | base h => exact h.simAt hD hΓ
  | trans _ _ ih1 ih2 => exact .trans (ih1 hΓ) (ih2 hΓ)
  | pattern hp hm hc =>
    intro T ht
    exact (pat_wf hΓ hp hm ht (hc hΓ hm ht)).of_l henv hΓ ht
  | app _ _ ih1 ih2 => exact .app henv.orderedStrong hΓ (ih1 hΓ) (ih2 hΓ)
  | lam _ _ ih1 ih2 => exact .lam henv.orderedStrong hΓ (ih1 hΓ) ih2
  | forallE _ _ ih1 ih2 => exact .forallE henv.orderedStrong hΓ (ih1 hΓ) ih2
  | proj _ ih => exact .proj henv.orderedStrong hΓ (ih hΓ)

/-- Every pattern computation path starting at a lift is itself a lift.
This is a syntactic theorem: it assumes no typing in either context. -/
theorem PatternCompute.lift_inv (R : PatternCompute D (e.lift' ρ) out) :
    ∃ e', PatternCompute D e e' ∧ out = e'.lift' ρ := by
  generalize hsrc : e.lift' ρ = source at R
  induction R generalizing e ρ with
  | base h =>
    rw [← hsrc] at h
    obtain ⟨e', hr, he⟩ := h.lift_inv
    exact ⟨e', .base hr, he⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨e1, R1, h1⟩ := ih1 hsrc
    obtain ⟨e2, R2, h2⟩ := ih2 h1.symm
    exact ⟨e2, R1.trans R2, h2⟩
  | pattern hp hm hc =>
    rw [← hsrc] at hm
    obtain ⟨captures, hm, hcaptures⟩ := Pattern.matches_lift'.1 hm
    refine ⟨_, .pattern hp hm hc, ?_⟩
    rw [Pattern.RHS.lift'_apply]
    congr 1
    exact funext hcaptures
  | app _ _ ihf iha =>
    obtain ⟨f, a, rfl, rfl, rfl⟩ := lift'_eq_app hsrc
    obtain ⟨f', Rf, rfl⟩ := ihf rfl
    obtain ⟨a', Ra, rfl⟩ := iha rfl
    exact ⟨_, .app Rf Ra, rfl⟩
  | proj _ ihm =>
    obtain ⟨m, rfl, rfl⟩ := lift'_eq_proj hsrc
    obtain ⟨m', Rm, rfl⟩ := ihm rfl
    exact ⟨_, .proj Rm, rfl⟩
  | lam _ _ ihA ihb =>
    obtain ⟨A, b, rfl, rfl, rfl⟩ := lift'_eq_lam hsrc
    obtain ⟨A', RA, rfl⟩ := ihA rfl
    obtain ⟨b', Rb, rfl⟩ := ihb rfl
    exact ⟨_, .lam RA Rb, rfl⟩
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, rfl, rfl⟩ := lift'_eq_forallE hsrc
    obtain ⟨A', RA, rfl⟩ := ihA rfl
    obtain ⟨B', RB, rfl⟩ := ihB rfl
    exact ⟨_, .forallE RA RB, rfl⟩

/-- Lower a complete path and reconstruct its equality at the original source
type, without an ambient typing premise and without strengthening. -/
theorem PatternCompute.descend (R : PatternCompute D (e.lift' ρ) out)
    (hD : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs)) (he : HasType env univs Γ e T) :
    ∃ e', out = e'.lift' ρ ∧ PatternCompute D e e' ∧ IsDefEq env univs Γ e e' T := by
  obtain ⟨e', R0, hh⟩ := R.lift_inv
  exact ⟨e', hh, R0, R0.simAt hD hΓ T he⟩

/-- Exact reflection when both endpoints are already presented below a lift. -/
theorem PatternCompute.reflect (R : PatternCompute D (e.lift' ρ) (out.lift' ρ))
    (hD : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs)) (he : HasType env univs Γ e T) :
    IsDefEq env univs Γ e out T := by
  obtain ⟨out₀, hh, _, h⟩ := R.descend hD hΓ he
  cases VExpr.lift'_inj.1 hh
  exact h

omit [Params] in
/-- Reflect an actual core parallel step with lifted endpoints using only the
original source typing. The ambient context need not be well formed, or even
related to the smaller context: the concrete checks are replayed from typing. -/
theorem core_reflect {env : VEnv} (henv : env.WF)
    (H : @ParRed (henv.params U) Γ' (e.lift' ρ) (out.lift' ρ))
    (hΓ : OnCtx Γ (env.IsType U)) (he : HasType env U Γ e T) :
    IsDefEq env U Γ e out T := by
  letI := henv.params U
  exact (PatternCompute.of_parRed (D := .empty) henv H).reflect
    (fun _ _ _ _ h => h.elim) hΓ he

/-- A computational Pi exposure above provides the actual function type below,
including paths which compute through registered patterns. Eta elimination
for this larger operational relation is still needed. -/
theorem PatternCompute.function_type_below
    (R : PatternCompute D (T.lift' ρ) (.forallE A B))
    (hD : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs)) (hf : HasType env univs Γ f T) :
    ∃ A' B', HasType env univs Γ f (.forallE A' B') ∧ IsDefEqU env univs Γ T (.forallE A' B') := by
  obtain ⟨out, R0, hh⟩ := R.lift_inv
  obtain ⟨A', B', rfl, _, _⟩ := lift'_eq_forallE hh.symm
  obtain ⟨u, hT⟩ := hf.isType henv hΓ
  have HT := R0.simAt hD hΓ (.sort u) hT
  exact ⟨A', B', HT.defeq hf, _, HT⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
