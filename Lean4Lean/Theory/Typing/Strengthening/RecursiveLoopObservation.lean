import Lean4Lean.Theory.Typing.Strengthening.RecursiveLoopComparison

/-! # Finite observations when the recursive role is absent

Once recursive nodes are excluded, a closed loop body has only the two simple
roles Prop and Prop → Prop. Finite observations suffice to analyze this fragment;
no normalization theorem for the ambient recursive calculus is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedEta
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
variable [Params] {r : LoopRole}

def PropVariables (Γ : List VExpr) : Prop :=
  ∀ i, i < Γ.length → env.HasType univs Γ (.bvar i) prop

theorem PropVariables.cons (H : PropVariables Γ) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.IsDefEqU univs Γ A prop) : PropVariables (A :: Γ) := by
  intro i hi
  cases i with
  | zero =>
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) :=
      ⟨hΓ, _, (hA.of_r henv hΓ (.sort (by trivial))).hasType.1⟩
    have h := hA.weakN henv (Ctx.LiftN.one (A := A))
    exact HasType.defeqU_r henv hΓA h (.bvar .zero)
  | succ i =>
    have hv := (H i (Nat.lt_of_succ_lt_succ hi)).weakN henv (Ctx.LiftN.one (A := A))
    simpa [prop, liftN, liftVar, Nat.add_comm] using hv

def LoopRole.observation : LoopRole → Ob
  | .recursive => .pi
  | .function => .app [.sort] .sort
  | .proposition => .sort

/-- Bodies with no recursive role in a proposition-variable context admit the
ordinary finite observation of their remaining simple type. -/
theorem LoopBody.simple_observation
    (hδ : ∀ Δ, env.IsDefEq univs Δ (domain c) (domainValue c) (.sort (.succ .zero)))
    (H : LoopBody c Γ e) (HN : NoRecursive c Γ e)
    (ht : env.HasType univs Γ e (r.type c)) (hr : r ≠ .recursive)
    (hΓ : OnCtx Γ (env.IsType univs)) (hvars : PropVariables Γ)
    (hS : ∀ i, i < Γ.length → S i .sort) :
    Obs .empty S (eraseLamDomains e) r.observation := by
  induction H generalizing r S with
  | bvar _ =>
    have hi := ht.closedN henv (CtxWF.closed henv hΓ)
    have hp := hvars _ hi
    have hrp : r = .proposition := LoopRole.type_injective hδ hΓ (ht.uniqU henv hΓ hp)
    subst r
    exact .var (hS _ hi)
  | app _ Hf Ha ihf iha =>
    cases HN with
    | app _ HNf HNa =>
      obtain ⟨rf, hf⟩ := Hf.role
      have hrf : rf ≠ .recursive := fun h => by subst rf; exact HNf.not_recursive hf
      obtain ⟨A, B, hfPi, ha⟩ := ht.app_inv henv hΓ
      obtain ⟨ra, rb, harrow, hA, _⟩ := LoopRole.pi_typing hδ hΓ hf hfPi
      cases rf with
      | recursive => exact (hrf rfl).elim
      | proposition => cases harrow
      | function =>
        cases harrow
        have haP := ha.defeqU_r henv hΓ hA
        have hp : env.HasType univs _ _ prop := hf.app haP
        have hrp : r = .proposition := LoopRole.type_injective hδ hΓ (ht.uniqU henv hΓ hp)
        subst r
        exact .app (ihf HNf hf (by decide) hΓ hvars hS) (by
          intro key hk
          obtain rfl : key = .sort := List.mem_singleton.1 hk
          exact iha HNa haP (by decide) hΓ hvars hS)
  | lam _ Hb ih =>
    cases HN with
    | lam _ HNb =>
      obtain ⟨B, hPi, hb⟩ := ht.lam_inv_forallE henv hΓ
      cases r with
      | recursive => exact (hr rfl).elim
      | proposition => exact (hPi.symm.sort_forallE_inv henv hΓ).elim
      | function =>
        obtain ⟨⟨_, hA⟩, ⟨_, hB⟩⟩ := hPi.forallE_inv henv hΓ
        have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA.hasType.1⟩
        apply Obs.lam
        apply ih (r := .proposition) HNb (hB.defeq hb) (by decide) hΓA (hvars.cons hΓ ⟨_, hA⟩)
        intro i hi
        cases i with
        | zero => exact List.mem_singleton_self _
        | succ i => exact hS i (Nat.lt_of_succ_lt_succ hi)

omit [Params] in
/-- Applying the untyped self-application loop to a beta-normal argument still
has only itself as a finite beta reduct. -/
theorem omega_app_beta_eq (hD : ¬ Developments.HasBeta D) (hx : ¬ Developments.HasBeta x)
    (R : BetaRed (.app (RecursiveDomain.omegaTerm D) x) out) :
    out = .app (RecursiveDomain.omegaTerm D) x := by
  suffices aux : ∀ {e out}, BetaRed e out → e = .app (RecursiveDomain.omegaTerm D) x →
      out = .app (RecursiveDomain.omegaTerm D) x from aux R rfl
  intro e out R
  induction R with
  | refl => exact id
  | trans _ _ ih1 ih2 => exact fun h => ih2 (ih1 h)
  | app Rf Ra _ _ =>
    intro h
    cases h
    rw [RecursiveDomain.omega_beta_eq hD Rf, beta_eq_of_not_hasBeta Ra hx]
  | beta => intro h; cases h
  | lam | forallE | proj => intro h; cases h

omit [Params] in
/-- The loop has no finite observation as a total function on the sort demand.
Realizing that observation at a literal sort would expose a sort by beta alone,
contradicting the exact self-application invariant. -/
theorem omega_no_simple_observation :
    ¬ Obs .empty (fun _ _ => False) (eraseLamDomains (omegaTerm c)) (.app [.sort] .sort) := by
  intro H
  have h := H.realizes (σ := .id) (fun _ _ h => h.elim)
  rw [subst_id] at h
  have hs : Realizes .empty (VExpr.sort .zero) Ob.sort := by
    simp only [Realizes]
    exact ⟨_, .refl⟩
  simp only [Realizes] at h
  obtain ⟨u, R⟩ := h (.sort .zero) (by
    intro key hk
    obtain rfl : key = .sort := List.mem_singleton.1 hk
    exact hs)
  have heq := omega_app_beta_eq (D := prop) (x := .sort .zero)
    (by simp [prop, Developments.HasBeta]) (by simp [Developments.HasBeta]) R.to_beta
  cases heq

/-- Every full reduct of the closed loop retains some recursive computational
role. Removing all such nodes would give a finite simple-type observation, which
beta/function-eta simulation transports back to the unobservable loop. -/
theorem omega_full_not_noRecursive
    (hc : env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Δ, env.IsDefEq univs Δ (domain c) (domainValue c) (.sort (.succ .zero)))
    (R : FullReduction [] (omegaTerm c) out) : ¬ NoRecursive c [] out := by
  intro HN
  have H := omega_loopBody (Γ := []) hc hδ
  have Hout := H.fullReduction hδ trivial R
  have ht := FullReduction.hasType (Γ := []) trivial R (omega_typed (Γ := []) hc hδ)
  have ho := Hout.simple_observation hδ HN (r := .function) ht (by decide) trivial
    (by intro i hi; cases hi) (S := fun _ _ => False) (by intro i hi; cases hi)
  exact omega_no_simple_observation ((H.fullReduction_erases hδ trivial R).obs_back ho)

end Lean4Lean.VEnv.Strengthening.GuardedEta
