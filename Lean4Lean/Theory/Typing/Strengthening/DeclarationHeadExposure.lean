import Lean4Lean.Theory.Typing.Strengthening.PureHeadExposure

/-! # Head exposure with closed declaration unfolding

Recursive declaration equations are admitted without a normalization assumption.
Finite beta/delta/eta paths exposing a Pi or sort yield finite beta/delta paths.
The computational paths lower through arbitrary lifts because declaration bodies
are closed; eta annotations need not themselves lower.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
variable {D : Definitions}

/-- Only valuation entries for variables actually available in the expression can
matter to an observation. This also handles bound variables under lambdas. -/
theorem Obs.mono_closed (H : Obs D S e o) (hc : e.ClosedN k)
    (hST : ∀ i, i < k → ∀ o, S i o → T i o) : Obs D T e o := by
  induction H generalizing k T with
  | var h => exact .var (hST _ hc _ h)
  | sort => exact .sort
  | pi => exact .pi
  | app _ _ ihf iha => exact .app (ihf hc.1 hST) (fun key hk => iha key hk hc.2 hST)
  | lam _ ih =>
    apply Obs.lam
    apply ih hc.2
    intro i hi o ho
    cases i with
    | zero => exact ho
    | succ i => exact hST i (Nat.lt_of_succ_lt_succ hi) o ho
  | delta hd hr => exact .delta hd hr
  | sub _ h ih => exact .sub (ih hc hST) h

/-- A closed body's observations do not depend on any surrounding valuation. -/
theorem Obs.closed_valuation (H : Obs D S e o) (hc : e.Closed) : Obs D T e o :=
  H.mono_closed hc (fun _ hi => (Nat.not_lt_zero _ hi).elim)

/-- Closed declaration unfolding cannot introduce an observation. -/
theorem Obs.delta_back (hd : D.unfolds c ls rhs) (H : Obs D S rhs o) :
    Obs D S (.const c ls) o := .delta hd (H.closed_valuation (D.closed hd))

/-- Observations are backwards closed under finite beta/delta computation. -/
theorem Compute.obs_back (R : Compute D e out) (H : Obs D S out o) : Obs D S e o := by
  induction R generalizing S o with
  | refl => exact H
  | trans _ _ ih1 ih2 => exact ih1 (ih2 H)
  | beta => exact H.beta_back
  | delta hd => exact H.delta_back hd
  | app _ _ ihf iha =>
    obtain ⟨keys, hf, ha⟩ := H.app_inv
    exact .app (ihf hf) (fun key hk => iha (ha key hk))
  | lam _ _ _ ihb =>
    obtain ⟨keys, result, hb, hl⟩ := H.lam_inv
    exact .sub (.lam (ihb hb)) hl
  | forallE => exact .sub .pi H.pi_inv
  | proj => exact H.proj_false.elim

/-- Finite computation of a lifted term is a lifted computation of the source.
Closedness is the only condition needed on the declaration equations. -/
theorem Compute.lift_inv (R : Compute D (e.lift' ρ) out) :
    ∃ e', Compute D e e' ∧ out = e'.lift' ρ := by
  generalize hsrc : e.lift' ρ = source at R
  induction R generalizing e ρ with
  | refl => exact ⟨e, .refl, hsrc.symm⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨e1, R1, h1⟩ := ih1 hsrc
    obtain ⟨e2, R2, h2⟩ := ih2 h1.symm
    exact ⟨e2, R1.trans R2, h2⟩
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
  | beta =>
    obtain ⟨f, a, rfl, hf, rfl⟩ := lift'_eq_app hsrc
    obtain ⟨A, b, rfl, rfl, rfl⟩ := lift'_eq_lam hf.symm
    exact ⟨_, .beta, (lift'_inst_hi b a ρ).symm⟩
  | delta hd =>
    cases e <;> cases hsrc
    exact ⟨_, .delta hd, ((D.closed hd).lift'_eq .zero).symm⟩

/-- Compatible computation and unrestricted function-eta expansion. -/
inductive ComputeEta (D : Definitions) : VExpr → VExpr → Prop where
  | compute : Compute D e out → ComputeEta D e out
  | trans : ComputeEta D a b → ComputeEta D b c → ComputeEta D a c
  | eta : ComputeEta D e (.lam A (.app e.lift (.bvar 0)))
  | app : ComputeEta D f f' → ComputeEta D a a' → ComputeEta D (.app f a) (.app f' a')
  | lam : ComputeEta D A A' → ComputeEta D b b' → ComputeEta D (.lam A b) (.lam A' b')
  | forallE : ComputeEta D A A' → ComputeEta D B B' → ComputeEta D (.forallE A B) (.forallE A' B')
  | proj : ComputeEta D m m' → ComputeEta D (.proj s i m) (.proj s i m')

/-- Every beta/eta path is available with any set of declaration equations. -/
theorem ComputeEta.of_betaEta (R : BetaEta e out) : ComputeEta D e out := by
  induction R with
  | refl => exact .compute .refl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | beta => exact .compute .beta
  | eta => exact .eta
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- Function eta does not add computational observations, including when its
expansion is interspersed with unfolding recursive declarations. -/
theorem ComputeEta.obs_back (R : ComputeEta D e out) (H : Obs D S out o) : Obs D S e o := by
  induction R generalizing S o with
  | compute h => exact h.obs_back H
  | trans _ _ ih1 ih2 => exact ih1 (ih2 H)
  | eta => exact H.eta_back
  | app _ _ ihf iha =>
    obtain ⟨keys, hf, ha⟩ := H.app_inv
    exact .app (ihf hf) (fun key hk => iha (ha key hk))
  | lam _ _ _ ihb =>
    obtain ⟨keys, result, hb, hl⟩ := H.lam_inv
    exact .sub (.lam (ihb hb)) hl
  | forallE => exact .sub .pi H.pi_inv
  | proj => exact H.proj_false.elim

/-- A Pi reached through beta/delta/eta can be exposed without eta. Its recovered
annotations are allowed to differ from those at the end of the original path. -/
theorem ComputeEta.pi_exposure (R : ComputeEta D e (.forallE A B)) :
    ∃ A' B', Compute D e (.forallE A' B') :=
  (R.obs_back (S := fun _ _ => False) .pi).pi_exposure

/-- A sort reached through beta/delta/eta can likewise be exposed without eta. -/
theorem ComputeEta.sort_exposure (R : ComputeEta D e (.sort u)) :
    ∃ v, Compute D e (.sort v) :=
  (R.obs_back (S := fun _ _ => False) .sort).sort_exposure

/-- Exposure above an arbitrary lift supplies actual computational Pi exposure
below, even when intermediate eta annotations mention newly inserted variables. -/
theorem ComputeEta.pi_exposure_below (R : ComputeEta D (e.lift' ρ) (.forallE A B)) :
    ∃ A' B', Compute D e (.forallE A' B') := by
  obtain ⟨A', B', RB⟩ := R.pi_exposure
  obtain ⟨out, R0, he⟩ := RB.lift_inv
  obtain ⟨A0, B0, rfl, _, _⟩ := lift'_eq_forallE he.symm
  exact ⟨A0, B0, R0⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
