import Lean4Lean.Theory.Typing.Strengthening.PureHeadExposure

/-! # Forward beta preservation of finite observations

Substitution of observation-realizing expressions closes the opposite direction
from the existing backward-beta theorem. No typing or normalization is used.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
variable {D : Definitions}

/-- Realizing each source variable's demands transports its observation through
an arbitrary simultaneous substitution, including under lambda binders. -/
theorem Obs.subst (H : Obs D S e o)
    (hσ : ∀ i key, S i key → Obs D T (σ i) key) : Obs D T (e.subst σ) o := by
  induction H generalizing T σ with
  | var h => exact hσ _ _ h
  | sort => exact .sort
  | pi => exact .pi
  | app _ _ ihf iha => exact .app (ihf hσ) (fun key hk => iha key hk hσ)
  | @lam keys S b o A _ ih =>
    apply Obs.lam
    apply ih
    intro i key hi
    cases i with
    | zero => exact .var hi
    | succ i => exact (Obs.lift_iff (P := fun key => key ∈ keys)).2 (hσ i key hi)
  | delta hd hr => exact .delta hd hr
  | sub _ h ih => exact .sub (ih hσ) h

/-- A body's finite demands can be discharged by observations of one argument. -/
theorem Obs.inst {keys : List Ob} (H : Obs D (Sets.cons (fun key => key ∈ keys) S) b o)
    (ha : ∀ key ∈ keys, Obs D S a key) : Obs D S (b.inst a) o := by
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using
    H.subst (σ := VExpr.Subst.one a) (fun i key hi => by
      cases i with
      | zero => exact ha key hi
      | succ i => exact .var hi)

/-- Root beta contraction preserves observations, including the contravariant
finite demands introduced by subsumption of the function observation. -/
theorem Obs.beta_forward (H : Obs D S (.app (.lam A b) a) o) : Obs D S (b.inst a) o := by
  obtain ⟨keys, hf, ha⟩ := H.app_inv
  obtain ⟨original, result, hb, hle⟩ := hf.lam_inv
  cases hle with
  | refl => exact hb.inst ha
  | app f hf hk ho =>
    exact .sub (hb.inst (fun key hkey => .sub (ha (f key) (hf key hkey)) (hk key hkey))) ho

/-- Every finite compatible beta computation preserves all existing observations. -/
theorem Obs.beta_compute_forward (R : BetaRed e out) (H : Obs D S e o) : Obs D S out o := by
  induction R generalizing S o with
  | refl => exact H
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ H)
  | beta => exact H.beta_forward
  | app _ _ ihf iha =>
    obtain ⟨keys, hf, ha⟩ := H.app_inv
    exact .app (ihf hf) (fun key hk => iha (ha key hk))
  | lam _ _ _ ihb =>
    obtain ⟨keys, result, hb, hle⟩ := H.lam_inv
    exact .sub (.lam (ihb hb)) hle
  | forallE => exact .sub .pi H.pi_inv
  | proj => exact H.proj_false.elim

/-- Constants are opaque when no declaration equations are interpreted. -/
theorem Obs.empty_const_false (H : Obs .empty S (.const c ls) o) : False := by
  generalize E : VExpr.const c ls = e at H
  induction H with
  | delta hd _ => exact hd.elim
  | sub _ _ ih => exact ih E
  | var | sort | pi | lam | app => cases E

end Lean4Lean.VEnv.Strengthening.PureObservation
