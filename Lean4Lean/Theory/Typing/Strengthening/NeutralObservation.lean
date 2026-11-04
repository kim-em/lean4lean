import Lean4Lean.Theory.Typing.Strengthening.PureObservationForward

/-! # Finite demands with a variable as their operational result

Unlike the Pi/sort interpretation, this observation relation has no rules for
literal type heads. Its base demand can therefore denote an exact free variable.
The model is used for operational beta readout, not equality reflection.
-/
namespace Lean4Lean.VEnv.Strengthening.NeutralObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
open PureObservation (Ob Sets)

/-- Only variables and application/lambda behavior generate neutral demands. -/
inductive Obs : Sets → VExpr → Ob → Prop where
  | var : S i o → Obs S (.bvar i) o
  | app : Obs S f (.app keys o) → (∀ key ∈ keys, Obs S a key) → Obs S (.app f a) o
  | lam : Obs (Sets.cons (fun key => key ∈ keys) S) b o → Obs S (.lam A b) (.app keys o)
  | sub : Obs S e o → Ob.Le o o' → Obs S e o'

/-- A neutral demand excludes constants, projections and literal type heads. -/
def NeutralHead : VExpr → Prop
  | .bvar .. | .app .. | .lam .. => True
  | _ => False

/-- Every observation has a potentially neutral outer constructor. -/
theorem Obs.neutralHead (H : Obs S e o) : NeutralHead e := by
  induction H with
  | var | app | lam => trivial
  | sub _ _ ih => exact ih

/-- Variable renaming transports every demand supplied by the target valuation. -/
theorem Obs.rename (H : Obs S e o) (hρ : ∀ i o, S i o → T (ρ.liftVar i) o) :
    Obs T (e.lift' ρ) o := by
  induction H generalizing ρ T with
  | var h => exact .var (hρ _ _ h)
  | app _ _ ihf iha => exact .app (ihf hρ) (fun key hk => iha key hk hρ)
  | lam _ ih =>
    apply Obs.lam
    apply ih (ρ := ρ.cons)
    intro i o hi
    cases i with
    | zero => exact hi
    | succ i => exact hρ i o hi
  | sub _ h ih => exact .sub (ih hρ) h

/-- A fresh binder can carry arbitrary additional demands. -/
theorem Obs.lift (H : Obs S e o) : Obs (Sets.cons P S) e.lift o := by
  rw [lift_eq_lift']
  exact H.rename (ρ := Lift.refl.skip) (fun _ _ h => h)

/-- Application inversion absorbs subsumption into the function demand. -/
theorem Obs.app_inv (H : Obs S (.app f a) o) :
    ∃ keys, Obs S f (.app keys o) ∧ ∀ key ∈ keys, Obs S a key := by
  generalize he : VExpr.app f a = e at H
  induction H with
  | app hf ha => cases he; exact ⟨_, hf, ha⟩
  | sub _ h ih =>
    obtain ⟨keys, hf, ha⟩ := ih he
    exact ⟨keys, .sub hf (.app id (fun _ h => h) (fun _ _ => .refl) h), ha⟩
  | var | lam => cases he

/-- A lambda demand records the finite assumptions used by its body. -/
theorem Obs.lam_inv (H : Obs S (.lam A b) o) :
    ∃ keys result, Obs (Sets.cons (fun key => key ∈ keys) S) b result ∧
      Ob.Le (.app keys result) o := by
  generalize he : VExpr.lam A b = e at H
  induction H with
  | lam hb => cases he; exact ⟨_, _, hb, .refl⟩
  | sub _ h ih => obtain ⟨_, _, hb, hl⟩ := ih he; exact ⟨_, _, hb, hl.trans h⟩
  | var | app => cases he

/-- Simultaneous substitution transports all supplied variable observations. -/
theorem Obs.subst (H : Obs S e o)
    (hσ : ∀ i key, S i key → Obs T (σ i) key) : Obs T (e.subst σ) o := by
  induction H generalizing T σ with
  | var h => exact hσ _ _ h
  | app _ _ ihf iha => exact .app (ihf hσ) (fun key hk => iha key hk hσ)
  | @lam keys S b o A _ ih =>
    apply Obs.lam
    apply ih
    intro i key hi
    cases i with
    | zero => exact .var hi
    | succ i => exact (hσ i key hi).lift
  | sub _ h ih => exact .sub (ih hσ) h

/-- An argument discharges the body's finite binder demands. -/
theorem Obs.inst {keys : List Ob} (H : Obs (Sets.cons (fun key => key ∈ keys) S) b o)
    (ha : ∀ key ∈ keys, Obs S a key) : Obs S (b.inst a) o := by
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using
    H.subst (σ := VExpr.Subst.one a) (fun i key hi => by
      cases i with
      | zero => exact ha key hi
      | succ i => exact .var hi)

/-- Beta contraction preserves neutral demands. -/
theorem Obs.beta_forward (H : Obs S (.app (.lam A b) a) o) : Obs S (b.inst a) o := by
  obtain ⟨keys, hf, ha⟩ := H.app_inv
  obtain ⟨original, result, hb, hle⟩ := hf.lam_inv
  cases hle with
  | refl => exact hb.inst ha
  | app f hf hk ho =>
    exact .sub (hb.inst (fun key hkey => .sub (ha (f key) (hf key hkey)) (hk key hkey))) ho

/-- Compatible beta paths preserve all neutral observations. -/
theorem Obs.beta_compute_forward (R : BetaRed e out) (H : Obs S e o) : Obs S out o := by
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
  | forallE | proj => exact H.neutralHead.elim

/-- An unused binder preserves every observation without demands on its argument. -/
theorem Obs.constant_expansion (H : Obs S e o) :
    Obs S (.app (.lam A e.lift) a) o :=
  .app (.lam (H.lift (P := fun key => key ∈ ([] : List Ob)))) (by simp)

/-- An identity wrapper demands exactly the payload's existing observation. -/
theorem Obs.identity_expansion (H : Obs S e o) :
    Obs S (.app (.lam A (.bvar 0)) e) o := by
  apply Obs.app (keys := [o])
  · exact .lam (.var (by simp [Sets.cons]))
  · intro key hk
    have E : key = o := List.mem_singleton.1 hk
    exact E ▸ H

/-- Interpret the base demand as beta reduction to an arbitrary designated expression.
The unused sort demand is impossible; function demands retain their meaning. -/
def Realizes (target : VExpr) (e : VExpr) : Ob → Prop
  | .pi => BetaRed e target
  | .sort => False
  | .app keys result => ∀ a, (∀ key ∈ keys, Realizes target a key) → Realizes target (.app e a) result
termination_by o => sizeOf o

/-- Realization is closed under beta predecessors. -/
theorem Realizes.compute_back (R : BetaRed e e') (H : Realizes target e' o) : Realizes target e o := by
  cases o with
  | pi =>
    simp only [Realizes] at H ⊢
    exact R.trans H
  | sort => simp only [Realizes] at H
  | app keys result =>
    simp only [Realizes] at H ⊢
    exact fun a ha => Realizes.compute_back (.app R .refl) (H a ha)
termination_by sizeOf o

/-- Observation subsumption is sound for this variable interpretation too. -/
theorem Realizes.mono (h : Ob.Le o o') (H : Realizes target e o) : Realizes target e o' := by
  induction h generalizing e with
  | refl => exact H
  | app f hf _ _ ihk iho =>
    simp only [Realizes] at H ⊢
    exact fun a ha => iho (H a (fun k hk => ihk k hk (ha (f k) (hf k hk))))

/-- Finite neutral observations have operational meaning under any realizing
substitution, including substitutions into open expressions. -/
theorem Obs.realizes (H : Obs S e o) (hσ : ∀ i key, S i key → Realizes target (σ i) key) :
    Realizes target (e.subst σ) o := by
  induction H generalizing σ with
  | var h => exact hσ _ _ h
  | app _ _ ihf iha =>
    have hf := ihf hσ
    simp only [Realizes] at hf
    exact hf _ (fun key hk => iha key hk hσ)
  | @lam keys S b o A _ ih =>
    simp only [Realizes]
    intro a ha
    have hb := ih (σ := σ.cons a) (by
      intro i key hi
      cases i with
      | zero => exact ha key hi
      | succ i => exact hσ i key hi)
    have R : BetaRed (.app ((VExpr.lam A b).subst σ) a) (b.subst (σ.cons a)) := by
      simpa only [VExpr.subst, inst_lift_cons] using
        (BetaRed.beta (A := A.subst σ) (b := b.subst σ.lift) (a := a))
    exact Realizes.compute_back R hb
  | sub _ h ih => exact Realizes.mono h (ih hσ)

/-- A demand originating at one free variable reads that exact variable back
by finite beta reduction. No typing or global normalization is required. -/
theorem Obs.variable_exposure (H : Obs (fun i o => i = j ∧ o = .pi) e .pi) :
    BetaRed e (.bvar j) := by
  have h := H.realizes (σ := .id) (target := .bvar j) (fun i key hi => by
    obtain ⟨rfl, rfl⟩ := hi
    simp only [Realizes]
    exact BetaRed.refl)
  simpa only [subst_id, Realizes] using h

/-- An identity demand at the empty valuation computes to any supplied argument,
including expressions with opaque constants and arbitrary annotations. -/
theorem Obs.identity_behavior
    (H : Obs (fun _ _ => False) e (.app [.pi] .pi)) (a : VExpr) :
    BetaRed (.app e a) a := by
  have h := H.realizes (σ := .id) (target := a) (fun _ _ h => h.elim)
  simp only [subst_id, Realizes] at h
  exact h a (fun key hk => by
    obtain rfl := List.mem_singleton.1 hk
    simp only [Realizes]
    exact .refl)

end Lean4Lean.VEnv.Strengthening.NeutralObservation
