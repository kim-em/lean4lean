import Lean4Lean.Theory.Typing.Strengthening.ConstructorObservation

/-! # Function eta cannot add finite non-function observations

Subsumption and renaming make the finite-demand interpretation insensitive to the
fresh eta variable. The backwards eta theorem needs no typing of the annotation;
it concerns computational observations, not equality of annotated terms.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

open PureObservation (Definitions PatternCompute)
variable {D : Definitions}

private theorem Ob.Le.trans_aux (h : Ob.Le x y) :
    (∀ w, Ob.Le w x → Ob.Le w y) ∧ (∀ z, Ob.Le y z → Ob.Le x z) := by
  induction h with
  | refl => exact ⟨fun _ h => h, fun _ h => h⟩
  | field ho ih =>
    constructor
    · intro w hw
      cases hw with
      | refl => exact .field ho
      | field h => exact .field (ih.1 _ h)
    · intro z hz
      cases hz with
      | refl => exact .field ho
      | field h => exact .field (ih.2 _ h)
  | app f hf1 hf2 ho ihk iho =>
    constructor
    · intro w hw
      cases hw with
      | refl => exact .app f hf1 hf2 ho
      | app g hg1 hg2 hgo =>
        exact .app (fun k => f (g k)) (fun k hk => hf1 _ (hg1 k hk))
          (fun k hk => (ihk _ (hg1 k hk)).2 _ (hg2 k hk)) (iho.1 _ hgo)
    · intro z hz
      cases hz with
      | refl => exact .app f hf1 hf2 ho
      | app g hg1 hg2 hgo =>
        exact .app (fun k => g (f k)) (fun k hk => hg1 _ (hf1 k hk))
          (fun k hk => (ihk k hk).1 _ (hg2 _ (hf1 k hk))) (iho.2 _ hgo)

theorem Ob.Le.trans (h1 : Ob.Le x y) (h2 : Ob.Le y z) : Ob.Le x z :=
  (h1.trans_aux).2 _ h2

variable [Params]

/-- Enlarging a valuation can only add observations. -/
theorem Obs.mono (H : Obs D S e o) (hST : ∀ i o, S i o → T i o) : Obs D T e o := by
  induction H generalizing T with
  | var h => exact .var (hST _ _ h)
  | sort => exact .sort
  | pi => exact .pi
  | app _ _ ihf iha => exact .app (ihf hST) (fun key hk => iha key hk hST)
  | lam _ ih =>
    apply Obs.lam
    apply ih
    intro i o hi
    cases i with
    | zero => exact hi
    | succ i => exact hST i o hi
  | ctor hi hl hg ho => exact .ctor hi hl hg ho
  | ctorTuple hn => exact .ctorTuple hn
  | recursor hp hc hr => exact .recursor hp hc hr
  | proj _ ih => exact .proj (ih hST)
  | delta hd hr => exact .delta hd hr
  | sub _ h ih => exact .sub (ih hST) h

/-- Rename variables along any lift whose target valuation supplies their demands. -/
theorem Obs.rename (H : Obs D S e o) (hρ : ∀ i o, S i o → T (ρ.liftVar i) o) :
    Obs D T (e.lift' ρ) o := by
  induction H generalizing ρ T with
  | var h => exact .var (hρ _ _ h)
  | sort => exact .sort
  | pi => exact .pi
  | app _ _ ihf iha => exact .app (ihf hρ) (fun key hk => iha key hk hρ)
  | lam _ ih =>
    apply Obs.lam
    apply ih (ρ := ρ.cons)
    intro i o hi
    cases i with
    | zero => exact hi
    | succ i => exact hρ i o hi
  | ctor hi hl hg ho => exact .ctor hi hl hg ho
  | ctorTuple hn => exact .ctorTuple hn
  | recursor hp hc hr => exact .recursor hp hc hr
  | proj _ ih => exact .proj (ih hρ)
  | delta hd hr => exact .delta hd hr
  | sub _ h ih => exact .sub (ih hρ) h

/-- Renaming is also reflected without any typing of the renamed source. -/
theorem Obs.rename_inv (H : Obs D T (e.lift' ρ) o)
    (hρ : ∀ i o, T (ρ.liftVar i) o → S i o) : Obs D S e o := by
  generalize he : e.lift' ρ = target at H
  induction H generalizing e ρ S with
  | var h =>
    cases e <;> cases he
    exact .var (hρ _ _ h)
  | sort =>
    cases e <;> cases he
    exact .sort
  | pi =>
    obtain ⟨_, _, rfl, _, _⟩ := lift'_eq_forallE he
    exact .pi
  | app _ _ ihf iha =>
    obtain ⟨f, a, rfl, rfl, rfl⟩ := lift'_eq_app he
    exact .app (ihf hρ rfl) (fun key hk => iha key hk hρ rfl)
  | lam _ ih =>
    obtain ⟨A, b, rfl, rfl, rfl⟩ := lift'_eq_lam he
    apply Obs.lam
    apply ih (ρ := ρ.cons) (e := b) ?_ rfl
    intro i o hi
    cases i with
    | zero => exact hi
    | succ i => exact hρ i o hi
  | ctor hi hl hg ho =>
    cases e <;> cases he
    exact .ctor hi hl hg ho
  | ctorTuple hn =>
    cases e <;> cases he
    exact .ctorTuple hn
  | recursor hp hc hr =>
    cases e <;> cases he
    exact .recursor hp hc hr
  | proj _ ih =>
    obtain ⟨m, rfl, rfl⟩ := lift'_eq_proj he
    exact .proj (ih hρ rfl)
  | delta hd hr =>
    cases e <;> cases he
    exact .delta hd hr
  | sub _ h ih => exact .sub (ih hρ he) h

/-- The new variable's observations are irrelevant to a lifted expression. -/
theorem Obs.lift_iff : Obs D (Sets.cons P S) e.lift o ↔ Obs D S e o := by
  rw [lift_eq_lift']
  constructor
  · intro H
    apply Obs.rename_inv (ρ := Lift.refl.skip) H
    intro i o h
    exact h
  · intro H
    exact Obs.rename (ρ := Lift.refl.skip) (T := Sets.cons P S) H (fun _ _ h => h)

/-- A variable's observation comes from one valuation entry by subsumption. -/
theorem Obs.var_inv (H : Obs D S (.bvar i) o) : ∃ o', S i o' ∧ Ob.Le o' o := by
  generalize he : VExpr.bvar i = e at H
  induction H with
  | var h => cases he; exact ⟨_, h, .refl⟩
  | sub _ h ih => obtain ⟨_, hS, hL⟩ := ih he; exact ⟨_, hS, hL.trans h⟩
  | ctorTuple | recursor | ctor | proj | delta | sort | pi | app | lam => cases he

/-- Push subsumption of an application result back to its function observation. -/
theorem Obs.app_inv (H : Obs D S (.app f a) o) :
    ∃ keys, Obs D S f (.app keys o) ∧ ∀ key ∈ keys, Obs D S a key := by
  generalize he : VExpr.app f a = e at H
  induction H with
  | app hf ha => cases he; exact ⟨_, hf, ha⟩
  | sub _ h ih =>
    obtain ⟨keys, hf, ha⟩ := ih he
    exact ⟨keys, .sub hf (.app id (fun _ h => h) (fun _ _ => .refl) h), ha⟩
  | ctorTuple | recursor | ctor | proj | delta | var | sort | pi | lam => cases he

/-- Expanding `e` to `λ x : A. e x` cannot add an observation that `e` did not
already have. This is deliberately one-way: a root expansion hides a Pi head. -/
theorem Obs.eta_back (H : Obs D S (.lam A (.app e.lift (.bvar 0))) o) : Obs D S e o := by
  classical
  generalize he : VExpr.lam A (.app e.lift (.bvar 0)) = target at H
  induction H generalizing e A with
  | @lam keys S b o A' HB _ =>
    cases he
    obtain ⟨demands, hf, ha⟩ := HB.app_inv
    have hf' := Obs.lift_iff.1 hf
    have hcover : ∀ key ∈ demands, ∃ key' ∈ keys, Ob.Le key' key := by
      intro key hk
      exact (ha key hk).var_inv
    let pick (key : Ob) := if h : key ∈ demands then (hcover key h).choose else key
    have hpick (key) (hk : key ∈ demands) : pick key ∈ keys ∧ Ob.Le (pick key) key := by
      simpa only [pick, dif_pos hk] using (hcover key hk).choose_spec
    exact .sub hf' (.app pick (fun key hk => (hpick key hk).1)
      (fun key hk => (hpick key hk).2) .refl)
  | sub _ h ih => exact .sub (ih he) h
  | ctorTuple | recursor | ctor | proj | delta | var | sort | pi | app => cases he

end Lean4Lean.VEnv.Strengthening.ConstructorObservation
