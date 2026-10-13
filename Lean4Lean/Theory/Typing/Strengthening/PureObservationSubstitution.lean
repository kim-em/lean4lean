import Lean4Lean.Theory.Typing.Strengthening.PureObservationEta

/-! # Substitution and finite support of computational observations

Finite support allows an observation of a substituted body to be abstracted back
into a finite function demand. This supplies backwards beta closure without
normalization or typing hypotheses.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

variable {D : Definitions}

/-- Valuation demands may be supplied by observations of target variables, allowing
subsumption at the boundary of a valuation. -/
theorem Obs.mono_obs (H : Obs D S e o) (hST : ∀ i o, S i o → Obs D T (.bvar i) o) : Obs D T e o := by
  induction H generalizing T with
  | var h => exact hST _ _ h
  | sort => exact .sort
  | pi => exact .pi
  | app _ _ ihf iha => exact .app (ihf hST) (fun key hk => iha key hk hST)
  | @lam keys S b o A _ ih =>
    apply Obs.lam
    apply ih
    intro i o hi
    cases i with
    | zero => exact .var hi
    | succ i =>
      simpa only [VExpr.lift, VExpr.liftN, liftVar, Nat.not_lt_zero, if_false, Nat.add_comm]
        using (Obs.lift_iff (P := fun key => key ∈ keys)).2 (hST i o hi)
  | delta hd hr => exact .delta hd hr
  | sub _ h ih => exact .sub (ih hST) h

theorem Obs.lam_inv (H : Obs D S (.lam A b) o) :
    ∃ keys result, Obs D (Sets.cons (fun key => key ∈ keys) S) b result ∧
      Ob.Le (.app keys result) o := by
  generalize he : VExpr.lam A b = e at H
  induction H with
  | lam hb => cases he; exact ⟨_, _, hb, .refl⟩
  | sub _ h ih => obtain ⟨_, _, hb, hl⟩ := ih he; exact ⟨_, _, hb, hl.trans h⟩
  | delta | var | sort | pi | app => cases he

theorem Obs.sort_inv (H : Obs D S (.sort u) o) : Ob.Le .sort o := by
  generalize he : VExpr.sort u = e at H
  induction H with
  | sort => exact .refl
  | sub _ h ih => exact (ih he).trans h
  | delta | var | pi | lam | app => cases he

theorem Obs.pi_inv (H : Obs D S (.forallE A B) o) : Ob.Le .pi o := by
  generalize he : VExpr.forallE A B = e at H
  induction H with
  | pi => exact .refl
  | sub _ h ih => exact (ih he).trans h
  | delta | var | sort | lam | app => cases he

/-- Constant observations are independent of the surrounding variable valuation. -/
theorem Obs.const_valuation (H : Obs D S (.const c ls) o) : Obs D T (.const c ls) o := by
  generalize he : VExpr.const c ls = e at H
  induction H with
  | delta hd hr => cases he; exact .delta hd hr
  | sub _ h ih => exact .sub (ih he) h
  | var | sort | pi | lam | app => cases he

theorem Obs.proj_false (H : Obs D S (.proj s i m) o) : False := by
  generalize he : VExpr.proj s i m = e at H
  induction H with
  | sub _ _ ih => exact ih he
  | delta | var | sort | pi | lam | app => cases he

/-- An observation of a substituted expression is an observation of its open
syntax under the valuation supplied by the substituted expressions. -/
theorem Obs.subst_inv (H : Obs D S (e.subst σ) o) : Obs D (fun i key => Obs D S (σ i) key) e o := by
  induction e generalizing S σ o with
  | bvar i => exact .var H
  | sort => exact .sub .sort H.sort_inv
  | const => exact H.const_valuation
  | proj => exact H.proj_false.elim
  | forallE => exact .sub .pi H.pi_inv
  | app f a ihf iha =>
    obtain ⟨keys, hf, ha⟩ := H.app_inv
    exact .app (ihf hf) (fun key hk => iha (ha key hk))
  | lam A b _ ihb =>
    obtain ⟨keys, result, hb, hl⟩ := H.lam_inv
    apply Obs.sub (Obs.lam ?_) hl
    apply (ihb hb).mono_obs
    intro i key hi
    cases i with
    | zero =>
      obtain ⟨key', hkey', hle⟩ := hi.var_inv
      exact .sub (.var hkey') hle
    | succ i => exact .var (Obs.lift_iff.1 hi)

/-- Each derivation consults only finitely many variable observations. -/
theorem Obs.finite_support (H : Obs D S e o) :
    ∃ support : List (Nat × Ob), (∀ p ∈ support, S p.1 p.2) ∧
      Obs D (fun i key => (i, key) ∈ support) e o := by
  classical
  induction H with
  | @var S i o h =>
    exact ⟨[(i,o)], by simpa using h, .var (by simp)⟩
  | sort => exact ⟨[], by simp, .sort⟩
  | pi => exact ⟨[], by simp, .pi⟩
  | delta hd hr => exact ⟨[], by simp, .delta hd hr⟩
  | @app S f keys o a _ _ ihf iha =>
    obtain ⟨sf, hsf, hf⟩ := ihf
    let supports (key : Ob) := if hk : key ∈ keys then (iha key hk).choose else []
    have hsupports (key) (hk : key ∈ keys) :
        (∀ p ∈ supports key, S p.1 p.2) ∧ Obs D (fun i o => (i,o) ∈ supports key) a key := by
      simpa only [supports, dif_pos hk] using (iha key hk).choose_spec
    refine ⟨sf ++ keys.flatMap supports, ?_, .app (keys := keys) ?_ ?_⟩
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hsf p hp
      · obtain ⟨key, hk, hp⟩ := List.mem_flatMap.1 hp
        exact (hsupports key hk).1 p hp
    · exact hf.mono (fun i o h => List.mem_append_left _ h)
    · intro key hk
      exact (hsupports key hk).2.mono (fun i o h =>
        List.mem_append_right _ (List.mem_flatMap.2 ⟨key, hk, h⟩))
  | @lam keys S b o A _ ih =>
    obtain ⟨support, hs, hb⟩ := ih
    let tail := support.filterMap fun p => match p.1 with
      | 0 => none
      | i+1 => some (i, p.2)
    refine ⟨tail, ?_, .lam (hb.mono ?_)⟩
    · intro p hp
      obtain ⟨⟨i, key⟩, hi, hp⟩ := List.mem_filterMap.1 hp
      cases i with
      | zero => cases hp
      | succ i => cases hp; exact hs _ hi
    · intro i key hi
      cases i with
      | zero => exact hs _ hi
      | succ i => exact List.mem_filterMap.2 ⟨(i+1,key), hi, rfl⟩
  | sub _ h ih =>
    obtain ⟨support, hs, he⟩ := ih
    exact ⟨support, hs, .sub he h⟩

/-- A possibly infinite head valuation can be replaced by the finite demands used
by one derivation, while the tail valuation is left unchanged. -/
theorem Obs.compact_head (H : Obs D (Sets.cons P S) e o) :
    ∃ keys : List Ob, (∀ key ∈ keys, P key) ∧ Obs D (Sets.cons (fun key => key ∈ keys) S) e o := by
  obtain ⟨support, hs, he⟩ := H.finite_support
  let keys := support.filterMap fun p => if p.1 = 0 then some p.2 else none
  refine ⟨keys, ?_, he.mono ?_⟩
  · intro key hk
    obtain ⟨⟨i, key'⟩, hi, heq⟩ := List.mem_filterMap.1 hk
    dsimp only at heq
    split at heq <;> try contradiction
    subst i
    cases heq
    exact hs _ hi
  · intro i key hi
    cases i with
    | zero => exact List.mem_filterMap.2 ⟨(0,key), hi, by simp⟩
    | succ i => exact hs _ hi

/-- An observation after substitution gives a finite abstraction demand and
observations of the argument satisfying every one of those demands. -/
theorem Obs.inst_inv (H : Obs D S (b.inst a) o) :
    ∃ keys : List Ob, Obs D (Sets.cons (fun key => key ∈ keys) S) b o ∧ ∀ key ∈ keys, Obs D S a key := by
  rw [inst_eq] at H
  have hb := H.subst_inv
  have hb' : Obs D (Sets.cons (fun key => Obs D S a key) S) b o := by
    apply hb.mono_obs
    intro i key hi
    cases i with
    | zero => exact .var hi
    | succ i =>
      obtain ⟨key', hk, hle⟩ := hi.var_inv
      exact .sub (.var hk) hle
  obtain ⟨keys, hk, hb⟩ := hb'.compact_head
  exact ⟨keys, hb, hk⟩

/-- Root beta contraction cannot add a finite computational observation. -/
theorem Obs.beta_back (H : Obs D S (b.inst a) o) : Obs D S (.app (.lam A b) a) o := by
  obtain ⟨keys, hb, ha⟩ := H.inst_inv
  exact .app (.lam hb) ha

end Lean4Lean.VEnv.Strengthening.PureObservation
