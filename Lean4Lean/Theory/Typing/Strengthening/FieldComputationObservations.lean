import Lean4Lean.Theory.Typing.Strengthening.FieldObservationSubstitution

/-! # Projection computation preserves finite observations backwards

A selected constructor argument supplies a finite field demand. The constructor's
curried demands can be chosen using only the selected argument's observation;
there is no obligation to observe parameters or unrelated fields.
-/
namespace Lean4Lean.VEnv.Strengthening.FieldObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
open PureObservation (Definitions Compute ProjectionCompute)
variable [Params]
variable {D : Definitions}

/-- Only valuation entries for syntactically available variables matter. -/
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
  | ctor hi hl hg ho => exact .ctor hi hl hg ho
  | proj _ ih => exact .proj (ih hc hST)
  | sub _ h ih => exact .sub (ih hc hST) h

/-- Closed bodies can be interpreted under the empty valuation. -/
theorem Obs.closed_valuation (H : Obs D S e o) (hc : e.Closed) : Obs D T e o :=
  H.mono_closed hc (fun _ hi => (Nat.not_lt_zero _ hi).elim)

/-- Declaration unfolding cannot introduce an observation. -/
theorem Obs.delta_back (hd : D.unfolds c ls rhs) (H : Obs D S rhs o) :
    Obs D S (.const c ls) o := .delta hd (H.closed_valuation (D.closed hd))

/-- Supply a complete finite argument spine to a curried observation. -/
theorem Obs.wrap_elim (H : Obs D S f (Ob.wrap keys result))
    (hargs : List.Forall₂ (fun K a => ∀ key ∈ K, Obs D S a key) keys args) :
    Obs D S (mkApps f args) result := by
  induction hargs generalizing f with
  | nil => exact H
  | cons ha _ ih => exact ih (.app H ha)

/-- A field observation of a constructor needs observations only of the selected
field. Every unrelated argument can receive an empty demand list. -/
theorem Obs.ctor_spine (hinfo : Params.env.projections s info)
    (hlen : args.length = info.nparams + info.numFields)
    (hget : args[info.nparams + i]? = some field) (H : Obs D S field o) :
    Obs D S (mkApps (.const info.ctorName ls) args) (.field s i o) := by
  classical
  let keys := args.map fun a => if a = field then [o] else []
  have hkeys : keys[info.nparams + i]? = some [o] := by
    simp [keys, List.getElem?_map, hget]
  have hc : Obs D S (.const info.ctorName ls) (Ob.wrap keys (.field s i o)) :=
    .ctor hinfo (by simp [keys, hlen]) hkeys (by simp)
  apply hc.wrap_elim
  change List.Forall₂ _ (args.map _) args
  clear hc hkeys keys hlen hget
  induction args with
  | nil => exact .nil
  | cons a args ih =>
    apply List.Forall₂.cons ?_ ih
    intro key hk
    by_cases ha : a = field
    · subst a
      simp at hk
      subst key
      exact H
    · simp [ha] at hk

/-- A root saturated projection contraction cannot add an observation. -/
theorem Obs.projIota_back (hinfo : Params.env.projections s info)
    (hlen : args.length = info.nparams + info.numFields)
    (hget : args[info.nparams + i]? = some field) (H : Obs D S field o) :
    Obs D S (.proj s i (mkApps (.const info.ctorName ls) args)) o :=
  .proj (H.ctor_spine hinfo hlen hget)

/-- Beta/delta computation is backwards sound also for field observations. -/
theorem compute_obs_back (R : Compute D e out) (H : Obs D S out o) : Obs D S e o := by
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
  | proj _ ih => exact .proj (ih H.proj_inv)

/-- All finite beta/delta/projection paths preserve observations backwards. -/
theorem projection_obs_back (R : ProjectionCompute D e out) (H : Obs D S out o) : Obs D S e o := by
  induction R generalizing S o with
  | base h => exact compute_obs_back h H
  | trans _ _ ih1 ih2 => exact ih1 (ih2 H)
  | projIota hi hl hg => exact H.projIota_back hi hl hg
  | app _ _ ihf iha =>
    obtain ⟨keys, hf, ha⟩ := H.app_inv
    exact .app (ihf hf) (fun key hk => iha (ha key hk))
  | lam _ _ _ ihb =>
    obtain ⟨keys, result, hb, hl⟩ := H.lam_inv
    exact .sub (.lam (ihb hb)) hl
  | forallE => exact .sub .pi H.pi_inv
  | proj _ ih => exact .proj (ih H.proj_inv)

end Lean4Lean.VEnv.Strengthening.FieldObservation
