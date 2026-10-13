import Lean4Lean.Theory.Typing.Strengthening.ConstructorObservationSubstitution

/-! # Pattern computation preserves finite observations backwards

Projection rules consume finite field demands. An arbitrary iota RHS observation
supplies finite demands on its captures and a uniform operational certificate;
non-projection constructor tuples pass these demands to the recursor.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
open PureObservation (Definitions Compute ProjectionCompute PatternCompute CheckFromTyping)
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
  | ctorTuple hn => exact .ctorTuple hn
  | recursor hp hcheck hr => exact .recursor hp hcheck hr
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

/-- Observing an instantiated RHS uses finitely many observations of each
capture, and these demands suffice for operational realization with ANY captures. -/
theorem Obs.apply_pat_inv {p : Pattern} {r : p.RHS} {levels : List VLevel}
    {captures : p.Path → VExpr} (H : Obs D S (r.apply levels captures) o) :
    ∃ K : p.Path → List Ob,
      (∀ p key, key ∈ K p → Obs D S (captures p) key) ∧ RHSRealizes D r levels K o := by
  classical
  induction r generalizing o with
  | fixed body hclosed =>
    refine ⟨fun _ => [], by simp, ?_⟩
    intro captures' _
    have h := (H.closed_valuation (T := fun _ _ => False) (hclosed.instL)).realizes (σ := .id) (fun _ _ h => h.elim)
    simpa only [subst_id, Pattern.RHS.apply] using h
  | var path =>
    refine ⟨fun p => if p = path then [o] else [], ?_, ?_⟩
    · intro p key hk
      by_cases hp : p = path
      · subst p; simp at hk; subst key; exact H
      · simp [hp] at hk
    · intro captures' hc
      exact hc path o (by simp)
  | app f a ihf iha =>
    obtain ⟨keys, hf, ha⟩ := H.app_inv
    obtain ⟨Kf, hKf, hRf⟩ := ihf hf
    let Ka (key : Ob) : p.Path → List Ob :=
      if hk : key ∈ keys then (iha (ha key hk)).choose else fun _ => []
    have hKa (key) (hk : key ∈ keys) :
        (∀ p o, o ∈ Ka key p → Obs D S (captures p) o) ∧ RHSRealizes D a levels (Ka key) key := by
      simpa only [Ka, dif_pos hk] using (iha (ha key hk)).choose_spec
    refine ⟨fun p => Kf p ++ keys.flatMap (fun key => Ka key p), ?_, ?_⟩
    · intro p o ho
      rcases List.mem_append.1 ho with ho | ho
      · exact hKf p o ho
      · obtain ⟨key, hk, ho⟩ := List.mem_flatMap.1 ho
        exact (hKa key hk).1 p o ho
    · intro captures' hc
      have hfn := hRf captures' (fun p key hk => hc p key (List.mem_append_left _ hk))
      simp only [Realizes] at hfn
      exact hfn _ (fun key hk => (hKa key hk).2 captures' (fun p o ho =>
        hc p o (List.mem_append_right _ (List.mem_flatMap.2 ⟨key, hk, ho⟩))))

/-- An ordinary constructor spine supplies all its argument demands together. -/
theorem Obs.ctor_tuple {ctor : Name} (hn : NotProjectionCtor ctor)
    (ha : List.Forall₂ (fun K a => ∀ key ∈ K, Obs D S a key) keys args) :
    Obs D S (mkApps (.const ctor levels) args) (.ctor ctor keys) :=
  (Obs.ctorTuple hn).wrap_elim ha

/-- Every enabled iota rule whose major is not a projection constructor preserves
finite observations backwards. The rule RHS is arbitrary, including quotient RHSs. -/
theorem Obs.iota_back {recursor ctor : Name} {major fields : Nat}
    {r : (SimplePattern.iota recursor major ctor fields).toPattern.RHS ×
      (SimplePattern.iota recursor major ctor fields).toPattern.Check}
    {captures : (SimplePattern.iota recursor major ctor fields).toPattern.Path → VExpr}
    (hp : Params.Pat _ r) (hc : CheckFromTyping Params.env Params.univs _ r levels)
    (hm : (SimplePattern.iota recursor major ctor fields).toPattern.Matches e levels captures)
    (hn : NotProjectionCtor ctor) (H : Obs D S (r.1.apply levels captures) o) : Obs D S e o := by
  obtain ⟨K, hK, hR⟩ := H.apply_pat_inv
  obtain ⟨recArgs, ctorArgs, ctorLevels, hrlen, hclen, rfl, hrg, hcg⟩ :=
    SimplePattern.iota_matches_inv hm
  have hrec := (spineKeys_demands hrlen hrg).2 (fun p key hk => hK (.inl p) key hk)
  have hctor := (spineKeys_demands hclen hcg).2 (fun p key hk => hK (.inr p) key hk)
  have hf := (Obs.recursor hp hc hR (S := S)).wrap_elim hrec
  rw [mkApps_append]
  apply Obs.app hf
  intro key hk
  simp only [List.mem_singleton] at hk
  subst key
  exact Obs.ctor_tuple hn hctor

end Lean4Lean.VEnv.Strengthening.ConstructorObservation
