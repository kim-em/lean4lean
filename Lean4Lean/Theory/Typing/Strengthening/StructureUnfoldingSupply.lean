import Lean4Lean.Theory.Typing.Strengthening.StructureHeadComputation

/-! # Supplying a closed structure unfolding

At full saturation the closed lambda program becomes the rule RHS on projections
of the supplied major. On an actual constructor major, these projections compute
to the original fields and the ignored parameter captures can be restored.
-/
namespace Lean4Lean.VEnv.Strengthening.ClosedStructure
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature
open PureObservation (Definitions Compute ProjectionCompute CheckFromTyping)

/-- Instantiation commutes with deterministic capture selection. -/
theorem spineCaptures_instOuter {c : Name} {n : Nat} (args values : List VExpr)
    (hlen : args.length = n) (p : ((Pattern.const c).varN n).Path) :
    (spineCaptures args hlen p).instOuter values =
      spineCaptures (args.map (·.instOuter values)) (by simpa using hlen) p := by
  simp only [spineCaptures, List.getElem_map]

/-- The recursor-prefix variables instantiate to the supplied prefix arguments. -/
theorem prefix_vars_instOuter (hlen : args.length = n) :
    (vars n 1).map (·.instOuter (args ++ [major])) = args := by
  rw [vars_eq_bvarRange_add, instOuter_bvarRange _ _ _ (by omega) (by simp [hlen])]
  simp only [List.length_append, List.length_singleton, hlen, Nat.sub_self, List.drop_zero]
  rw [← hlen, List.take_append_length]

/-- The innermost variable instantiates to the supplied major. -/
theorem major_instOuter : (VExpr.bvar 0).instOuter (args ++ [major]) = major := by
  rw [instOuter_bvar _ (by simp)]
  simp

/-- Substitution through a projection preserves its family and index. -/
theorem projection_instOuter {family : Name} :
    (VExpr.proj family index major).instOuter args = .proj family index (major.instOuter args) := by
  simp only [instOuter_eq_subst, VExpr.subst]

/-- The projection program after supplying all recursor arguments. -/
def suppliedBody (data : RecursorData) (info : VProjectionInfo) (levels : List VLevel)
    (rhs : (pattern data info).RHS) (args : List VExpr) (hlen : args.length = data.majorOffset)
    (major : VExpr) : VExpr :=
  Pattern.RHS.apply (p := pattern data info) levels (Sum.elim
    (spineCaptures (c := data.name) args hlen)
    (spineCaptures (c := info.ctorName) (n := info.nparams + info.numFields)
      (List.replicate info.nparams (.sort .zero) ++
        (List.range info.numFields).map (fun i => .proj (family data) i major)) (by simp))) rhs

set_option backward.isDefEq.respectTransparency false in
/-- Full beta substitution has exactly the projected-rule syntax above. -/
theorem body_instOuter (hlen : args.length = data.majorOffset) :
    (body data info levels rhs).instOuter (args ++ [major]) =
      suppliedBody data info levels rhs args hlen major := by
  unfold body suppliedBody
  simp only [instOuter_eq_subst, Pattern.RHS.subst_apply]
  congr 1
  funext p
  cases p with
  | inl p =>
    simp only [Sum.elim]
    rw [← instOuter_eq_subst, spineCaptures_instOuter]
    simp only [prefix_vars_instOuter hlen]
  | inr p =>
    simp only [Sum.elim]
    rw [← instOuter_eq_subst, spineCaptures_instOuter]
    simp only [List.map_append, List.map_replicate, instOuter_sort, List.map_map,
      Function.comp_def, projection_instOuter, major_instOuter]

variable [Params]

/-- Supply arbitrary raw arguments to the closed structure equation and beta
reduce to its projected-rule program. The arguments need not be typed. -/
theorem supplied_compute
    {r : (pattern data info).RHS × (pattern data info).Check}
    (hr : RecursorRegistered Params.env data) (hw : ∀ l ∈ levels, l.WF Params.univs)
    (hl : levels.length = data.uvars) (hi : Params.env.projections (family data) info)
    (hn : info.nindices = 0) (hz : Admissible Params.env Params.univs data info levels)
    (hp : Params.Pat _ r) (hc : CheckFromTyping Params.env Params.univs _ r levels)
    (ha : args.length = data.majorOffset) :
    Compute (definitions D) (.app (mkApps (.const data.name levels) args) major)
      (suppliedBody data info levels r.1 args ha major) := by
  have H := saturated_compute (D := D) hr hw hl hi hn hz hp hc
    (args := args ++ [major]) (by simp [ha])
  simpa only [mkApps_append, mkApps_cons, mkApps_nil, body_instOuter ha] using H

/-- Computational capture paths extend through every pattern RHS. -/
theorem projection_apply_pat {p : Pattern} (r : p.RHS)
    {levels : List VLevel} {captures captures' : p.Path → VExpr}
    (H : ∀ p, ProjectionCompute D (captures p) (captures' p)) :
    ProjectionCompute D (r.apply levels captures) (r.apply levels captures') := by
  induction r with
  | fixed => exact .base .refl
  | var => exact H _
  | app _ _ ihf iha => exact .app ihf iha

/-- Pointwise computation of a spine's arguments computes all its captures. -/
theorem projection_spineCaptures {c : Name} {n : Nat}
    (H : List.Forall₂ (ProjectionCompute D) args args')
    (hlen : args.length = n) (hlen' : args'.length = n) (p : ((Pattern.const c).varN n).Path) :
    ProjectionCompute D (spineCaptures args hlen p) (spineCaptures args' hlen' p) :=
  H.getElem_of _ (hlen ▸ (spineIndex p).isLt) (hlen' ▸ (spineIndex p).isLt)

/-- Projecting a saturated constructor recovers its entire field suffix while
leaving the dummy parameter captures fixed. -/
theorem projected_fields_compute {family : Name} (hi : Params.env.projections family info)
    (hlen : args.length = info.nparams + info.numFields) :
    List.Forall₂ (ProjectionCompute D)
      (List.replicate info.nparams (.sort .zero) ++
        (List.range info.numFields).map (fun i => .proj family i (mkApps (.const info.ctorName ls) args)))
      (List.replicate info.nparams (.sort .zero) ++ args.drop info.nparams) := by
  apply List.forall₂_of_getElem (by simp [hlen])
  intro j hj hj'
  by_cases hparam : j < info.nparams
  · simp only [List.getElem_append_left (as := List.replicate info.nparams (VExpr.sort .zero)) (i := j) (by simpa using hparam), List.getElem_replicate]
    exact .base .refl
  · have hjfield : j - info.nparams < info.numFields := by
      simp only [List.length_append, List.length_replicate, List.length_map, List.length_range] at hj
      omega
    simp only [List.getElem_append_right (as := List.replicate info.nparams (VExpr.sort .zero))
      (i := j) (by simp; omega), List.length_replicate, List.getElem_map, List.getElem_range,
      List.getElem_drop]
    exact .projIota hi hlen (List.getElem?_eq_getElem (by omega))

set_option backward.isDefEq.respectTransparency false in
/-- Every iota match for this registered structure recursor is simulated by its
closed equation, beta, and constructor projections. This is a raw computation
statement; it requires no typing of the matched source or captured arguments. -/
theorem iota_compute
    {r : (pattern data info).RHS × (pattern data info).Check}
    {captures : (pattern data info).Path → VExpr}
    (hr : RecursorRegistered Params.env data) (hw : ∀ l ∈ levels, l.WF Params.univs)
    (hl : levels.length = data.uvars) (hi : Params.env.projections (family data) info)
    (hn : info.nindices = 0) (hz : Admissible Params.env Params.univs data info levels)
    (hp : Params.Pat _ r) (hc : CheckFromTyping Params.env Params.univs _ r levels)
    (hm : (pattern data info).Matches source levels captures) :
    ProjectionCompute (definitions D) source (r.1.apply levels captures) := by
  cases hm with
  | app hrec hctor =>
    rename_i ctorLevels recCaptures ctorCaptures
    obtain ⟨args, ha, rfl, _⟩ := Pattern.matches_varN_const_inv hrec
    obtain ⟨ctorArgs, hca, rfl, _⟩ := Pattern.matches_varN_const_inv hctor
    have hrecEq := (Pattern.matches_determ hrec (spineCaptures_match args ha levels)).2
    rw [hrecEq]
    let dummyArgs := List.replicate info.nparams (VExpr.sort .zero) ++ ctorArgs.drop info.nparams
    have hdlen : dummyArgs.length = info.nparams + info.numFields := by simp [dummyArgs, hca]
    have hdummy := spineCaptures_match (c := info.ctorName) dummyArgs hdlen []
    have hactual : ((Pattern.const info.ctorName).varN (info.nparams + info.numFields)).Matches
        (mkApps (.const info.ctorName ctorLevels) (ctorArgs.take info.nparams ++ ctorArgs.drop info.nparams))
        ctorLevels ctorCaptures := by
      simpa only [List.take_append_drop] using hctor
    have he := (Params.pat_iota_params hp hi rfl hactual hdummy
      (by simp [hca]) (by simp)).1 levels (spineCaptures args ha)
    rw [he]
    apply ProjectionCompute.trans (.base (supplied_compute hr hw hl hi hn hz hp hc ha))
    unfold suppliedBody
    apply projection_apply_pat
    intro p
    cases p with
    | inl => exact .base .refl
    | inr p =>
      exact projection_spineCaptures (projected_fields_compute hi hca) (by simp) hdlen p

/-- The simulation embeds structure iota directly into the existing mixed
observation model; the model needs no new constructor tests for structures. -/
theorem iota_etaCompute
    {r : (pattern data info).RHS × (pattern data info).Check}
    {captures : (pattern data info).Path → VExpr}
    (hr : RecursorRegistered Params.env data) (hw : ∀ l ∈ levels, l.WF Params.univs)
    (hl : levels.length = data.uvars) (hi : Params.env.projections (family data) info)
    (hn : info.nindices = 0) (hz : Admissible Params.env Params.univs data info levels)
    (hp : Params.Pat _ r) (hc : CheckFromTyping Params.env Params.univs _ r levels)
    (hm : (pattern data info).Matches source levels captures) :
    ConstructorObservation.EtaCompute (definitions D) source (r.1.apply levels captures) :=
  .compute (iota_compute hr hw hl hi hn hz hp hc hm)

omit [Params] in
/-- An enabled concrete structure-iota rule supplies its own uniform check
certificate. The remaining premises concern registry data, universe levels, and closed
projection admissibility. -/
theorem concrete_iota_etaCompute {env : VEnv} (henv : env.WF)
    {r : (pattern data info).RHS × (pattern data info).Check}
    {captures : (pattern data info).Path → VExpr}
    (hr : RecursorRegistered env data) (hw : ∀ l ∈ levels, l.WF U)
    (hl : levels.length = data.uvars) (hi : env.projections (family data) info)
    (hn : info.nindices = 0) (hz : Admissible env U data info levels)
    (hp : ConcretePattern env _ r)
    (hc : r.2.OK (env.IsDefEqU U Γ) levels captures)
    (hm : (pattern data info).Matches source levels captures) :
    @ConstructorObservation.EtaCompute (henv.params U) (@definitions (henv.params U) D)
      source (r.1.apply levels captures) := by
  letI := henv.params U
  exact iota_etaCompute hr hw hl hi hn hz hp (PureObservation.ConcretePattern.checkFromTyping henv hp hc) hm

end Lean4Lean.VEnv.Strengthening.ClosedStructure
