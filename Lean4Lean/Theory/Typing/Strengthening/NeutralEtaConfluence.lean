import Lean4Lean.Theory.Typing.Strengthening.PrefixConfluence
import Lean4Lean.Theory.Typing.Strengthening.NeutralEtaCompletion
import Lean4Lean.Theory.Typing.Strengthening.SymmetricPrefixEtaPhase

/-! # Joining independently computed neutral structure majors

Exact computational confluence aligns all finitely many copies introduced by
structure eta. The major may compute indefinitely and its copies may take
different finite paths; the only excluded case is exposing its constructor.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

private abbrev actualD : Definitions :=
  RegisteredStructure.definitions (Definitions.ofEnv env univs henv)

/-- Every finite collection of reducts of a typed source has a common reduct.
No normalization or bound on the supplied paths is required. -/
theorem PrefixCompute.finite_common_target {xs : List VExpr}
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A)
    (paths : ∀ x ∈ xs, PrefixCompute actualD Γ a x) :
    ∃ out, PrefixCompute actualD Γ a out ∧ ∀ x ∈ xs, PrefixCompute actualD Γ x out := by
  induction xs with
  | nil => exact ⟨a, .refl, by simp⟩
  | cons x xs ih =>
    obtain ⟨middle, HM, HX⟩ := ih (fun y hy => paths y (List.mem_cons_of_mem _ hy))
    obtain ⟨out, HO, HM'⟩ := (paths x (List.mem_cons_self ..)).confluent hcon hΓ ha HM
    refine ⟨out, HM.trans HM', ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact HO
    · exact (HX y hy).trans HM'

/-- Without constructor exposure, every computed field retains a projection
of a computed major. The major need not be computationally fixed. -/
theorem PrefixCompute.neutral_projection_trace
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hi : env.projections family info)
    (hn : ∀ levels args, ¬ PrefixCompute D Γ major (VExpr.mkApps (.const info.ctorName levels) args))
    (R : PrefixCompute D Γ (.proj family index major) out) :
    ∃ major', PrefixCompute D Γ major major' ∧ out = .proj family index major' := by
  rcases R.projection_trace hcon with H | ⟨info', levels, args, field, hi', HM, _, _, _⟩
  · exact H
  · cases henv.ordered.projections_unique hi hi'
    exact (hn levels args HM).elim

/-- Independent computations of a neutral major's projected fields can all
continue to projections of one common computed major. -/
theorem neutral_fields_common_major
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hm : env.HasType univs Γ major T)
    (hi : env.projections family info)
    (hn : ∀ levels args, ¬ PrefixCompute actualD Γ major (VExpr.mkApps (.const info.ctorName levels) args))
    (HF : List.Forall₂ (PrefixCompute actualD Γ)
      ((List.range info.numFields).map (fun i => VExpr.proj family i major)) fields) :
    ∃ common, PrefixCompute actualD Γ major common ∧
      List.Forall₂ (PrefixCompute actualD Γ) fields
        ((List.range info.numFields).map (fun i => VExpr.proj family i common)) := by
  classical
  have hlen : fields.length = info.numFields := by simpa using HF.length_eq.symm
  have traces (i : Fin info.numFields) :
      ∃ major', PrefixCompute actualD Γ major major' ∧
        fields[i.val]'(by omega) = .proj family i major' := by
    have H := HF.getElem_of i.val (by simp) (by omega)
    simp only [List.getElem_map, List.getElem_range] at H
    exact H.neutral_projection_trace hcon hi hn
  let majors := List.ofFn (fun i => (traces i).choose)
  obtain ⟨common, HM, HC⟩ := PrefixCompute.finite_common_target hcon hΓ hm (xs := majors) (by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact (traces i).choose_spec.1)
  refine ⟨common, HM, List.forall₂_of_getElem (by simpa using hlen) ?_⟩
  intro i hi hi'
  have hin : i < info.numFields := by omega
  have path := HC _ (List.mem_ofFn.2 ⟨⟨i, hin⟩, rfl⟩)
  simp only [List.getElem_map, List.getElem_range]
  rw [(traces ⟨i, hin⟩).choose_spec.2]
  exact .proj path

/-- Computation after structure eta at any non-constructor-exposing major has
a computational join with a single later eta expansion. All duplicated major
paths are unrestricted finite paths and are aligned by exact confluence. -/
theorem neutral_eta_compute_join
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : params.length = info.nparams)
    (hx : info.nindices = 0)
    (hm : env.HasType univs Γ major (VExpr.mkApps (.const family levels) params))
    (hc : env.HasType univs Γ (structExpand family info levels params major)
      (VExpr.mkApps (.const family levels) params))
    (hn : ∀ levels args, ¬ PrefixCompute actualD Γ major (VExpr.mkApps (.const info.ctorName levels) args))
    (R : PrefixCompute actualD Γ (structExpand family info levels params major) out) :
    ∃ common target, PrefixCompute actualD Γ major common ∧ PrefixCompute actualD Γ out target ∧
      TypedEtaExpansion Γ common target := by
  have hs := RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)
  obtain ⟨args, rfl, HA⟩ := R.rigid_spine_paths (henv.projectionCtorRigid hi)
    (fun _ _ => RegisteredStructure.definitions_ofEnv_no_rigid (henv.projectionCtorRigid hi))
  have HP : List.Forall₂ (PrefixCompute actualD Γ) params (args.take params.length) := by
    simpa only [List.take_left] using List.forall₂_take HA params.length
  have HF : List.Forall₂ (PrefixCompute actualD Γ)
      ((List.range info.numFields).map (fun i => VExpr.proj family i major)) (args.drop params.length) := by
    simpa only [List.drop_left] using List.forall₂_drop HA params.length
  obtain ⟨common, HM, HFields⟩ := neutral_fields_common_major hcon hΓ hm hi hn HF
  have hp' := HP.length_eq.symm.trans hp
  obtain ⟨u, hfamily⟩ := hm.isType henv hΓ
  have HPType := (PrefixCompute.mkApps_paths (D := actualD) (Γ := Γ)
    (f := .const family levels) .refl HP).simAt hs hΓ _ hfamily
  have hm' := ((HM.simAt hs hΓ _ hm).hasType.2).defeqU_r henv hΓ ⟨_, HPType⟩
  have hc' := (StructureReplay.expansion_typed_iff henv hΓ hi hp' hx hm').2
    ((StructureReplay.expansion_typed_iff henv hΓ hi hp hx hm).1 hc)
  refine ⟨common, structExpand family info levels (args.take params.length) common, HM, ?_,
    .structEta hi hp' hx hm' hc'⟩
  have HR : List.Forall₂ (PrefixCompute actualD Γ) (args.take params.length) (args.take params.length) :=
    List.Forall₂.rfl (fun _ _ => .refl)
  simpa only [structExpand, List.take_append_drop] using
    (PrefixCompute.mkApps_paths (f := .const info.ctorName levels) .refl
      (HR.append' HFields))

/-- Computing the major computes all copies in its structure expansion. -/
theorem PrefixCompute.structExpand_major (R : PrefixCompute D Γ major major') :
    PrefixCompute D Γ (structExpand family info levels params major)
      (structExpand family info levels params major') := by
  have HP : List.Forall₂ (PrefixCompute D Γ) params params := List.Forall₂.rfl (fun _ _ => .refl)
  have HF : List.Forall₂ (PrefixCompute D Γ)
      ((List.range info.numFields).map (fun i => VExpr.proj family i major))
      ((List.range info.numFields).map (fun i => VExpr.proj family i major')) := by
    apply List.forall₂_of_getElem (by simp)
    intro i hi hi'
    simpa only [List.getElem_map, List.getElem_range] using PrefixCompute.proj (s := family) (i := i) R
  exact PrefixCompute.mkApps_paths .refl (HP.append' HF)

/-- If the major can expose a constructor at the eta root's own parameters
and universes, arbitrary computation after eta joins computation of the major
itself. Constructor exposure need not occur along any of the supplied copies. -/
theorem structure_eta_compute_join_of_constructor
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : params.length = info.nparams)
    (hf : fields.length = info.numFields)
    (hc : env.HasType univs Γ (structExpand family info levels params major) T)
    (HM : PrefixCompute actualD Γ major (VExpr.mkApps (.const info.ctorName levels) (params ++ fields)))
    (R : PrefixCompute actualD Γ (structExpand family info levels params major) out) :
    ∃ result, PrefixCompute actualD Γ major result ∧ PrefixCompute actualD Γ out result := by
  obtain ⟨target, HS, HE⟩ := constructor_eta_compute_join (D := actualD) (Γ := Γ) hi hp hf
    (fun _ _ => RegisteredStructure.definitions_ofEnv_no_rigid (henv.projectionCtorRigid hi))
    (PrefixCompute.refl (e := structExpand family info levels params
      (VExpr.mkApps (.const info.ctorName levels) (params ++ fields))))
  have HX := HM.structExpand_major (family := family) (info := info) (levels := levels) (params := params)
  obtain ⟨result, HO, HT⟩ := R.confluent hcon hΓ hc (HX.trans HE)
  exact ⟨result, (HM.trans HS).trans HT, HO⟩

/-- The neutral root join has the symmetric phase required by the equality
coverage route, without fixedness, canonical Eq or a witnessed front. -/
theorem neutral_eta_compute_symmetric_phase
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : params.length = info.nparams)
    (hx : info.nindices = 0)
    (hm : env.HasType univs Γ major (VExpr.mkApps (.const family levels) params))
    (hc : env.HasType univs Γ (structExpand family info levels params major)
      (VExpr.mkApps (.const family levels) params))
    (hn : ∀ levels args, ¬ PrefixCompute actualD Γ major (VExpr.mkApps (.const info.ctorName levels) args))
    (R : PrefixCompute actualD Γ (structExpand family info levels params major) out) :
    PrefixEtaJoin actualD Γ major out := by
  obtain ⟨common, target, HM, HO, HE⟩ := neutral_eta_compute_join hcon hΓ hi hp hx hm hc hn R
  have hs := RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)
  exact ⟨common, target, HM, HO, target, target, HE, .refl,
    .refl (HE.simAt hΓ _ (HM.simAt hs hΓ _ hm).hasType.2).hasType.2⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
