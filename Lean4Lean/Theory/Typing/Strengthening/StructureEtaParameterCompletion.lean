import Lean4Lean.Theory.Typing.Strengthening.ConstructorParameterChange

/-! # Completing every structure eta root up to explicit parameter change

Computational confluence aligns all fields. The remaining difference is an
actual constructor parameter change, whose soundness and subsequent computation
transport are proved separately. No phase certificates for data parameters are
assumed. This is a root theorem; compatible terminal closure remains to be built.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

private abbrev actualD : Definitions :=
  RegisteredStructure.definitions (Definitions.ofEnv env univs henv)

/-- In the constructor-exposing case, both sides compute to the same fields.
Their sole residual is a typed change of constructor parameters and universes.
All parameters may be data, and their conversions require no phase witnesses. -/
theorem structure_eta_compute_parameter_change
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : params.length = info.nparams)
    (hpc : ctorParams.length = info.nparams) (hfc : ctorFields.length = info.numFields)
    (hpo : outParams.length = info.nparams)
    (hm : env.HasType univs Γ major (mkApps (.const family levels) params))
    (hc : env.HasType univs Γ (structExpand family info levels params major)
      (mkApps (.const family levels) params))
    (HM : PrefixCompute actualD Γ major
      (mkApps (.const info.ctorName ctorLevels) (ctorParams ++ ctorFields)))
    (R : PrefixCompute actualD Γ (structExpand family info levels params major)
      (mkApps (.const info.ctorName levels) (outParams ++ outFields))) :
    ∃ left right, PrefixCompute actualD Γ major left ∧
      PrefixCompute actualD Γ (mkApps (.const info.ctorName levels) (outParams ++ outFields)) right ∧
      ConstructorParameterChange Γ left right := by
  have hs := RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)
  obtain ⟨args, he, HA⟩ := R.rigid_spine_paths (henv.projectionCtorRigid hi)
    (fun _ _ => RegisteredStructure.definitions_ofEnv_no_rigid (henv.projectionCtorRigid hi))
  obtain ⟨_, _, he⟩ := mkApps_const_inj he
  subst args
  have HF : List.Forall₂ (PrefixCompute actualD Γ)
      ((List.range info.numFields).map (fun i => VExpr.proj family i major)) outFields := by
    have H := List.forall₂_drop HA info.nparams
    rw [← hp, List.drop_left, show params.length = outParams.length from hp.trans hpo.symm,
      List.drop_left] at H
    exact H
  obtain ⟨fields, HC, HO⟩ := constructor_exposure_fields_join hcon hΓ hi hpc hfc hc HM HF
  have RL := PrefixCompute.mkApps_paths (f := .const info.ctorName ctorLevels) .refl
    ((List.Forall₂.rfl (fun _ _ => PrefixCompute.refl) :
      List.Forall₂ (PrefixCompute actualD Γ) ctorParams ctorParams).append' HC)
  have RR := PrefixCompute.mkApps_paths (f := .const info.ctorName levels) .refl
    ((List.Forall₂.rfl (fun _ _ => PrefixCompute.refl) :
      List.Forall₂ (PrefixCompute actualD Γ) outParams outParams).append' HO)
  exact ⟨_, _, HM.trans RL, RR,
    .intro hi hx hpc hpo (HC.length_eq.symm.trans hfc)
      ((StructureReplay.expansion_typed_iff henv hΓ hi hp hx hm).1 hc)
      ((HM.trans RL).simAt hs hΓ _ hm).hasType.2
      ((R.trans RR).simAt hs hΓ _ hc).hasType.2⟩

/-- Every actual structure eta root followed by arbitrary finite computation
has either the existing symmetric phase or a computational join with precisely
one constructor parameter change. This covers all majors and data parameters;
it does not claim closure of this disjunction under compatible composition. -/
theorem structure_eta_compute_join_or_parameter_change
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : params.length = info.nparams)
    (hx : info.nindices = 0)
    (hm : env.HasType univs Γ major (mkApps (.const family levels) params))
    (hc : env.HasType univs Γ (structExpand family info levels params major)
      (mkApps (.const family levels) params))
    (R : PrefixCompute actualD Γ (structExpand family info levels params major) out) :
    PrefixEtaJoin actualD Γ major out ∨
      ∃ left right, PrefixCompute actualD Γ major left ∧ PrefixCompute actualD Γ out right ∧
        ConstructorParameterChange Γ left right := by
  classical
  by_cases hn : ∃ ls args, PrefixCompute actualD Γ major (mkApps (.const info.ctorName ls) args)
  · obtain ⟨ls, args, HM⟩ := hn
    have hs := RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)
    have ht := (HM.simAt hs hΓ _ hm).hasType.2
    have hlen := (projection_major_family henv hΓ hi (henv.projectionRigid hi) ht).2
    obtain ⟨outArgs, rfl, HA⟩ := R.rigid_spine_paths (henv.projectionCtorRigid hi)
      (fun _ _ => RegisteredStructure.definitions_ofEnv_no_rigid (henv.projectionCtorRigid hi))
    have hlenOut : outArgs.length = info.nparams + info.numFields := by
      simpa [hp] using HA.length_eq.symm
    apply Or.inr
    have H := structure_eta_compute_parameter_change
      (ctorParams := args.take info.nparams) (ctorFields := args.drop info.nparams)
      (outParams := outArgs.take info.nparams) (outFields := outArgs.drop info.nparams)
      hcon hΓ hi hx hp (by simp [hlen]) (by simp [hlen]) (by simp [hlenOut]) hm hc
      (by simpa only [List.take_append_drop] using HM)
      (by simpa only [List.take_append_drop] using R)
    simpa only [List.take_append_drop] using H
  · exact .inl (neutral_eta_compute_symmetric_phase hcon hΓ hi hp hx hm hc
      (fun ls args HM => hn ⟨ls, args, HM⟩) R)

end Lean4Lean.VEnv.Strengthening.PureObservation
