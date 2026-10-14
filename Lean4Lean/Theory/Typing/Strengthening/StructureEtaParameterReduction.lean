import Lean4Lean.Theory.Typing.Strengthening.NeutralEtaConfluence
import Lean4Lean.Theory.Typing.Strengthening.SymmetricSpineCompatibility

/-! # Reducing constructor-exposing eta overlaps to parameter phases

Computational confluence joins all fields independently, even when the major
exposes a constructor at different parameters and universe syntax. Typing
supplies the universe comparison. Only the constructor parameters require
symmetric phase certificates; arbitrary conversion does not supply those here.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

private abbrev actualD : Definitions :=
  RegisteredStructure.definitions (Definitions.ofEnv env univs henv)

/-- A constructor exposure supplies a common computational ancestor for each
selected field and every independently computed copy of the original projection.
Neither the exposure's parameters nor its universes must equal the eta root's. -/
theorem constructor_exposure_fields_join
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : ctorParams.length = info.nparams)
    (hf : ctorFields.length = info.numFields)
    (ht : env.HasType univs Γ (structExpand family info levels params major) T)
    (HM : PrefixCompute actualD Γ major
      (mkApps (.const info.ctorName ctorLevels) (ctorParams ++ ctorFields)))
    (HF : List.Forall₂ (PrefixCompute actualD Γ)
      ((List.range info.numFields).map (fun i => VExpr.proj family i major)) fields) :
    ∃ common, List.Forall₂ (PrefixCompute actualD Γ) ctorFields common ∧
      List.Forall₂ (PrefixCompute actualD Γ) fields common := by
  have hlen : ctorFields.length = fields.length := by simpa [hf] using HF.length_eq
  apply forall₂_common_targets hlen
  intro i hiF hiO
  have hiN : i < info.numFields := by omega
  have H := HF.getElem_of i (by simp; exact hiN) hiO
  simp only [List.getElem_map, List.getElem_range] at H
  obtain ⟨S, hproj⟩ := mkApps_arg_type hΓ ht (arg := .proj family i major)
    (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hiN, rfl⟩))
  have hg : (ctorParams ++ ctorFields)[info.nparams + i]? = some ctorFields[i] := by
    rw [List.getElem?_append_right (by omega), hp, Nat.add_sub_cancel_left]
    exact List.getElem?_eq_getElem hiF
  have root : PrefixCompute actualD Γ
      (.proj family i (mkApps (.const info.ctorName ctorLevels) (ctorParams ++ ctorFields))) ctorFields[i] :=
    .base (.base (.projIota hi (by simp [hp, hf]) hg))
  exact ((PrefixCompute.proj HM).trans root).confluent hcon hΓ hproj H

/-- Saturated constructors at a common type have pairwise convertible
parameters, even when their displayed universe syntax differs. This supplies
conversion only; symmetric phase certificates remain a separate obligation. -/
theorem constructor_parameters_defeq
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : params.length = info.nparams) (hp' : params'.length = info.nparams)
    (hf : fields.length = info.numFields) (hf' : fields'.length = info.numFields)
    (ht : env.HasType univs Γ (mkApps (.const info.ctorName levels) (params ++ fields)) T)
    (ht' : env.HasType univs Γ (mkApps (.const info.ctorName levels') (params' ++ fields')) T) :
    List.Forall₂ (env.IsDefEqU univs Γ) params params' := by
  obtain ⟨idx, H⟩ := ht.ctorApp_type hΓ hi (by simp [hp, hf])
  obtain ⟨idx', H'⟩ := ht'.ctorApp_type hΓ hi (by simp [hp', hf'])
  simp only [← hp, List.take_left] at H
  simp only [← hp', List.take_left] at H'
  obtain ⟨_, hT⟩ := ht.isType henv hΓ
  have HE := H.symm.trans henv hΓ H'
  have HA := (HE.structApp_inv henv hΓ hi (hT.defeqU_l henv hΓ H)).2
  exact (List.forall₂_append_split HA (hp.trans hp'.symm)).1

/-- After a constructor exposure, symmetric phase certificates for its
parameters and the output parameters suffice for the complete eta/computation
overlap. Field computation and universe syntax need no extra certificates. -/
theorem structure_eta_compute_parameter_phase
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : params.length = info.nparams)
    (hpc : ctorParams.length = info.nparams) (hfc : ctorFields.length = info.numFields)
    (hpo : outParams.length = info.nparams)
    (hm : env.HasType univs Γ major (mkApps (.const family levels) params))
    (ht : env.HasType univs Γ (structExpand family info levels params major) T)
    (HM : PrefixCompute actualD Γ major
      (mkApps (.const info.ctorName ctorLevels) (ctorParams ++ ctorFields)))
    (R : PrefixCompute actualD Γ (structExpand family info levels params major)
      (mkApps (.const info.ctorName levels) (outParams ++ outFields)))
    (HP : List.Forall₂ (PrefixEtaJoin actualD Γ) ctorParams outParams) :
    PrefixEtaJoin actualD Γ major
      (mkApps (.const info.ctorName levels) (outParams ++ outFields)) := by
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
  obtain ⟨fields, HC, HO⟩ := constructor_exposure_fields_join hcon hΓ hi hpc hfc ht HM HF
  have hc := (HM.simAt hs hΓ _ hm).hasType.2
  have hlen : (ctorParams ++ ctorFields).length = info.nparams + info.numFields := by simp [hpc, hfc]
  obtain ⟨hwc, hlc, hw, hlevels⟩ := StructureReplay.constructor_levels henv hΓ hi hlen hc
  have headNormal : NormalEq Γ (.const info.ctorName ctorLevels) (.const info.ctorName levels) :=
    .constDF (henv.ordered.projectionConstructor hi) hwc hw hlc hlevels
  have RLeft := PrefixCompute.mkApps_paths (f := .const info.ctorName ctorLevels) .refl
    ((List.Forall₂.rfl (fun _ _ => PrefixCompute.refl) :
      List.Forall₂ (PrefixCompute actualD Γ) ctorParams ctorParams).append' HC)
  have RRight := PrefixCompute.mkApps_paths (f := .const info.ctorName levels) .refl
    ((List.Forall₂.rfl (fun _ _ => PrefixCompute.refl) :
      List.Forall₂ (PrefixCompute actualD Γ) outParams outParams).append' HO)
  have hleft := (RLeft.simAt hs hΓ _ hc).hasType.2
  have hright := (RRight.simAt hs hΓ _ (R.simAt hs hΓ _ ht).hasType.2).hasType.2
  have HFields : List.Forall₂ (PrefixEtaJoin actualD Γ) fields fields :=
    List.Forall₂.rfl (fun field hfield =>
      PrefixEtaJoin.compute hs hΓ .refl
        (mkApps_arg_type hΓ hleft (List.mem_append_right _ hfield)).choose_spec)
  have H := PrefixEtaJoin.mkApps_spine hs hΓ
    (PrefixEtaJoin.of_eta (EtaNormal.normal headNormal).join) (HP.append' HFields) hleft hright
  exact (H.prepend_left (HM.trans RLeft)).prepend_right RRight

/-- Every structure eta root with no parameters admits a symmetric phase
after arbitrary finite computation. Neutral and constructor-exposing majors
are both covered, including different constructor universe syntax. -/
theorem parameterless_structure_eta_compute_phase
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : info.nparams = 0) (hx : info.nindices = 0)
    (hm : env.HasType univs Γ major (.const family levels))
    (hc : env.HasType univs Γ (structExpand family info levels [] major) (.const family levels))
    (R : PrefixCompute actualD Γ (structExpand family info levels [] major) out) :
    PrefixEtaJoin actualD Γ major out := by
  classical
  by_cases hn : ∃ ls args, PrefixCompute actualD Γ major (mkApps (.const info.ctorName ls) args)
  · obtain ⟨ls, args, HM⟩ := hn
    have hs := RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)
    have ht := (HM.simAt hs hΓ _ hm).hasType.2
    have hlen := (projection_major_family henv hΓ hi (henv.projectionRigid hi) (ps := []) ht).2
    obtain ⟨outArgs, rfl, _⟩ := R.rigid_spine_paths (henv.projectionCtorRigid hi)
      (fun _ _ => RegisteredStructure.definitions_ofEnv_no_rigid (henv.projectionCtorRigid hi))
    exact structure_eta_compute_parameter_phase (params := []) (ctorParams := []) (outParams := [])
      hcon hΓ hi hp.symm hp.symm
      (by simpa [hp] using hlen) hp.symm hm hc HM R (.nil : List.Forall₂ _ [] [])
  · exact neutral_eta_compute_symmetric_phase (params := []) hcon hΓ hi hp.symm hx hm hc
      (fun ls args HM => hn ⟨ls, args, HM⟩) R

end Lean4Lean.VEnv.Strengthening.PureObservation
