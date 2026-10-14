import Lean4Lean.Theory.Typing.Strengthening.ProjectionComputationTrace
import Lean4Lean.Theory.Typing.Strengthening.ConstructorEtaCompletion

/-! # Completing structure eta at a fixed neutral major

Finite computation after this root can change its parameters, but cannot select
or change a projected field. The resulting parameters are valid parameters for
a fresh typed eta expansion of the original major. This discharges the neutral
root case without computational confluence or a strengthening front. Empty
structures require no fixedness premise at all. Majors with nonempty field
lists whose duplicated copies compute differently remain outside these results.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- If every projected field is computationally fixed, computation after eta
only changes the explicit parameter prefix. No condition is imposed on the
major itself. -/
theorem eta_compute_fixed_fields_shape
    (hi : env.projections family info)
    (hnCtor : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hfields : ∀ i, i < info.numFields → ∀ out,
      PrefixCompute D Γ (.proj family i major) out → out = .proj family i major)
    (R : PrefixCompute D Γ (structExpand family info levels params major) out) :
    ∃ params', List.Forall₂ (PrefixCompute D Γ) params params' ∧
      out = structExpand family info levels params' major := by
  obtain ⟨args, rfl, HA⟩ := R.rigid_spine_paths (henv.projectionCtorRigid hi) hnCtor
  have HP : List.Forall₂ (PrefixCompute D Γ) params (args.take params.length) := by
    simpa only [List.take_left] using List.forall₂_take HA params.length
  have HF : List.Forall₂ (PrefixCompute D Γ)
      ((List.range info.numFields).map (fun i => VExpr.proj family i major))
      (args.drop params.length) := by
    simpa only [List.drop_left] using List.forall₂_drop HA params.length
  have he : args.drop params.length =
      (List.range info.numFields).map (fun i => VExpr.proj family i major) := by
    apply List.ext_getElem HF.length_eq.symm
    intro j hj hj'
    have H := HF.getElem_of j hj' hj
    simp only [List.getElem_map, List.getElem_range] at H ⊢
    exact hfields j (by simpa using hj') _ H
  refine ⟨args.take params.length, HP, ?_⟩
  unfold structExpand
  rw [← he, List.take_append_drop]

/-- Computed parameters can be used directly by the original major's eta
root. Typing conversion changes the family instance, while the original
closed eta-admissibility certificate supplies the reconstructed constructor. -/
theorem eta_compute_fixed_fields_expansion
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : params.length = info.nparams)
    (hx : info.nindices = 0)
    (hm : env.HasType univs Γ major (mkApps (.const family levels) params))
    (hc : env.HasType univs Γ (structExpand family info levels params major)
      (mkApps (.const family levels) params))
    (hnCtor : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hfields : ∀ i, i < info.numFields → ∀ out,
      PrefixCompute D Γ (.proj family i major) out → out = .proj family i major)
    (R : PrefixCompute D Γ (structExpand family info levels params major) out) :
    TypedEtaExpansion Γ major out := by
  obtain ⟨params', HP, rfl⟩ := eta_compute_fixed_fields_shape hi hnCtor hfields R
  have hp' := HP.length_eq.symm.trans hp
  obtain ⟨u, hfamily⟩ := hm.isType henv hΓ
  have HF := (PrefixCompute.mkApps_paths (D := D) (Γ := Γ)
    (f := .const family levels) .refl HP).simAt hs hΓ _ hfamily
  have hm' := hm.defeqU_r henv hΓ ⟨_, HF⟩
  have hc' := (StructureReplay.expansion_typed_iff henv hΓ hi hp' hx hm').2
    ((StructureReplay.expansion_typed_iff henv hΓ hi hp hx hm).1 hc)
  exact .structEta hi hp' hx hm' hc'

/-- For a fixed neutral major, the projection trace excludes field selection.
Only parameters compute, and conversion supplies a single new eta root. -/
theorem neutral_eta_compute_expansion
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hi : env.projections family info) (hp : params.length = info.nparams)
    (hx : info.nindices = 0)
    (hm : env.HasType univs Γ major (mkApps (.const family levels) params))
    (hc : env.HasType univs Γ (structExpand family info levels params major)
      (mkApps (.const family levels) params))
    (hnCtor : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hfix : ∀ out, PrefixCompute D Γ major out → out = major)
    (hnMajor : ∀ info' levels args, env.projections family info' →
      major ≠ mkApps (.const info'.ctorName levels) args)
    (R : PrefixCompute D Γ (structExpand family info levels params major) out) :
    TypedEtaExpansion Γ major out :=
  eta_compute_fixed_fields_expansion hs hΓ hi hp hx hm hc hnCtor
    (fun _ _ _ R => R.projection_fixed hcon hfix hnMajor) R

/-- With no fields, there are no duplicated major paths to align. Arbitrary
finite computation after the root is absorbed by retyping its parameters,
without any fixedness assumption on the original major. -/
theorem empty_structure_eta_compute_expansion
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : params.length = info.nparams)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hm : env.HasType univs Γ major (mkApps (.const family levels) params))
    (hc : env.HasType univs Γ (structExpand family info levels params major)
      (mkApps (.const family levels) params))
    (hnCtor : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (R : PrefixCompute D Γ (structExpand family info levels params major) out) :
    TypedEtaExpansion Γ major out :=
  eta_compute_fixed_fields_expansion hs hΓ hi hp hx hm hc hnCtor
    (fun _ hi _ _ => (by omega)) R

/-- Arbitrary parameter computation after eta at a variable already has an
exact one-sided eta/normal phase. It needs no completion of the right endpoint. -/
theorem variable_eta_compute_phase
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hi : env.projections family info) (hp : params.length = info.nparams)
    (hx : info.nindices = 0)
    (hm : env.HasType univs Γ (.bvar i) (mkApps (.const family levels) params))
    (hc : env.HasType univs Γ (structExpand family info levels params (.bvar i))
      (mkApps (.const family levels) params))
    (hnCtor : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (R : PrefixCompute D Γ (structExpand family info levels params (.bvar i)) out) :
    EtaNormal Γ (.bvar i) out := by
  apply EtaNormal.expansion hΓ _ hm
  apply neutral_eta_compute_expansion hs hΓ hcon hi hp hx hm hc hnCtor
    (fun _ R => R.bvar_eq) _ R
  intro info' levels args _ he
  have hh := congrArg getAppFn he
  simp only [getAppFn_mkApps, getAppFn] at hh
  cases hh

end Lean4Lean.VEnv.Strengthening.PureObservation
