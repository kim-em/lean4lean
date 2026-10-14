import Lean4Lean.Theory.Typing.Strengthening.NormalConstructorFields

/-! # Selective projection requires a more complicated terminal witness

For the two-field test with sort-typed fields, no eta/normal witness can have a
literal constructor spine at the end of its eta phase. Normal spine exposure
may beta-reduce the arguments, but cannot erase the distinguishing projection.
Arbitrary eta-generated lambda spines are not excluded by this theorem.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Adding normal comparison does not repair the selective-projection test
when the eta phase ends at a literal spine of the original constructor. The
remaining case is an eta-generated lambda in function position, not covered
by this statement. -/
theorem selective_projection_no_constructor_middle
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hnp : ¬ env.HasType univs Γ (.const family levels) (.sort .zero))
    (ht : env.HasType univs Γ (mkApps (.const info.ctorName levels) [.bvar i, .bvar i])
      (.const family levels))
    (hv : env.HasType univs Γ (.bvar i) (.sort u))
    (hproj : env.HasType univs Γ (.proj family 0
      (mkApps (.const info.ctorName levels) [.bvar i, .bvar i])) (.sort v)) :
    let source := mkApps (.const info.ctorName levels) [.bvar i, .bvar i]
    ∀ ls args, ¬ (TypedEtaExpansion Γ source (mkApps (.const info.ctorName ls) args) ∧
      NormalEq Γ (mkApps (.const info.ctorName ls) args)
        (mkApps (.const info.ctorName levels) [.bvar i, .proj family 1 source])) := by
  intro source ls args ⟨RE, HN⟩
  have hm := (RE.simAt hΓ _ ht).hasType.2
  obtain ⟨argsB, RB, NB⟩ := normal_constructor_fields hΓ hi (params := []) hnp hm HN
  have hlenB : argsB.length = 2 := by simpa using NB.length_eq
  have hlen : args.length = 2 := RB.length_eq.trans hlenB
  rcases RE.constructor_exposure hΓ ht with ⟨args0, he, HA⟩ | HE
  · have he' := congrArg getAppArgs he
    simp only [source, getAppArgs_mkApps, getAppArgs, List.nil_append] at he'
    subst args0
    have H1 := HA.getElem_of 1 (by simp) (by omega)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at H1
    have he1 := H1.sort_bvar_eq hΓ hv
    have RB1 := RB.getElem_of 1 (by omega) (by omega)
    have NB1 := NB.getElem_of 1 (by omega) (by simp)
    rw [he1] at RB1
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at NB1
    have he := variable_beta_normal_fixed hΓ hv RB1 NB1
    cases he
  · obtain ⟨family', info', params, hi', hc, _, _, _, _, _, HF⟩ := HE
    obtain ⟨hfamily, hinfo⟩ := henv.ordered.projectionConstructor_family hi' hi hc
    cases hinfo
    cases hfamily
    simp only [hp, hf, List.drop_zero] at HF
    have H0 := HF.getElem_of 0 (by simp) (by omega)
    simp only [List.getElem_map, List.getElem_range] at H0
    obtain ⟨major, he0⟩ := H0.sort_proj_out hΓ hproj
    have RB0 := RB.getElem_of 0 (by omega) (by omega)
    have NB0 := NB.getElem_of 0 (by omega) (by simp)
    rw [he0] at RB0
    simp only [List.getElem_cons_zero] at NB0
    exact projection_beta_normal_not_variable hΓ hv RB0 NB0

end Lean4Lean.VEnv.Strengthening.PureObservation
