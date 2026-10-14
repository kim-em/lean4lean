import Lean4Lean.Theory.Typing.Strengthening.EtaConstructorExposure

/-! # Selective projection contraction is not pure eta expansion

For a two-field constructor containing a variable twice, structure expansion
followed by contraction of just its first projection is not itself a finite
eta expansion. This tests a strict exchange invariant; it does not refute the
larger computation/eta/normal representation.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Eta expansion cannot create a variable head. -/
theorem TypedEtaExpansion.bvar_source (R : TypedEtaExpansion Γ e (.bvar i)) : e = .bvar i := by
  have aux {Γ e out} (R : TypedEtaExpansion Γ e out) :
      ∀ i, out = .bvar i → e = .bvar i := by
    induction R with
    | refl => exact fun _ h => h
    | trans _ _ ih1 ih2 => exact fun i h => ih1 i (ih2 i h)
    | structEta =>
      intro i h
      have hh := congrArg getAppFn h
      simp only [getAppFn_mkApps, getAppFn] at hh
      cases hh
    | app | lam | forallE | proj | funEta => exact fun _ h => by cases h
  exact aux R i rfl

/-- Eta expansion cannot create a projection head. -/
theorem TypedEtaExpansion.proj_source (R : TypedEtaExpansion Γ e (.proj s i m)) :
    ∃ m', e = .proj s i m' := by
  generalize hout : VExpr.proj s i m = target at R
  induction R generalizing m with
  | refl => exact ⟨m, hout.symm⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨m', he⟩ := ih2 hout
    exact ih1 he.symm
  | structEta =>
    have hh := congrArg getAppFn hout
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh
  | proj => cases hout; exact ⟨_, rfl⟩
  | app | lam | forallE | funEta => cases hout

/-- The first projection of an expanded pair may contract while the second
remains. No finite eta path alone reaches that mixed result from the original
constructor. Normal comparison and preceding computation are deliberately not
excluded by this theorem. -/
theorem selective_projection_not_eta (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (ht : env.HasType univs Γ (mkApps (.const info.ctorName levels) [.bvar i, .bvar i]) T) :
    let source := mkApps (.const info.ctorName levels) [.bvar i, .bvar i]
    ¬ TypedEtaExpansion Γ source
      (mkApps (.const info.ctorName levels) [.bvar i, .proj family 1 source]) := by
  intro source R
  rcases R.constructor_exposure hΓ ht with ⟨args, he, HA⟩ | HE
  · have he' := congrArg getAppArgs he
    simp only [source, getAppArgs_mkApps, getAppArgs, List.nil_append] at he'
    subst args
    have HR := HA.getElem_of 1 (by simp) (by simp)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at HR
    obtain ⟨m, hm⟩ := HR.proj_source
    cases hm
  · obtain ⟨family', info', params, hi', hc, _, _, _, _, _, HF⟩ := HE
    obtain ⟨hfamily, hinfo⟩ := henv.ordered.projectionConstructor_family hi' hi hc
    cases hinfo
    cases hfamily
    simp only [hp, hf, List.drop_zero] at HF
    have HR := HF.getElem_of 0 (by simp) (by simp)
    simp only [List.getElem_map, List.getElem_range, List.getElem_cons_zero] at HR
    have he := HR.bvar_source
    cases he

/-- The selectively contracted result is nevertheless reached by an actual
structure-eta step and one compatible projection contraction. Both original
endpoint typings at the eta root remain explicit. -/
theorem selective_projection_full (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 2)
    (ht : env.HasType univs Γ (mkApps (.const info.ctorName levels) [.bvar i, .bvar i])
      (.const family levels))
    (hc : env.HasType univs Γ
      (structExpand family info levels [] (mkApps (.const info.ctorName levels) [.bvar i, .bvar i]))
      (.const family levels)) :
    let source := mkApps (.const info.ctorName levels) [.bvar i, .bvar i]
    FullReduction Γ source (mkApps (.const info.ctorName levels) [.bvar i, .proj family 1 source]) := by
  intro source
  have RE : FullReduction Γ source (structExpand family info levels [] source) :=
    .tail .rfl (.structEta hi hp.symm hx ht hc)
  have he : structExpand family info levels [] source =
      mkApps (.const info.ctorName levels) [.proj family 0 source, .proj family 1 source] := by
    simp [structExpand, hf, List.range_succ]
  rw [he] at RE hc
  obtain ⟨F, hproj⟩ := mkApps_arg_type hΓ hc (arg := .proj family 0 source) (by simp)
  have hlen : ([.bvar i, .bvar i] : List VExpr).length = info.nparams + info.numFields := by simp [hp, hf]
  have hg : ([.bvar i, .bvar i] : List VExpr)[info.nparams + 0]? = some (.bvar i) := by simp [hp]
  have RF : FullReduction Γ (.proj family 0 source) (.bvar i) :=
    .tail .rfl (.projIota hi hproj hg (HasType.projIota_field hΓ hi hproj hlen hg))
  exact RE.trans (FullReduction.app (.app .rfl RF) .rfl)

end Lean4Lean.VEnv.Strengthening.PureObservation
