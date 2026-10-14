import Lean4Lean.Theory.Typing.Strengthening.ConstructorHeadExposure
import Lean4Lean.Theory.Typing.Strengthening.ProjectionRecoveryTotality

/-! # Repair family exposure through arbitrary eta annotations

Empty tuple demands observe only a family's head, levels, and argument count.
Projection families cannot be structure constructors, so structure eta cannot
introduce this observation spuriously. The existing backwards-observation proof
therefore removes both kinds of eta from family-exposing paths in this model.
Indexed singleton prefixes remain outside its covered computational rules.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions PatternCompute)
variable [Params]

/-- A projection family is never any projection constructor, including one
installed by another declaration. -/
theorem NotProjectionCtor.of_family (hi : env.projections s info) : NotProjectionCtor s := by
  intro s' info' hi' he
  exact (henv.projStatic hi).famNotProjCtor ⟨s', info', hi', he⟩

/-- Empty demands consume a spine without inspecting any of its arguments. -/
theorem Obs.mkApps_empty (H : Obs D S f (Ob.wrap (args.map (fun _ => [])) o)) :
    Obs D S (mkApps f args) o := by
  induction args generalizing f with
  | nil => exact H
  | cons a args ih =>
    apply ih
    exact .app H (by simp)

/-- The tuple interface also observes family applications: no argument
annotation or universe-dependent structure-eta guard is needed. -/
theorem Obs.family_tuple (hi : env.projections s info) :
    Obs D S (mkApps (.const s ls) args) (.ctor s ls (args.map (fun _ => []))) :=
  Obs.mkApps_empty (.ctorTuple (NotProjectionCtor.of_family hi).notEtaCtor.atLevels)

/-- A family tuple observation exposes a literal family spine by computation.
Its empty demands retain the argument count without constraining their syntax. -/
theorem Obs.family_exposure {args : List VExpr}
    (H : Obs D (fun _ _ => False) e (.ctor s ls (args.map (fun _ => [])))) :
    ∃ args', PatternCompute D e (mkApps (.const s ls) args') ∧ args'.length = args.length := by
  have h := H.realizes (σ := .id) (fun _ _ h => h.elim)
  rw [subst_id] at h
  obtain ⟨args', R, hargs⟩ := h.ctor_inv
  exact ⟨args', R, by simpa using hargs.length_eq.symm⟩

/-- Both eta forms can be removed from a family-exposing path in the covered
beta/declaration/projection/pattern model. Recovered arguments may differ. -/
theorem EtaCompute.family_exposure (hD : ConstructorRigid D) (hi : env.projections s info)
    (R : EtaCompute D e (mkApps (.const s ls) args)) :
    ∃ args', PatternCompute D e (mkApps (.const s ls) args') ∧ args'.length = args.length :=
  (R.obs_back hD (Obs.family_tuple hi)).family_exposure

/-- The repaired family computation lowers through any binder insertion.
No scope premise on the original path's eta annotations or arguments is used. -/
theorem EtaCompute.family_exposure_below (hD : ConstructorRigid D)
    (hi : env.projections s info)
    (R : EtaCompute D (e.lift' ρ) (mkApps (.const s ls) args)) :
    ∃ args', PatternCompute D e (mkApps (.const s ls) args') ∧ args'.length = args.length := by
  obtain ⟨args', RC, hlen⟩ := R.family_exposure hD hi
  obtain ⟨out, R₀, he⟩ := RC.lift_inv
  obtain ⟨args₀, rfl, rfl⟩ := PureObservation.lift'_eq_const_spine he.symm
  exact ⟨args₀, R₀, by simpa using hlen⟩

/-- A lifted family exposure reconstructs a genuine family typing below using
only the major's original lower typing. Its parameters need not match the
ambient exposure's parameters, which may mention the removed variables. -/
theorem EtaCompute.major_type_below (hD : ConstructorRigid D) (hs : D.Sound env univs)
    (hi : env.projections s info) (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m T)
    (R : EtaCompute D (T.lift' ρ) (mkApps (.const s ls) args)) :
    ∃ args', PatternCompute D T (mkApps (.const s ls) args') ∧
      env.HasType univs Γ m (mkApps (.const s ls) args') ∧ args'.length = args.length := by
  obtain ⟨args', RC, hlen⟩ := R.family_exposure_below hD hi
  obtain ⟨_, hT⟩ := hm.isType henv hΓ
  exact ⟨args', RC, (RC.simAt hs hΓ _ hT).defeq hm, hlen⟩

/-- A source-typed projection recovers its selected field below from such a
family exposure. Field success and the elimination guard are derived, not
assumed for the repaired parameters. -/
theorem EtaCompute.projection_type_below (hD : ConstructorRigid D) (hs : D.Sound env univs)
    (hi : env.projections s info) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : VExpr.WF env univs Γ (.proj s i m)) (hm : env.HasType univs Γ m T)
    (R : EtaCompute D (T.lift' ρ) (mkApps (.const s ls) args)) :
    ∃ args' F, PatternCompute D T (mkApps (.const s ls) args') ∧
      info.fieldType s ls (args'.take info.nparams) i m = some F ∧
      env.HasType univs Γ (.proj s i m) F := by
  obtain ⟨args', RC, hm', _⟩ := R.major_type_below hD hs hi hΓ hm
  obtain ⟨F, hF, hp⟩ := projection_at_recovered_family_exists henv hΓ hi ht hm'
  exact ⟨args', F, RC, hF, hp⟩

end Lean4Lean.VEnv.Strengthening.ConstructorObservation
