import Lean4Lean.Theory.Typing.Strengthening.NormalPrefixFactorization
import Lean4Lean.Theory.Typing.Strengthening.CanonicalEqHeadBoundary

/-! # Conditional head repair for actual prefix/function-eta paths

The witnessed front repairs Pi and sort-typed constant-head exposure through
arbitrary pattern/prefix/function-eta paths, even when eta annotations capture
an inserted binder. Structure eta is outside the input relation; its separate
factorization obstruction is recorded in PrefixStructureBoundary.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}
variable (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelStable univs)
variable (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
variable (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
include heq hs hl hfront hcon

/-- Function eta can be removed from a path exposing a Pi, while retaining
actual prefix checks. The recovered annotations may differ from the originals. -/
theorem TypedPrefixEta.pi_exposure (hΓ : OnCtx Γ (env.IsType univs))
    (R : TypedPrefixEta D Γ e (.forallE A B)) (ht : env.HasType univs Γ e T) :
    ∃ A' B', PrefixCompute D Γ e (.forallE A' B') := by
  obtain ⟨mid, RC, HN⟩ := R.factor heq hfront hs hl hcon hΓ ht
  obtain ⟨A', B', rfl⟩ := normal_pi_right hΓ HN
  exact ⟨A', B', RC⟩

/-- Sort typing eliminates both extensional exposure alternatives. The remaining
beta-only exposure reaches the same constant name and equivalent levels, with
unchanged arity. No rigidity hypothesis for that constant is needed. -/
theorem TypedPrefixEta.const_spine_exposure (hΓ : OnCtx Γ (env.IsType univs))
    (R : TypedPrefixEta D Γ e (mkApps (.const name levels) args))
    (ht : env.HasType univs Γ e (.sort u)) :
    ∃ levels' args', PrefixCompute D Γ e (mkApps (.const name levels') args') ∧
      List.Forall₂ (· ≈ ·) levels' levels ∧ args'.length = args.length := by
  obtain ⟨mid, RC, n, HN⟩ := R.factor heq hfront hs hl hcon hΓ ht
  have hmid := (RC.simAt hs hΓ _ ht).hasType.2
  rcases normal_spine_expose_beta hΓ .const n HN (bs := []) .nil hmid with
    hp | ⟨head, args', hh, RB, HA⟩ | ⟨A, body, m, xs, B, hm, RB, HB, hx, hfun⟩ |
      ⟨z, A, B, m, xs, hm, RB, hz, HB, hx, hfun⟩
  · exact (HasType.sort_not_proof hΓ hmid hp).elim
  · cases hh with
    | const hlevels =>
      simp only [mkApps, List.foldl_nil] at RB
      exact ⟨_, args', RC.trans (.base (.of_beta RB)), hlevels, by
        simpa only [List.append_nil] using HA.length_eq⟩
  · have hbody := (RB.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hmid).hasType.2
    exact (HasType.sort_not_lam hΓ hbody).elim
  · have hsort := (RB.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hmid).hasType.2
    exact ((hsort.uniqU henv hΓ hz).sort_forallE_inv henv hΓ).elim

/-- Repaired Pi exposure descends through arbitrary insertion from source typing
alone. In particular, the original upper eta domains need not be scoped below. -/
theorem TypedPrefixEta.pi_exposure_below (W : Ctx.Lift' ρ Γ Γ')
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (R : TypedPrefixEta D Γ' (e.lift' ρ) (.forallE A B))
    (ht : env.HasType univs Γ e T) :
    ∃ A' B', PrefixCompute D Γ e (.forallE A' B') := by
  obtain ⟨A0, B0, RC⟩ := R.pi_exposure heq hs hl hfront hcon hΓ' (ht.weak' henv W)
  obtain ⟨out, Rlower, he⟩ := RC.lift_inv heq hs hfront W hΓ hΓ' ht
  obtain ⟨A', B', rfl, _, _⟩ := lift'_eq_forallE he.symm
  exact ⟨A', B', Rlower⟩

/-- Sort-typed constant-head exposure likewise repairs and descends, preserving
its constant name, equivalent universe list and supplied arity. -/
theorem TypedPrefixEta.const_spine_exposure_below (W : Ctx.Lift' ρ Γ Γ')
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (R : TypedPrefixEta D Γ' (e.lift' ρ) (mkApps (.const name levels) args))
    (ht : env.HasType univs Γ e (.sort u)) :
    ∃ levels' args', PrefixCompute D Γ e (mkApps (.const name levels') args') ∧
      List.Forall₂ (· ≈ ·) levels' levels ∧ args'.length = args.length := by
  obtain ⟨levels', args0, RC, hlevels, hlen⟩ :=
    R.const_spine_exposure heq hs hl hfront hcon hΓ' (ht.weak' henv W)
  obtain ⟨out, Rlower, he⟩ := RC.lift_inv heq hs hfront W hΓ hΓ' ht
  obtain ⟨args', rfl, rfl⟩ := lift'_eq_const_spine he.symm
  exact ⟨levels', args', Rlower, hlevels, by simpa only [List.length_map] using hlen⟩

/-- Exposure of an inferred type reconstructs an actual Pi typing below. The
witnessed front is still assumed and full structure-eta paths are not covered. -/
theorem TypedPrefixEta.function_type_below (W : Ctx.Lift' ρ Γ Γ')
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (hf : env.HasType univs Γ f T)
    (R : TypedPrefixEta D Γ' (T.lift' ρ) (.forallE A B)) :
    ∃ A' B', env.HasType univs Γ f (.forallE A' B') ∧
      env.IsDefEqU univs Γ T (.forallE A' B') := by
  obtain ⟨u, hT⟩ := hf.isType henv hΓ
  obtain ⟨A', B', RC⟩ := R.pi_exposure_below heq hs hl hfront hcon W hΓ hΓ' hT
  have HE := RC.simAt hs hΓ _ hT
  exact ⟨A', B', hf.defeqU_r henv hΓ ⟨_, HE⟩, _, HE⟩

/-- Family exposure of an inferred type reconstructs a lower family typing,
including actual indexed-singleton prefix steps allowed by the witnessed front. -/
theorem TypedPrefixEta.family_type_below (W : Ctx.Lift' ρ Γ Γ')
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (hm : env.HasType univs Γ m T)
    (R : TypedPrefixEta D Γ' (T.lift' ρ) (mkApps (.const name levels) args)) :
    ∃ levels' args', env.HasType univs Γ m (mkApps (.const name levels') args') ∧
      env.IsDefEqU univs Γ T (mkApps (.const name levels') args') ∧
      List.Forall₂ (· ≈ ·) levels' levels ∧ args'.length = args.length := by
  obtain ⟨u, hT⟩ := hm.isType henv hΓ
  obtain ⟨levels', args', RC, hlevels, hlen⟩ :=
    R.const_spine_exposure_below heq hs hl hfront hcon W hΓ hΓ' hT
  have HE := RC.simAt hs hΓ _ hT
  exact ⟨levels', args', hm.defeqU_r henv hΓ ⟨_, HE⟩, ⟨_, HE⟩, hlevels, hlen⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
