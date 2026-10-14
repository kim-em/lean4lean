import Lean4Lean.Theory.Typing.Strengthening.PrefixConstructorFixed
import Lean4Lean.Theory.Typing.Strengthening.PrefixStep

/-! # Computationally fixed neutral recursor spines

At a nonzero source universe an actual recursor has no singleton prefix.
If all supplied arguments are computationally fixed and none has a constant
head, its iota patterns cannot match either. This includes variable majors
with lambda motives and branches. No rigidity of the recursor is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

private theorem no_neutral_pattern
    (hreg : recursorData c = some data)
    (ha : ∀ a ∈ args, ∀ name levels, getAppFn a ≠ .const name levels)
    (hp : Pat p r) (hm : p.Matches (mkApps (.const c ls) args) levels captures) : False := by
  obtain ⟨sp, rfl⟩ := pat_simple hp
  cases sp with
  | defn name =>
    generalize hsrc : mkApps (.const c ls) args = source at hm
    cases hm
    have hh := congrArg getAppFn hsrc
    simp only [getAppFn_mkApps, getAppFn, VExpr.const.injEq] at hh
    obtain ⟨rfl, _⟩ := hh
    have hn := (pat_const_not_unfolding hp).1
    rw [hreg] at hn
    cases hn
  | iota rc n ctor k =>
    obtain ⟨xs, ys, us, _, _, he, _, _⟩ := SimplePattern.iota_matches_inv hm
    have hh := congrArg getAppArgs he
    simp only [getAppArgs_mkApps, getAppArgs, List.nil_append] at hh
    have hm' : mkApps (.const ctor us) ys ∈ args := by rw [hh]; simp
    exact ha _ hm' ctor us (by simp [getAppFn_mkApps, getAppFn])

private theorem pattern_neutral_spine_fixed (R : PatternStep D (mkApps (.const c ls) args) out)
    (hreg : recursorData c = some data) (hn : ∀ rhs, ¬ D.unfolds c ls rhs)
    (ha : ∀ a ∈ args, ∀ name levels, getAppFn a ≠ .const name levels)
    (hfix : ∀ a ∈ args, ∀ out, PatternCompute D a out → out = a) :
    out = mkApps (.const c ls) args := by
  generalize hsrc : mkApps (.const c ls) args = source at R
  induction R generalizing args with
  | pattern hp _ hm _ => exact (no_neutral_pattern hreg ha hp (hsrc ▸ hm)).elim
  | delta hd =>
    have hh := congrArg getAppFn hsrc
    simp only [getAppFn_mkApps, getAppFn, VExpr.const.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    exact (hn _ hd).elim
  | @appL f f' a R ih =>
    obtain ⟨xs, rfl, he⟩ := RigidHead.const.mkApps_eq_app hsrc
    have hf := ih (fun a h => ha a (List.mem_append_left _ h))
      (fun a h => hfix a (List.mem_append_left _ h)) he.symm
    simpa only [mkApps_snoc] using congrArg (fun f => VExpr.app f a) hf
  | @appR a a' f R _ =>
    obtain ⟨xs, rfl, he⟩ := RigidHead.const.mkApps_eq_app hsrc
    have h := hfix a (List.mem_append_right _ (by simp)) _ R.toCompute
    rw [h, he]
  | beta | projIota | lamL | lamR | forallL | forallR | proj =>
    have hh := congrArg getAppFn hsrc
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh

private theorem prefix_neutral_spine_fixed
    (R : PrefixStep D Γ (mkApps (.const c ls) args) out)
    (hreg : recursorData c = some data) (hz : ¬ data.sourceLevel ls ≈ .zero)
    (hn : ∀ rhs, ¬ D.unfolds c ls rhs)
    (ha : ∀ a ∈ args, ∀ name levels, getAppFn a ≠ .const name levels)
    (hfix : ∀ a ∈ args, ∀ out, PrefixCompute D Γ a out → out = a) :
    out = mkApps (.const c ls) args := by
  generalize hsrc : mkApps (.const c ls) args = source at R
  induction R generalizing args with
  | base R =>
    exact (pattern_neutral_spine_fixed (hsrc ▸ R) hreg hn ha
      (fun a h out R => hfix a h out (.base R))).trans hsrc
  | singleton R =>
    have hh := congrArg getAppFn hsrc
    simp only [getAppFn_mkApps, getAppFn, VExpr.const.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    cases R with
    | intro hr _ _ _ _ hzero _ _ =>
      cases Option.some.inj (hreg.symm.trans hr)
      exact (hz hzero).elim
  | quotient R =>
    have hh := congrArg getAppFn hsrc
    simp only [getAppFn_mkApps, getAppFn, VExpr.const.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    have he := recursorData_quot R.registered
    rw [hreg] at he
    cases he
  | @appL Γ f f' a R ih =>
    obtain ⟨xs, rfl, he⟩ := RigidHead.const.mkApps_eq_app hsrc
    have hf := ih (fun a h => ha a (List.mem_append_left _ h))
      (fun a h => hfix a (List.mem_append_left _ h)) he.symm
    simpa only [mkApps_snoc] using congrArg (fun f => VExpr.app f a) hf
  | @appR Γ a a' f R _ =>
    obtain ⟨xs, rfl, he⟩ := RigidHead.const.mkApps_eq_app hsrc
    have h := hfix a (List.mem_append_right _ (by simp)) _ R.toCompute
    rw [h, he]
  | lamL | lamR | forallL | forallR | proj =>
    have hh := congrArg getAppFn hsrc
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh

/-- At a registered nonzero-source recursor, fixed arguments without constant
heads exclude every actual prefix and pattern computation. -/
theorem PrefixCompute.neutral_recursor_fixed
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (R : PrefixCompute D Γ (mkApps (.const c ls) args) out)
    (hreg : recursorData c = some data) (hz : ¬ data.sourceLevel ls ≈ .zero)
    (hn : ∀ rhs, ¬ D.unfolds c ls rhs)
    (ha : ∀ a ∈ args, ∀ name levels, getAppFn a ≠ .const name levels)
    (hfix : ∀ a ∈ args, ∀ out, PrefixCompute D Γ a out → out = a) :
    out = mkApps (.const c ls) args := by
  exact prefix_induct_steps hcon R (P := fun x => x = mkApps (.const c ls) args) rfl
    (fun R he => prefix_neutral_spine_fixed (he ▸ R) hreg hz hn ha hfix)

end Lean4Lean.VEnv.Strengthening.PureObservation
