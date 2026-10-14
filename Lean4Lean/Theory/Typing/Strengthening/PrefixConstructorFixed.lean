import Lean4Lean.Theory.Typing.Strengthening.FreshPrefixReflection
import Lean4Lean.Theory.Typing.Strengthening.QuotHeadComputation

/-! # Constructor spines of variables are computationally fixed

Registered projection constructors cannot head stored pattern or prefix rules.
Consequently a constructor applied only to variables is fixed by every actual
prefix computation, provided the chosen declarations do not unfold its head.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params

/-- Compatible beta/delta computation fixes a non-unfolding constant spine
whose arguments are variables. -/
theorem Compute.bvar_spine_fixed (R : Compute D (VExpr.mkApps (.const c ls) args) out)
    (hn : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (ha : ∀ a ∈ args, ∃ i, a = .bvar i) : out = VExpr.mkApps (.const c ls) args := by
  generalize hsrc : VExpr.mkApps (.const c ls) args = source at R
  induction R generalizing args with
  | refl => rfl
  | trans _ _ ih1 ih2 =>
    have h1 := ih1 ha hsrc
    exact (ih2 ha (hsrc.trans h1.symm)).trans h1
  | delta hd =>
    have hh := congrArg getAppFn hsrc
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh
    exact (hn _ _ hd).elim
  | @app f f' a a' Rf Ra ihf iha =>
    obtain ⟨args0, rfl, he⟩ := RigidHead.const.mkApps_eq_app hsrc
    have hf := ihf (fun a h => ha a (List.mem_append_left _ h)) he.symm
    obtain ⟨i, rfl⟩ := ha a (List.mem_append_right _ (by simp))
    rw [compute_bvar_eq Ra, hf]
  | beta | lam | forallE | proj =>
    have hh := congrArg getAppFn hsrc
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh

variable [Params]

theorem ProjectionCompute.bvar_spine_fixed
    (R : ProjectionCompute D (VExpr.mkApps (.const c ls) args) out)
    (hn : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (ha : ∀ a ∈ args, ∃ i, a = .bvar i) : out = VExpr.mkApps (.const c ls) args := by
  generalize hsrc : VExpr.mkApps (.const c ls) args = source at R
  induction R generalizing args with
  | base R => rw [← hsrc] at R ⊢; exact R.bvar_spine_fixed hn ha
  | trans _ _ ih1 ih2 =>
    have h1 := ih1 ha hsrc
    exact (ih2 ha (hsrc.trans h1.symm)).trans h1
  | @app f f' a a' Rf Ra ihf iha =>
    obtain ⟨args0, rfl, he⟩ := RigidHead.const.mkApps_eq_app hsrc
    have hf := ihf (fun a h => ha a (List.mem_append_left _ h)) he.symm
    obtain ⟨i, rfl⟩ := ha a (List.mem_append_right _ (by simp))
    rw [Ra.bvar_eq, hf]
  | projIota | lam | forallE | proj =>
    have hh := congrArg getAppFn hsrc
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh

theorem PatternCompute.bvar_spine_fixed
    (R : PatternCompute D (VExpr.mkApps (.const c ls) args) out)
    (hrigid : env.Rigid c) (hn : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (ha : ∀ a ∈ args, ∃ i, a = .bvar i) : out = VExpr.mkApps (.const c ls) args := by
  generalize hsrc : VExpr.mkApps (.const c ls) args = source at R
  induction R generalizing args with
  | base R => rw [← hsrc] at R ⊢; exact R.bvar_spine_fixed hn ha
  | trans _ _ ih1 ih2 =>
    have h1 := ih1 ha hsrc
    exact (ih2 ha (hsrc.trans h1.symm)).trans h1
  | pattern hp hm hc =>
    rw [← hsrc] at hm
    exact (hrigid.not_patternHeadsStoredRule (pat_storedRule hp)
      (matches_constHead (us := ls) hm (by rw [← VExpr.getAppFn_eq_fst]; simp [getAppFn_mkApps, getAppFn]))).elim
  | @app f f' a a' Rf Ra ihf iha =>
    obtain ⟨args0, rfl, he⟩ := RigidHead.const.mkApps_eq_app hsrc
    have hf := ihf (fun a h => ha a (List.mem_append_left _ h)) he.symm
    obtain ⟨i, rfl⟩ := ha a (List.mem_append_right _ (by simp))
    rw [Ra.bvar_eq, hf]
  | lam | forallE | proj =>
    have hh := congrArg getAppFn hsrc
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh

/-- Actual singleton prefixes cannot occur at a projection constructor head,
including prefixes with supplied arguments and indexed declarations. -/
theorem prefixUnfold_not_constructor
    (H : PrefixUnfold env univs recursorData Γ name levels args out)
    (hi : env.projections family info) : info.ctorName ≠ name := by
  cases H with
  | intro _ hr hname _ _ _ hg _ =>
    intro he
    obtain ⟨_, _, _, _, hseq, _⟩ := RecursorData.singletonUnfolding_spec hg
    obtain ⟨r, ru, hc, hof, hp⟩ := hr.singletonEquation hseq
    obtain ⟨index, howner, hgen⟩ := RecursorData.singletonEquation_eq hseq
    have hhead := hr.equation_head howner hgen
    have hrec := hof.2.1
    rw [lamBody_eq_stripLams, VExpr.headConst?_eq_some] at hrec
    obtain ⟨us, hrec⟩ := hrec
    rw [VExpr.getAppFn_eq_fst, hhead] at hrec
    have hrname := (VExpr.const.inj hrec).1.symm
    exact (henv.projectionCtorRigid hi).pats _ _ hp
      (by rw [SimplePattern.iota_headConst, hrname, hname, he])

/-- Every computational phase fixes a constructor applied only to variables. -/
theorem PrefixCompute.constructor_bvar_spine_fixed
    (R : PrefixCompute D Γ (VExpr.mkApps (.const info.ctorName ls) args) out)
    (hi : env.projections family info)
    (hn : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (ha : ∀ a ∈ args, ∃ i, a = .bvar i) :
    out = VExpr.mkApps (.const info.ctorName ls) args := by
  generalize hsrc : VExpr.mkApps (.const info.ctorName ls) args = source at R
  induction R generalizing args with
  | base R => rw [← hsrc] at R ⊢; exact R.bvar_spine_fixed (henv.projectionCtorRigid hi) hn ha
  | trans _ _ ih1 ih2 =>
    have h1 := ih1 ha hsrc
    exact (ih2 ha (hsrc.trans h1.symm)).trans h1
  | singleton H =>
    have hh := congrArg getAppFn hsrc
    simp only [getAppFn_mkApps, getAppFn] at hh
    exact (prefixUnfold_not_constructor H hi (VExpr.const.inj hh).1).elim
  | quotient H =>
    have hh := congrArg getAppFn hsrc
    simp only [getAppFn_mkApps, getAppFn] at hh
    exact (ClosedQuot.quotient_not_constructor H.registered hi (VExpr.const.inj hh).1).elim
  | @app Δ f f' a a' Rf Ra ihf iha =>
    obtain ⟨args0, rfl, he⟩ := RigidHead.const.mkApps_eq_app hsrc
    have hf := ihf (fun a h => ha a (List.mem_append_left _ h)) he.symm
    obtain ⟨i, rfl⟩ := ha a (List.mem_append_right _ (by simp))
    rw [Ra.bvar_eq, hf]
  | lam | forallE | proj =>
    have hh := congrArg getAppFn hsrc
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh

end Lean4Lean.VEnv.Strengthening.PureObservation
