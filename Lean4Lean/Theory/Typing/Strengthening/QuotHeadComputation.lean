import Lean4Lean.Theory.Typing.Strengthening.ClosedQuotUnfolding

/-! # Closed quotient unfolding in computational head exposure

A derived, closed Quot.lift equation is added to the actual declaration collection.
Every generated Prop-source quotient prefix then becomes one constant unfolding
followed by beta reduction. Its replay uses no occurrence-specific typing checks.
-/
namespace Lean4Lean.VEnv.Strengthening.ClosedQuot
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
open PureObservation (Definitions Compute ProjectionCompute)

/-- Actual closed declarations plus the proved Prop-source Quot.lift equation. -/
def definitions (env : VEnv) (U : Nat) (henv : env.WF) (hr : QuotRegistered env) : Definitions where
  unfolds c ls rhs := (Definitions.ofEnv env U henv).unfolds c ls rhs ∨
    c = ``Quot.lift ∧ ∃ u v, ls = [u,v] ∧ u.WF U ∧ v.WF U ∧ u ≈ .zero ∧ rhs = value u v
  closed := by
    rintro c ls rhs (h | ⟨rfl, u, v, rfl, hu, hv, hz, rfl⟩)
    · exact (Definitions.ofEnv env U henv).closed h
    · exact value_closed henv hr hu hv hz

/-- The extra equation is sound in every context by weakening its closed proof. -/
theorem definitions_sound (henv : env.WF) (hr : QuotRegistered env) :
    (definitions env U henv hr).Sound env U := by
  rintro Γ c ls rhs (h | ⟨rfl, u, v, rfl, hu, hv, hz, rfl⟩)
  · exact Definitions.ofEnv_sound henv _ _ _ _ h
  · exact ⟨_, (equation henv hr hu hv hz).weak0 henv.ordered⟩

/-- Constant computation is compatible with an arbitrary supplied argument spine. -/
theorem compute_mkApps (R : Compute D f f') (args : List VExpr) :
    Compute D (mkApps f args) (mkApps f' args) := by
  induction args generalizing f f' with
  | nil => exact R
  | cons a args ih => exact ih (.app R .refl)

/-- Every generated quotient prefix is a computational path using the one closed
constant equation. There are no ambient replay or source typing premises. -/
theorem generated_compute (henv : env.WF) (hr : QuotRegistered env)
    (hu : u.WF U) (hv : v.WF U) (hz : u ≈ .zero)
    (hg : QuotPrefixUnfolding.generate [u,v] args = some program) :
    Compute (definitions env U henv hr) (mkApps (.const ``Quot.lift [u,v]) args) program.rhs := by
  have hd : Compute (definitions env U henv hr) (.const ``Quot.lift [u,v]) (value u v) :=
    .delta (.inr ⟨rfl, u, v, rfl, hu, hv, hz, rfl⟩)
  exact (compute_mkApps hd args).trans (.of_beta (value_prefix_beta hg))

/-- Every checked quotient prefix embeds, independently of the context in which
its occurrence-specific checks were supplied. -/
theorem prefix_compute (henv : env.WF) (hr : QuotRegistered env)
    (H : QuotPrefixUnfold env U Γ levels args rhs) :
    Compute (definitions env U henv hr) (mkApps (.const ``Quot.lift levels) args) rhs := by
  cases H with
  | intro _ hw hz hg _ =>
    have hl := (QuotPrefixUnfolding.generate_spec hg).1
    cases levels with
    | nil => cases hl
    | cons u levels =>
      cases levels with
      | nil => cases hl
      | cons v levels =>
        cases levels with
        | nil => exact generated_compute henv hr (hw _ (by simp)) (hw _ (by simp)) hz hg
        | cons => simp at hl

/-- A checked quotient prefix above a lift yields a computational equality below,
using only the source typing below. No ambient capture typing is strengthened. -/
theorem prefix_descend (henv : env.WF) (hr : QuotRegistered env)
    (H : QuotPrefixUnfold env U Γ' levels (args.map (·.lift' ρ)) rhs)
    (hΓ : OnCtx Γ (env.IsType U))
    (ht : HasType env U Γ (mkApps (.const ``Quot.lift levels) args) T) :
    ∃ rhs₀, rhs = rhs₀.lift' ρ ∧ IsDefEq env U Γ (mkApps (.const ``Quot.lift levels) args) rhs₀ T := by
  have R := prefix_compute henv hr H
  have R' : Compute (definitions env U henv hr)
      ((mkApps (.const ``Quot.lift levels) args).lift' ρ) rhs := by
    simpa only [VExpr.lift'_mkApps, VExpr.lift'] using R
  obtain ⟨rhs₀, R0, he⟩ := R'.lift_inv
  exact ⟨rhs₀, he, R0.simAt henv (definitions_sound henv hr) hΓ T ht⟩

/-- Reflect a quotient-prefix equation when both endpoints are already given
below the lift. This is an exact strengthening theorem for this reduction rule. -/
theorem prefix_reflect (henv : env.WF) (hr : QuotRegistered env)
    (H : QuotPrefixUnfold env U Γ' levels (args.map (·.lift' ρ)) (rhs.lift' ρ))
    (hΓ : OnCtx Γ (env.IsType U))
    (ht : HasType env U Γ (mkApps (.const ``Quot.lift levels) args) T) :
    IsDefEq env U Γ (mkApps (.const ``Quot.lift levels) args) rhs T := by
  obtain ⟨rhs₀, he, h⟩ := prefix_descend henv hr H hΓ ht
  cases VExpr.lift'_inj.1 he
  exact h

section
open Params
variable [Params]

/-- Quot.lift is not a projection constructor, since its stored equation has
that head and actual projection constructors are rigid. -/
theorem quotient_not_constructor (hr : QuotRegistered Params.env)
    (hi : Params.env.projections s info) : info.ctorName ≠ ``Quot.lift := by
  intro hn
  exact (henv.projectionCtorRigid hi).defeqs quotDefEq hr.equation [.param 0, .param 1]
    (by rw [hn]; rfl)

/-- Adding the quotient equation preserves the rigidity required by structure eta. -/
theorem definitions_rigid (hr : QuotRegistered Params.env) :
    FieldObservation.ConstructorRigid (definitions Params.env univs henv hr) := by
  rintro s info hi ls rhs (h | ⟨hn, _⟩)
  · exact Definitions.ofEnv_no_rigid henv (henv.projectionCtorRigid hi) h
  · exact quotient_not_constructor hr hi hn

/-- An actual quotient prefix is available inside the mixed observation path. -/
theorem prefix_etaCompute (hr : QuotRegistered Params.env)
    (H : QuotPrefixUnfold Params.env univs Γ levels args rhs) :
    FieldObservation.EtaCompute (definitions Params.env univs henv hr)
      (mkApps (.const ``Quot.lift levels) args) rhs :=
  .compute (.base (prefix_compute henv hr H))

/-- The existing mixed head-exposure theorem now includes every checked quotient
prefix, with all extra declaration soundness and constructor-rigidity discharged. -/
theorem function_type_below (hr : QuotRegistered Params.env)
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hf : HasType Params.env univs Γ f T)
    (R : FieldObservation.EtaCompute (definitions Params.env univs henv hr)
      (T.lift' ρ) (.forallE A B)) :
    ∃ A' B', HasType Params.env univs Γ f (.forallE A' B') ∧
      IsDefEqU Params.env univs Γ T (.forallE A' B') :=
  R.function_type_below (definitions_rigid hr) (definitions_sound henv hr) hΓ hf

end
end Lean4Lean.VEnv.Strengthening.ClosedQuot
