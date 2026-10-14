import Lean4Lean.Theory.Typing.Strengthening.SymmetricFullStep
import Lean4Lean.Theory.Typing.Strengthening.NeutralRecursorFixed

/-! # Neutral head constraints on symmetric phases

At a sort-typed projection endpoint, symmetric terminal eta still reflects a
projection in the original source. A projection of a variable is computationally
fixed. Consequently a fixed neutral recursor spine cannot have a symmetric
phase to such a projection. This locates a missing structure-readout equation;
it does not assert a counterexample to strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- Eta expansion on the right preserves the projection head at a sort type,
so ordinary normal reflection still recovers a projection on the left. -/
theorem EtaJoin.sort_proj_source (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.proj family index major) (.sort u))
    (H : EtaJoin Γ e (.proj family index major)) :
    ∃ major', e = .proj family index major' := by
  obtain ⟨left, right, RL, RR, HN⟩ := H
  obtain ⟨major', rfl⟩ := RR.sort_proj_out hΓ ht
  exact EtaNormal.sort_proj_source hΓ (RR.simAt hΓ _ ht).hasType.2 ⟨left, RL, HN⟩

private theorem pattern_projection_bvar_fixed
    (R : PatternStep D (.proj family index (.bvar i)) out) :
    out = .proj family index (.bvar i) := by
  generalize hsrc : VExpr.proj family index (.bvar i) = source at R
  cases R with
  | pattern hp _ hm _ =>
    obtain ⟨_, hh⟩ := (Params.constHeaded hp).matches_head hm
    rw [← hsrc] at hh
    cases hh
  | proj R =>
    cases hsrc
    rw [R.toCompute.bvar_eq]
  | projIota =>
    have hh := congrArg getAppFn (VExpr.proj.inj hsrc).2.2
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh
  | delta | beta | appL | appR | lamL | lamR | forallL | forallR => cases hsrc

/-- No compatible actual computation changes a projection of a bare variable. -/
theorem PrefixCompute.projection_bvar_fixed
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (R : PrefixCompute D Γ (.proj family index (.bvar i)) out) :
    out = .proj family index (.bvar i) := by
  apply prefix_induct_steps hcon R (P := fun x => x = .proj family index (.bvar i)) rfl
  intro x y R he
  subst x
  generalize hsrc : VExpr.proj family index (.bvar i) = source at R
  cases R with
  | base R => exact (pattern_projection_bvar_fixed (hsrc ▸ R)).trans hsrc
  | singleton | quotient =>
    have hh := congrArg getAppFn hsrc
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh
  | proj R => cases hsrc; rw [R.toCompute.bvar_eq]
  | appL | appR | lamL | lamR | forallL | forallR => cases hsrc

/-- Fixed neutral recursor applications and sort-typed variable projections
cannot have a symmetric phase when the chosen equations do not unfold that
recursor. Thus a readout path between these endpoints needs extra computation. -/
theorem neutral_recursor_not_symmetric_phase
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.proj family index (.bvar i)) (.sort u))
    (hreg : recursorData c = some data) (hz : ¬ data.sourceLevel ls ≈ .zero)
    (hn : ∀ rhs, ¬ D.unfolds c ls rhs)
    (ha : ∀ a ∈ args, ∀ name levels, getAppFn a ≠ .const name levels)
    (hfix : ∀ a ∈ args, ∀ out, PrefixCompute D Γ a out → out = a) :
    ¬ PrefixEtaJoin D Γ (mkApps (.const c ls) args) (.proj family index (.bvar i)) := by
  rintro ⟨a0, b0, RA, RB, HJ⟩
  cases RA.neutral_recursor_fixed hcon hreg hz hn ha hfix
  cases RB.projection_bvar_fixed hcon
  obtain ⟨major, he⟩ := HJ.sort_proj_source hΓ ht
  have hh := congrArg getAppFn he
  simp only [getAppFn_mkApps, getAppFn] at hh
  cases hh

end Lean4Lean.VEnv.Strengthening.PureObservation
