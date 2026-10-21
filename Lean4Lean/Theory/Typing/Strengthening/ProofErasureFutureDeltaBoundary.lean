import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureApplicationBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaStableJoint

/-! # Future common certificates need not survive delta computation

A declared constant of type Unit → Unit hides its arguments from every beta
future, including after interpreted substitution. Unfolding it to the identity
exposes distinct unit variables. They still have a carrier guard, but no common
comparison, even in the full joint union. This tests endpoint computation of
future certificates; it does not refute carrier transport or strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
open private identity_erasures
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCommonBetaBoundary
variable [Params]

private theorem constant_unit_beta (hi : env.projections family info)
    (hp : info.nparams = 0) (hx : info.nindices = 0) (hf : info.numFields = 0)
    (HR : ScopedTypeRecovery Step Δ (.const c ls) (.forallE (.const family us) B))
    (RA : ProofShape.BetaRed (.app (.const c ls) a) p)
    (RB : ProofShape.BetaRed (.app (.const c ls) b) q) :
    JointCompare Step Δ true p q := by
  obtain ⟨args, rfl, HA⟩ := RA.const_spine (args := [a])
  obtain ⟨args', rfl, HB⟩ := RB.const_spine (args := [b])
  cases HA with
  | cons _ HA =>
    cases HA
    cases HB with
    | cons _ HB =>
      cases HB
      exact .appCarrier HR (.leaf .refl)
        (.carrierSubsingleton (.unit hi hx hf (ps := []) hp.symm))

/-- A constant application with a recoverable unit domain has a full future
common certificate for arbitrary arguments. Recovery is supplied in every
future context; beta and substitution leave the constant head intact. -/
theorem constant_unit_application_family (hi : env.projections family info)
    (hp : info.nparams = 0) (hx : info.nindices = 0) (hf : info.numFields = 0)
    (HR : ∀ Δ, ScopedTypeRecovery Step Δ (.const c ls) (.forallE (.const family us) B)) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ
      (.app (.const c ls) a) (.app (.const c ls) b) := by
  refine ⟨fun R S => constant_unit_beta hi hp hx hf (HR _) R S, ?_⟩
  intro Δ' τ p q _ R S
  simp only [ProofShape.subst] at R S
  exact constant_unit_beta hi hp hx hf (HR _) R S

private theorem constant_unit_recovery
    (hc : env.constants c = some ⟨0, .forallE (.const family []) (.const family [])⟩)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ScopedTypeRecovery Step Δ (.const c [])
      (.forallE (.const family []) (.const family [])) := by
  have hΓS : OnCtx [VExpr.const family []] (env.IsType univs) := ⟨trivial, _, hS⟩
  have hF := HasType.forallE hS (hS.weak henv)
  have EF : proofErase [] (.forallE (.const family []) (.const family [])) =
      .forallE (.const family []) (.const family []) := by
    rw [show proofErase [] (.forallE (.const family []) (.const family [])) =
      .forallE _ _ from if_neg (not_isProof_of_sort (by trivial) hF)]
    rw [show proofErase [] (.const family []) = .const family [] from
      if_neg (not_isProof_of_sort (by trivial) hS)]
    rw [show proofErase [VExpr.const family []] (.const family []) = .const family [] from
      if_neg (not_isProof_of_sort hΓS (hS.weak henv))]
  rw [← EF]
  exact .const hc (by simp) rfl

private theorem constant_unit_erasures
    (hc : env.constants c = some ⟨0, .forallE (.const family []) (.const family [])⟩)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family []) (.sort (.succ u)))
    (hv : env.HasType univs Γ (.bvar i) (.const family [])) :
    env.HasType univs Γ (.app (.const c []) (.bvar i)) (.const family []) ∧
    proofErase Γ (.app (.const c []) (.bvar i)) = .app (.const c []) (.bvar i) := by
  have hF : env.HasType univs Γ (.const c [])
      (.forallE (.const family []) (.const family [])) := .const hc (by simp) rfl
  have ht : env.HasType univs Γ (.app (.const c []) (.bvar i)) (.const family []) := .app hF hv
  have hn := not_proof_at_positive_type hΓ hS ht
  refine ⟨ht, ?_⟩
  rw [show proofErase Γ (.app (.const c []) (.bvar i)) = .app _ _ from if_neg hn,
    show proofErase Γ (.const c []) = .const c [] from if_neg (not_isProof_fn hΓ hF hv hn),
    show proofErase Γ (.bvar i) = .bvar i from if_neg (not_proof_at_positive_type hΓ hS hv)]

/-- Given a closed positive unit and a declared identity unfolding, two typed
constant applications have full future common certificates even with no
primitives. Certified delta and beta expose endpoints with no common comparison
in the full union. Their full future unit carrier certificate survives. No soundness assumption
on unrelated definitions is needed for this explicit computation. -/
theorem unit_constant_future_compute_failure
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hc : env.constants c = some ⟨0, .forallE (.const family []) (.const family [])⟩)
    (hd : D.unfolds c [] (.lam (.const family []) (.bvar 0)))
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hiT : env.HasType univs Γ (.bvar i) (.const family []))
    (hjT : env.HasType univs Γ (.bvar j) (.const family [])) (hne : i ≠ j) :
    ∃ a b, env.HasType univs Γ a (.const family []) ∧
      env.HasType univs Γ b (.const family []) ∧
      BetaStableFamily (fun Δ => JointCompare (fun _ _ _ => False) Δ true)
        (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b) ∧
      ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ a) (.bvar i) ∧
      ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ b) (.bvar j) ∧
      (¬ JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true (.bvar i) (.bvar j)) ∧
      BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ)
        (.const family []) (.bvar i) (.bvar j) := by
  have hSΓ := hS.weak0 (Γ := Γ) henv.ordered
  obtain ⟨ha, Ea⟩ := constant_unit_erasures hc hΓ hSΓ hiT
  obtain ⟨hb, Eb⟩ := constant_unit_erasures hc hΓ hSΓ hjT
  obtain ⟨hidapp, Eidapp⟩ := identity_erasures hΓ hSΓ hiT
  have Eid : proofErase [] (.lam (.const family []) (.bvar 0)) =
      .lam (.const family []) (.bvar 0) := by
    have Eapp : proofErase Γ (.app (.lam (.const family []) (.bvar 0)) (.bvar i)) =
        .app (proofErase Γ (.lam (.const family []) (.bvar 0))) (proofErase Γ (.bvar i)) :=
      if_neg (not_proof_at_positive_type hΓ hSΓ hidapp)
    rw [Eapp] at Eidapp
    have E := (ProofShape.app.inj Eidapp).1
    rw [proofErase_closed_context (D.closed hd) (HasType.lam hS (.bvar .zero)) hΓ] at E
    exact E
  have RD : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (.const c []) (.lam (.const family []) (.bvar 0)) := by
    rw [← Eid]
    exact .base (.inl (.inl (.inl (.delta hd))))
  have R (k) : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (.app (.const c []) (.bvar k)) (.bvar k) := by
    refine .trans (.app RD .refl) (.beta ?_)
    simpa only [ProofShape.inst_eq_subst, ProofShape.subst, ProofShape.Subst.one,
      ProofShape.Subst.cons, ProofShape.Subst.liftN] using
      (ProofShape.BetaRed.beta (A := .const family []) (b := .bvar 0) (a := .bvar k))
  refine ⟨_, _, ha, hb, ?_, Ea ▸ R i, Eb ▸ R j, ?_, ?_⟩
  · rw [Ea, Eb]
    exact constant_unit_application_family hi hp hx hf (fun _ => constant_unit_recovery hc hS)
  · exact fun H => hne (H.bvar_injective erased_joint_union_head)
  · exact .subsingleton (.unit hi hx hf (ps := []) hp.symm)

/-- The closed unit supplies a concrete two-variable context. Thus failure of
future common-certificate computation requires no hypothesized ambient typing
or inequality of arbitrary terms. The environment assumptions are the unit's
registration and positive typing and the constant's declaration and unfolding;
this does not construct a canonical-Eq strengthening counterexample. -/
theorem unit_constant_future_compute_context
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hc : env.constants c = some ⟨0, .forallE (.const family []) (.const family [])⟩)
    (hd : D.unfolds c [] (.lam (.const family []) (.bvar 0)))
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ a b, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ a (.const family []) ∧ env.HasType univs Γ b (.const family []) ∧
      BetaStableFamily (fun Δ => JointCompare (fun _ _ _ => False) Δ true)
        (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b) ∧
      ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ a) (.bvar 0) ∧
      ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ b) (.bvar 1) ∧
      (¬ JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true (.bvar 0) (.bvar 1)) ∧
      BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ)
        (.const family []) (.bvar 0) (.bvar 1) := by
  let S := VExpr.const family []
  let Γ := [S, S]
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨⟨trivial, _, hS⟩, _, hS.weak0 henv.ordered⟩
  have hiT : env.HasType univs Γ (.bvar 0) S := .bvar .zero
  have hjT : env.HasType univs Γ (.bvar 1) S := .bvar (.succ .zero)
  obtain ⟨a, b, H⟩ := unit_constant_future_compute_failure hi hp hx hf hc hd hS hΓ hiT hjT (by decide)
  exact ⟨Γ, a, b, hΓ, H⟩

end Lean4Lean.VEnv.Strengthening
