import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEndpointBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointExample

/-! # General common comparison cannot be the beta induction invariant

Carrier-aware comparison accepts identity applications to two distinct values
of a positive empty structure. Beta exposes the distinct variables, which no
joint comparison can relate even with the full joint union. Carrier checking
still relates them. This refutes a general common-mode extension of proposition
beta transport, not the proposition-only law or declarative strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Distinct bare variables cannot compare in either joint mode. Computation
at constant/projection heads and carrier-aware applications cannot change this. -/
theorem ProofShape.JointCompare.bvar_injective
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : JointCompare Step Δ mode (.bvar i) (.bvar j)) : i = j := by
  generalize EA : ProofShape.bvar i = a at H
  generalize EB : ProofShape.bvar j = b at H
  change JointCheck Step Δ (.compare mode) a b at H
  generalize hk : JointCheckKind.compare mode = kind at H
  induction H generalizing mode i j with
  | leaf H =>
    cases H with
    | refl => exact ProofShape.bvar.inj (EA.trans EB.symm)
    | sort | const => cases EA
    | etaL H => obtain ⟨_, _, E, _⟩ := H.shape; cases EA.trans E
    | etaR H => obtain ⟨_, _, E, _⟩ := H.shape; cases EB.trans E
  | compute RA RB H ih =>
    exact ih ((EA ▸ RA).bvar_fixed hhead).symm ((EB ▸ RB).bvar_fixed hhead).symm hk
  | symm H ih => exact (ih EB EA hk).symm
  | structFields =>
    have E := congrArg ProofShape.constHead EA
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at E
    cases E
  | etaBodyR => cases EB
  | app | appCarrier | proj | lam | forallE | lamSorted | forallSorted | lamCommon | etaBodyL | etaLams => cases EA
  | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hk

private theorem identity_erasures
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hx : env.HasType univs Γ (.bvar i) (.const family ls)) :
    env.HasType univs Γ (.app (.lam (.const family ls) (.bvar 0)) (.bvar i)) (.const family ls) ∧
    proofErase Γ (.app (.lam (.const family ls) (.bvar 0)) (.bvar i)) =
      .app (.lam (.const family ls) (.bvar 0)) (.bvar i) := by
  have hΓS : OnCtx (.const family ls :: Γ) (env.IsType univs) := ⟨hΓ, _, hS⟩
  have hb : env.HasType univs (.const family ls :: Γ) (.bvar 0) (.const family ls) := .bvar .zero
  have hF : env.HasType univs Γ (.lam (.const family ls) (.bvar 0))
      (.forallE (.const family ls) (.const family ls)) := .lam hS hb
  have ht : env.HasType univs Γ (.app (.lam (.const family ls) (.bvar 0)) (.bvar i))
      (.const family ls) := .app hF hx
  have hn := not_proof_at_positive_type hΓ hS ht
  refine ⟨ht, ?_⟩
  rw [show proofErase Γ (.app (.lam (.const family ls) (.bvar 0)) (.bvar i)) = .app _ _ from if_neg hn]
  rw [show proofErase Γ (.lam (.const family ls) (.bvar 0)) = .lam _ _ from
    if_neg (not_isProof_fn hΓ hF hx hn)]
  rw [show proofErase Γ (.const family ls) = .const family ls from if_neg (not_isProof_of_sort hΓ hS)]
  rw [show proofErase (.const family ls :: Γ) (.bvar 0) = .bvar 0 from
    if_neg (not_proof_at_positive_type hΓS (hS.weak henv) hb)]
  rw [show proofErase Γ (.bvar i) = .bvar i from if_neg (not_proof_at_positive_type hΓ hS hx)]

/-- The identity peak is a typed source comparison at any primitive relation,
while its beta reducts have no common comparison in any target obeying the
primitive-head restriction. The same reducts retain an actual carrier guard. -/
theorem joint_unit_identity_beta_boundary
    (hhead : ∀ {Δ a b}, Target Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : info.nparams = 0) (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hiT : env.HasType univs Γ (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ (.bvar j) (.const family ls)) (hne : i ≠ j) :
    ∃ a b, env.HasType univs Γ a (.const family ls) ∧ env.HasType univs Γ b (.const family ls) ∧
      JointCompare Step (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b) ∧
      ProofShape.BetaRed (proofErase Γ a) (proofErase Γ (.bvar i)) ∧
      ProofShape.BetaRed (proofErase Γ b) (proofErase Γ (.bvar j)) ∧
      (¬ JointCompare Target (proofEraseCtx Γ) true
        (proofErase Γ (.bvar i)) (proofErase Γ (.bvar j))) ∧
      JointCarrierGuard Target (proofEraseCtx Γ) (proofErase Γ (.const family ls))
        (proofErase Γ (.bvar i)) (proofErase Γ (.bvar j)) := by
  obtain ⟨ha, Ea⟩ := identity_erasures hΓ hS hiT
  obtain ⟨hb, Eb⟩ := identity_erasures hΓ hS hjT
  have Ei : proofErase Γ (.bvar i) = .bvar i := if_neg (not_proof_at_positive_type hΓ hS hiT)
  have Ej : proofErase Γ (.bvar j) = .bvar j := if_neg (not_proof_at_positive_type hΓ hS hjT)
  have ES : proofErase Γ (.const family ls) = .const family ls := if_neg (not_isProof_of_sort hΓ hS)
  refine ⟨_, _, ha, hb, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Ea, Eb]
    have HR : ScopedTypeRecovery Step (proofEraseCtx Γ)
        (.lam (.const family ls) (.bvar 0)) (.forallE (.const family ls) (.const family ls)) := by
      exact .lam .bvar
    exact .appCarrier HR (.leaf .refl) (.carrierSubsingleton (.unit hi hx hf (ps := []) hp.symm))
  · rw [Ea, Ei]
    simpa only [ProofShape.inst_eq_subst, ProofShape.subst, ProofShape.Subst.one,
      ProofShape.Subst.cons, ProofShape.Subst.liftN] using
      (ProofShape.BetaRed.beta (A := .const family ls) (b := .bvar 0) (a := .bvar i))
  · rw [Eb, Ej]
    simpa only [ProofShape.inst_eq_subst, ProofShape.subst, ProofShape.Subst.one,
      ProofShape.Subst.cons, ProofShape.Subst.liftN] using
      (ProofShape.BetaRed.beta (A := .const family ls) (b := .bvar 0) (a := .bvar j))
  · rw [Ei, Ej]
    exact fun H => hne (H.bvar_injective hhead)
  · rw [ES]
    exact .carrierSubsingleton (.unit hi hx hf (ps := []) hp.symm)

/-- A closed positive empty structure supplies a concrete two-variable context
for the obstruction. Its source certificate is already at stage zero, while
its two beta reducts fail comparison in the entire joint union. -/
theorem joint_unit_identity_beta_boundary_context
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ∃ Γ a b, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ a (.const family ls) ∧ env.HasType univs Γ b (.const family ls) ∧
      JointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b) ∧
      ProofShape.BetaRed (proofErase Γ a) (.bvar 0) ∧
      ProofShape.BetaRed (proofErase Γ b) (.bvar 1) ∧
      (¬ JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true (.bvar 0) (.bvar 1)) ∧
      JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx Γ) (.const family ls) (.bvar 0) (.bvar 1) := by
  let S := VExpr.const family ls
  let Γ := [S, S]
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨⟨trivial, _, hS⟩, _, hS.weak0 henv.ordered⟩
  have hSΓ : env.HasType univs Γ S (.sort (.succ u)) := hS.weak0 henv.ordered
  have h₀ : env.HasType univs Γ (.bvar 0) S := .bvar .zero
  have h₁ : env.HasType univs Γ (.bvar 1) S := .bvar (.succ .zero)
  obtain ⟨a, b, ha, hb, HC, RA, RB, Hno, HG⟩ :=
    joint_unit_identity_beta_boundary (Step := ErasedJointStage D 0)
      (Target := ErasedJointUnion D) erased_joint_union_head hΓ hi hp hx hf hSΓ h₀ h₁ (by decide)
  have E₀ : proofErase Γ (.bvar 0) = .bvar 0 := if_neg (not_proof_at_positive_type hΓ hSΓ h₀)
  have E₁ : proofErase Γ (.bvar 1) = .bvar 1 := if_neg (not_proof_at_positive_type hΓ hSΓ h₁)
  have ES : proofErase Γ (.const family ls) = .const family ls := if_neg (not_isProof_of_sort hΓ hSΓ)
  rw [E₀] at RA
  rw [E₁] at RB
  rw [E₀, E₁] at Hno
  rw [ES, E₀, E₁] at HG
  exact ⟨Γ, a, b, hΓ, ha, hb, HC, RA, RB, Hno, HG⟩

/-- Even the whole joint union fails general common-mode endpoint beta
stability in any context containing distinct variables of a positive empty
structure. This counterexample needs neither recursive definitions nor a cast;
it does not refute proposition-only beta transport. -/
theorem joint_common_beta_stability_not_of_unit
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : info.nparams = 0) (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hiT : env.HasType univs Γ (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ (.bvar j) (.const family ls)) (hne : i ≠ j) :
    ¬ JointCommonBetaStability (ErasedJointUnion D) := by
  intro Hbeta
  obtain ⟨a, b, ha, hb, HC, RA, RB, Hno, _⟩ :=
    joint_unit_identity_beta_boundary (Step := ErasedJointUnion D)
      erased_joint_union_head hΓ hi hp hx hf hS hiT hjT hne
  have H := Hbeta hΓ ha hb HC RB
  obtain ⟨b', Rb, Eb⟩ := proofErase_beta_replay hΓ hb RB
  have hb' := (beta_eq hΓ hb Rb).hasType.2
  rw [← Eb] at H
  have H' := Hbeta hΓ hb' ha H.symm RA
  rw [Eb] at H'
  exact Hno H'.symm

end Lean4Lean.VEnv.Strengthening
