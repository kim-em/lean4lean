import Lean4Lean.Theory.Typing.Strengthening.ProofErasureClosedCarrierReadout

/-! # Carrier checking at a type equal to a universe

Actual equality to a sort rules out every exposed function or record carrier
in the joint derivation. Replaying carrier computation therefore leaves only
common checking and its endpoint-computation/symmetry closure. No semantic
sort-exposure path or general carrier-conversion law is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

private theorem carrier_sort_raw
    (hstep : ErasedScopedPrimitiveDescent Step)
    (H : JointCheck Step Δ kind a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (HE : env.IsDefEqU univs Γ A (.sort v))
    (EΓ : proofEraseCtx Γ = Δ)
    (E : JointCheckKind.carrier (proofErase Γ A) = kind) :
    JointCompare Step Δ true a b := by
  induction H generalizing Γ A u with
  | carrierChecked HC => exact HC
  | carrierFunction =>
    obtain ⟨D, C, rfl, _, _, _⟩ := erase_forallE_inv (JointCheckKind.carrier.inj E)
    exact (henv.headInversion.sort_forallE hΓ (HE.typeChain henv hΓ hA).symm).elim
  | carrierSubsingleton HS =>
    cases HS with
    | unit hi hz hf hp =>
      obtain ⟨args, rfl, _⟩ := proofErase_const_spine_inv (JointCheckKind.carrier.inj E)
      exact (henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
        (HE.typeChain henv hΓ hA).symm).elim
    | forallE HS =>
      obtain ⟨D, C, rfl, _, _, _⟩ := erase_forallE_inv (JointCheckKind.carrier.inj E)
      exact (henv.headInversion.sort_forallE hΓ (HE.typeChain henv hΓ hA).symm).elim
  | carrierSymm HC ih => exact .symm (ih hΓ hA HE EΓ E)
  | carrierReduce RA RB HC ih => exact .compute RA RB (ih hΓ hA HE EΓ E)
  | carrierCompute R HC ih =>
    obtain ⟨A', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ
      (JointCheckKind.carrier.inj E) R
    exact ih hΓ HA.hasType.2 (HA.symm.toU.trans henv hΓ HE) EΓ (congrArg JointCheckKind.carrier EA)
  | carrierIntro hi hz hp hadm HF =>
    obtain ⟨args, rfl, _⟩ := proofErase_const_spine_inv (JointCheckKind.carrier.inj E)
    exact (henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
      (HE.typeChain henv hΓ hA).symm).elim
  | carrierNested hi hz hp hadm HT HF =>
    obtain ⟨args, rfl, _⟩ := proofErase_const_spine_inv (JointCheckKind.carrier.inj E)
    exact (henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
      (HE.typeChain henv hΓ hA).symm).elim
  | leaf | app | appCarrier | proj | lam | forallE | lamSorted | forallSorted | lamCommon |
      etaBodyL | etaBodyR | structFields | etaLams | compute | symm => cases E

/-- Any joint guard at an actual type equal to a universe yields common
checking of its raw endpoints. The carrier need not display or compute to a
sort. Its supplied actual equality suffices to exclude all structural carrier
cases; primitive soundness handles carrier-computation prefixes. -/
theorem proofErase_joint_carrier_semantic_sort
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (HE : env.IsDefEqU univs Γ A (.sort v))
    (H : JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A) a b) :
    JointCompare Step (proofEraseCtx Γ) true a b :=
  carrier_sort_raw hstep H hΓ hA HE rfl rfl

/-- Full future checking at a carrier equal to a universe is exactly full
future common checking. Unlike general carrier conversion, this needs no type
comparison certificate, no primitive head-shape assumption, and no exposure
path. Actual carrier equality substitutes into every future context. -/
theorem proofErase_future_carrier_semantic_sort_iff
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ A (.sort v) (.sort u)) :
    BetaStableCarrier Step (proofEraseCtx Γ) (proofErase Γ A) a b ↔
      BetaStableFamily (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ) a b := by
  constructor
  · intro H
    constructor
    · intro p q RP RQ
      exact proofErase_joint_carrier_semantic_sort hstep hΓ HE.hasType.1 HE.toU (H.1 .refl RP RQ)
    · intro Δ' τ p q W RP RQ
      have HG := H.2 W .refl RP RQ
      obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
      rw [← proofErase_subst_with hΓ₀ WS HE.hasType.1 ES, ← EΓ₀] at HG
      rw [← EΓ₀]
      have HE' := HE.subst henv WS
      exact proofErase_joint_carrier_semantic_sort hstep hΓ₀ HE'.hasType.1 HE'.toU HG
  · exact fun H => H.carrier

end Lean4Lean.VEnv.Strengthening
