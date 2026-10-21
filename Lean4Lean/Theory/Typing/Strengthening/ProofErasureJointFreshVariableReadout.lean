import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTypeExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCarrierExposure

/-! # Fresh variables cannot be synthesized by inferred comparison

Inferred comparison against a bare variable contains a computation to that
same variable. Primitive descent therefore excludes comparison of a lifted
typed source with a variable in the newly inserted block.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape

private theorem bvar_fixed
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ (.bvar i) out) : out = .bvar i := by
  obtain ⟨args, E, HA⟩ := (show ScopedCompute Step Δ (mkApps (.bvar i) []) out from R).bvar_spine hhead
  cases HA
  exact E

variable [Params]

private theorem bvar_compute_pair
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : JointCheck Step Δ kind sa sb) (hk : kind = .compare false) :
    (∀ i, sa = .bvar i → ScopedCompute Step Δ sb (.bvar i)) ∧
    (∀ i, sb = .bvar i → ScopedCompute Step Δ sa (.bvar i)) := by
  induction H with
  | leaf H =>
    cases hk
    cases H with
    | refl => exact ⟨fun _ E => E ▸ .refl, fun _ E => E ▸ .refl⟩
    | sort | const => constructor <;> intro i E <;> cases E
  | compute RA RB HC ih =>
    have IH := ih hk
    constructor
    · intro i E
      have EA := bvar_fixed hhead (E ▸ RA)
      exact RB.trans (IH.1 i EA)
    · intro i E
      have EB := bvar_fixed hhead (E ▸ RB)
      exact RA.trans (IH.2 i EB)
  | symm H ih => exact (ih hk).symm
  | app | appCarrier | proj | lam | forallE | lamSorted | forallSorted | etaLams =>
    constructor <;> intro i E <;> cases E
  | lamCommon | etaBodyL | etaBodyR | structFields | carrierIntro | carrierChecked |
      carrierSubsingleton | carrierFunction | carrierSymm | carrierCompute | carrierReduce |
      carrierNested => cases hk

/-- Inferred checking against a bare variable supplies a directed computation
to that variable, even when the certificate contains symmetry and computation. -/
theorem ProofShape.JointCompare.inferred_bvar_compute
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : JointCompare Step Δ false source (.bvar i)) :
    ScopedCompute Step Δ source (.bvar i) := (bvar_compute_pair hhead H rfl).2 i rfl

/-- Even common checking distinguishes two bare variables. Eta and structural
checking cannot start with bare variables on both sides, and computation fixes
both indices. This statement needs no original typing hypotheses. -/
theorem ProofShape.JointCompare.bvar_indices
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : JointCompare Step Δ mode (.bvar i) (.bvar j)) : i = j := by
  generalize Ei : ProofShape.bvar i = a at H
  generalize Ej : ProofShape.bvar j = b at H
  change JointCheck Step Δ (.compare mode) a b at H
  generalize hk : JointCheckKind.compare mode = kind at H
  induction H generalizing mode i j with
  | leaf H => cases H with
    | refl => exact ProofShape.bvar.inj (Ei.trans Ej.symm)
    | sort | const => cases Ei
    | etaL H => obtain ⟨_, _, E, _⟩ := H.shape; cases Ei.trans E
    | etaR H => obtain ⟨_, _, E, _⟩ := H.shape; cases Ej.trans E
  | compute RA RB HC ih =>
    exact ih (bvar_fixed hhead (Ei ▸ RA)).symm (bvar_fixed hhead (Ej ▸ RB)).symm hk
  | symm H ih => exact (ih Ej Ei hk).symm
  | structFields =>
    have E := congrArg constHead Ei
    simp only [constHead_mkApps, constHead] at E
    cases E
  | app | appCarrier | proj | lam | forallE | lamSorted | forallSorted | lamCommon | etaBodyL | etaLams => cases Ei
  | etaBodyR => cases Ej
  | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction | carrierSymm |
      carrierCompute | carrierReduce | carrierNested => cases hk

/-- Inferred checking cannot identify a lifted typed source with any fresh
variable in an inserted front block. The contradiction uses exact computation
descent and the range of lifting, not semantic strengthening. -/
theorem proofErase_joint_inferred_no_fresh_variable
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n 0 Γ Γ') (ht : env.HasType univs Γ e T) (hi : i < n)
    (H : JointCompare Step (proofEraseCtx Γ') false ((proofErase Γ e).liftN n) (.bvar i)) : False := by
  obtain ⟨e', _, E⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ' W ht rfl
    (H.inferred_bvar_compute hhead)
  generalize Er : proofErase Γ e' = raw at E
  cases raw <;> simp_all [ProofShape.liftN, liftVar]
  omega

/-- For sort-typed endpoints common checking cannot hide a fresh variable
either. Typed mode inversion reduces this case to the raw inferred readout. -/
theorem proofErase_joint_types_no_fresh_variable
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n 0 Γ Γ') (ht : env.HasType univs Γ e (.sort u))
    (hv : env.HasType univs Γ' (.bvar i) (.sort v)) (hi : i < n)
    (H : JointCompare Step (proofEraseCtx Γ') mode
      (proofErase Γ' (e.liftN n)) (proofErase Γ' (.bvar i))) : False := by
  have HC := proofErase_joint_types_inferred hstep hΓ' (ht.weakN henv W) hv H
  rw [proofErase_liftN hΓ hΓ' W ht,
    show proofErase Γ' (.bvar i) = .bvar i from if_neg (not_isProof_of_sort hΓ' hv)] at HC
  exact proofErase_joint_inferred_no_fresh_variable hstep hhead hΓ hΓ' W ht hi HC

end Lean4Lean.VEnv.Strengthening
