import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointNativeEqRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointImageComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeSupplyJoin

/-! # Native telescope computation with retained original recoveries

Instantiate a typed body path at its original recoverable argument before
computing that argument in the output. Computed arguments need no recovery.
This orders the substitution square without unrestricted union substitution.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Typed union body computation and argument computation form a directed
substitution square when only the original argument recovers its assigned
type. The computed argument need not retain that recovery. -/
theorem proofErase_joint_union_compute_inst_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (RB : ScopedCompute (ErasedJointUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) out)
    (RX : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ x) image) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (out.inst image) := by
  have RI := proofErase_joint_union_compute_inst heq hs hΓA.1 hx HR hb RB
  rw [← proofErase_instN hΓA hx Ctx.InstN.zero hb] at RI
  obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize
    (erased_joint_union_descent heq hs) hΓA hb rfl rfl RB
  obtain ⟨stage, RX⟩ := RX.finite_stage erased_joint_stage_mono
  have RXB := proofErase_joint_compute_inst_argument heq hs hΓA HB.hasType.2 hx RX
  rw [proofErase_instN hΓA hx Ctx.InstN.zero HB.hasType.2, EB] at RXB
  exact RI.trans (RXB.mono (fun H => ⟨stage, H⟩))

/-- Supply one computed argument to a computed typed Pi. Native body
instantiation computes to the supplied raw body without a recovery premise
on the computed argument or general substitution closure. -/
theorem proofErase_joint_union_computed_pi_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v)) (hx : env.HasType univs Γ x A)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (RT : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (.forallE rawA rawB))
    (RX : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ x) image) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (B.inst x)) (rawB.inst image) := by
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB))] at RT
  obtain ⟨_, _, HE, _, RB⟩ := proofErase_joint_union_forallE_inv heq hs hΓ hA hB rfl RT
  cases HE
  exact proofErase_joint_union_compute_inst_square heq hs ⟨hΓ, u, hA⟩ hB hx HR RB RX

/-- A literal native telescope walk retaining recovery of each original
non-proof argument at its actual assigned domain. No recovery of later
computed argument images is included or required. -/
inductive RecoverableNativeWalk (D : PureObservation.Definitions) (Γ : List VExpr) :
    VExpr → List VExpr → VExpr → Prop where
  | nil : RecoverableNativeWalk D Γ T [] T
  | cons : env.HasType univs Γ a A →
      (¬ IsProof Γ a → ScopedTypeRecovery (ErasedJointUnion D)
        (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ A)) →
      RecoverableNativeWalk D Γ (B.inst a) args result →
      RecoverableNativeWalk D Γ (.forallE A B) (a :: args) result

/-- Forgetting retained recoveries gives the ordinary typed native walk. -/
theorem RecoverableNativeWalk.typed (W : RecoverableNativeWalk D Γ T args result) :
    InstForallsC env univs Γ T args result := by
  induction W with
  | nil => exact .nil
  | cons ha _ _ ih => exact .cons ha ih

/-- All computed arguments still supply a computed native telescope in the
full union when the original walk retains its recoveries. The native residual
computes to the deterministic supplied result, with no confluence premise. -/
theorem proofErase_joint_union_computed_native_supply
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (HW : RecoverableNativeWalk D Γ T args residual)
    (RT : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ T) rawType)
    (HA : List.Forall₂ (ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) rawArgs) :
    ∃ out, ProofShape.supplyType rawArgs rawType = some out ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ residual) out := by
  induction HW generalizing u rawType rawArgs with
  | nil => cases HA; exact ⟨_, rfl, RT⟩
  | @cons a A args residual B ha HR HW ih =>
    cases HA with
    | cons RA HA =>
      obtain ⟨⟨v, hA⟩, w, hB⟩ := hT.forallE_inv henv
      have RT' := RT
      rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
        if_neg (not_isProof_of_sort hΓ hT)] at RT'
      obtain ⟨D', C, rfl, _⟩ := RT'.forallE_domain_inv erased_joint_union_head
      have RB := proofErase_joint_union_computed_pi_inst heq hs hΓ hA hB ha HR RT RA
      obtain ⟨out, HS, RO⟩ := ih (hB.instN henv Ctx.InstN.zero ha) RB HA
      exact ⟨out, HS, RO⟩

/-- Two recoverable native walks whose arguments compute to one shared list
have a native residual join in the full union. This constructs the join at
exact residuals, without requiring recovery of the shared argument list. -/
theorem proofErase_joint_union_native_residuals_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (HW : RecoverableNativeWalk D Γ T args residual)
    (HW' : RecoverableNativeWalk D Γ T args' residual')
    (HA : List.Forall₂ (ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) sharedArgs)
    (HA' : List.Forall₂ (ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ))
      (args'.map (proofErase Γ)) sharedArgs) :
    ∃ out, ProofShape.supplyType sharedArgs (proofErase Γ T) = some out ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ residual) out ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ residual') out := by
  obtain ⟨out, HS, R⟩ := proofErase_joint_union_computed_native_supply heq hs hΓ hT HW .refl HA
  obtain ⟨out', HS', R'⟩ := proofErase_joint_union_computed_native_supply heq hs hΓ hT HW' .refl HA'
  cases Option.some.inj (HS.symm.trans HS')
  exact ⟨out, HS, R, R'⟩

end Lean4Lean.VEnv.Strengthening
