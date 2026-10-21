import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointNativeTelescope
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIdentityRecoveryCover

/-! # Native Eq recovery without an anchor recovery premise

An identity expansion of the anchor recovers its assigned carrier. The union
instantiation square contracts that expansion after transporting the body.
Eq's final Pi is independent of the anchor, so the expansion disappears from
the native source type. No inverse computation or union substitution law is
needed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private eq_carrier_recovery
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqNativeCarrierRecovery
variable [Params]

/-- Computed nondependent function types instantiate at arbitrary typed
arguments, even when those arguments cannot recover their assigned domains.
An identity cover supplies recovery before the argument computes; the native
result type contains no argument occurrence, so it remains unchanged. -/
theorem proofErase_joint_union_computed_arrow_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs Γ B (.sort v)) (hx : env.HasType univs Γ x A)
    (RT : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B.lift)) (.forallE rawA rawB))
    (RX : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ x) image) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ B) (rawB.inst image) := by
  obtain ⟨hy, _, RY, HR⟩ := proofErase_identity_recovery_cover
    (Step := ErasedJointUnion D) hΓ hx
  have H := proofErase_joint_union_computed_pi_inst heq hs hΓ hA (hB.weak henv)
    hy HR RT ((ScopedCompute.beta RY).trans RX)
  simpa only [VExpr.inst_lift] using H

/-- Any selected recovery of a typed Eq prefix computes from its native final
Pi in the full union. A temporary recoverable anchor expansion is eliminated
by the directed instantiation square; no recovery of the actual anchor is
assumed. The final native type is independent of that anchor. -/
theorem proofErase_joint_union_eq_native_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α)
    (R : ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ)
      (.app (.app (.const ``Eq [u]) (proofErase Γ α)) (proofErase Γ z)) T) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (.forallE (proofErase Γ α) (.sort .zero)) T := by
  classical
  generalize EΔ : proofEraseCtx Γ = Δ at R
  generalize E : ProofShape.app (.app (.const ``Eq [u]) (proofErase Γ α)) (proofErase Γ z) = e at R
  induction R with
  | app RF =>
    cases E
    have RC := eq_carrier_recovery heq erased_joint_union_head RF
    have hS := HasType.sort (env := env) (U := univs) (Γ := α :: Γ)
      (l := .zero) (by trivial)
    have hB := HasType.forallE hα hS
    have hΓα : OnCtx (α :: Γ) (env.IsType univs) := ⟨hΓ, u, hα⟩
    have EB : proofErase Γ (.forallE α (.sort .zero)) =
        .forallE (proofErase Γ α) (.sort .zero) := by
      change (if IsProof Γ (.forallE α (.sort .zero)) then _ else _) = _
      rw [if_neg (not_isProof_of_sort hΓ hB)]
      rw [show proofErase (α :: Γ) (.sort .zero) = .sort .zero from
        if_neg (not_isProof_of_sort hΓα hS)]
    have EP : proofErase Γ (.forallE α (VExpr.forallE α (.sort .zero)).lift) =
        .forallE (proofErase Γ α) (.forallE ((proofErase Γ α).liftN 1) (.sort .zero)) := by
      rw [show proofErase Γ (.forallE α (VExpr.forallE α (.sort .zero)).lift) = .forallE _ _ from
        if_neg (not_isProof_of_sort hΓ (HasType.forallE hα (hB.weak henv)))]
      rw [show proofErase (α :: Γ) (VExpr.forallE α (.sort .zero)).lift =
        (proofErase Γ (.forallE α (.sort .zero))).liftN 1 from
          proofErase_liftN hΓ hΓα Ctx.LiftN.one hB, EB]
      rfl
    rw [← EΔ, ← EP] at RC
    have HI := proofErase_joint_union_computed_arrow_inst heq hs hΓ hα hB hz RC .refl
    simpa only [EB, EΔ] using HI
  | convert _ H ih => exact (ih EΔ E).trans H
  | bvar | sort | const | lam | forallE | proj => cases E

/-- The selected last-argument domain of a typed Eq prefix is reachable from
its supplied carrier in the union, without any exact anchor recovery premise. -/
theorem proofErase_joint_union_eq_domain_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α)
    (R : ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ)
      (.app (.app (.const ``Eq [u]) (proofErase Γ α)) (proofErase Γ z)) (.forallE A B)) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ α) A := by
  obtain ⟨A', B', HE, RA⟩ := (proofErase_joint_union_eq_native_compute
    heq hs hΓ hα hz R).forallE_domain_inv erased_joint_union_head
  cases HE
  exact RA

end Lean4Lean.VEnv.Strengthening
