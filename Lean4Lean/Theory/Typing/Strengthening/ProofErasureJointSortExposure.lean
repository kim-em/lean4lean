import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointResynthesis

/-! # Universe exposure forced by joint domain re-synthesis

The Pi output in re-synthesis does not restrict its recovery obligation to Pi
heads. A retained lambda with a Pi expression as its body tests sort recovery
of that Pi's domain. The auxiliary binder is retained explicitly throughout.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
open private erase_sort_inv ProofShape.liftN_sort_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison

namespace ProofShape
/-- Trailing conversion cannot hide recovery of a displayed lambda body. -/
theorem ScopedTypeRecovery.lam_body_inv
    (R : ScopedTypeRecovery Step Δ (.lam A b) T) :
    ∃ B, ScopedTypeRecovery Step (A :: Δ) b B := by
  generalize E : ProofShape.lam A b = e at R
  induction R with
  | lam R => cases E; exact ⟨_, R⟩
  | convert _ _ ih => exact ih E
  | bvar | sort | const | app | forallE | proj => cases E

/-- Recovering any type of a displayed Pi requires a sort for its domain. -/
theorem ScopedTypeRecovery.forallE_domain_inv
    (R : ScopedTypeRecovery Step Δ (.forallE A B) T) :
    ∃ u, ScopedTypeRecovery Step Δ A (.sort u) := by
  generalize E : ProofShape.forallE A B = e at R
  induction R with
  | forallE R _ => cases E; exact ⟨_, R⟩
  | convert _ _ ih => exact ih E
  | bvar | sort | const | lam | app | proj => cases E
end ProofShape

/-- Joint re-synthesis forces universe recovery of every type after one
inhabited dummy binder. The test function returns the Pi with that type as its
domain; its argument guard is reflexive. No recovery certificate for the type
is assumed, and no substitution closure of Recovery is used. -/
theorem JointCarrierDomainResynthesis.sort_recovery_above
    (H : JointCarrierDomainResynthesis Recovery Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e (.sort u)) :
    ∃ v, ProofShape.ScopedTypeRecovery Recovery
      (proofEraseCtx (.sort (.succ .zero) :: Γ))
      (proofErase (.sort (.succ .zero) :: Γ) e.lift) (.sort v) := by
  let S : VExpr := .sort (.succ .zero)
  have hS : env.HasType univs Γ S (.sort (.succ (.succ .zero))) := .sort (by trivial)
  have hΓS : OnCtx (S :: Γ) (env.IsType univs) := ⟨hΓ, _, hS⟩
  have hPi := HasType.forallE (he.weak henv (B := S))
    (HasType.sort (l := VLevel.zero) (Γ := e.lift :: S :: Γ) (by trivial))
  have hf := HasType.lam hS hPi
  have hn := not_isProof_function_to_sort hΓ hf
  obtain ⟨A, B, R⟩ := H.pi_of_inhabited hΓ hf (HasType.sort (l := VLevel.zero) (by trivial)) hn
  rw [show proofErase Γ (.lam S (.forallE e.lift (.sort .zero))) =
    .lam (proofErase Γ S) (proofErase (S :: Γ) (.forallE e.lift (.sort .zero))) from if_neg hn] at R
  obtain ⟨_, R⟩ := R.lam_body_inv
  rw [show proofErase (S :: Γ) (.forallE e.lift (.sort .zero)) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓS hPi)] at R
  exact R.forallE_domain_inv

/-- Re-synthesis requires universe exposure for every type convertible to a
sort, in the context extended by its fresh variable and the dummy binder.
This does not retract contextual computation using an untyped raw filler. -/
theorem JointCarrierDomainResynthesis.sort_exposure_above
    (H : JointCarrierDomainResynthesis Recovery Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort u))
    (HT : env.IsDefEqU univs Γ T (.sort v)) :
    ∃ w, ProofShape.ScopedCompute Recovery
      (proofEraseCtx (.sort (.succ .zero) :: T :: Γ))
      (((proofErase Γ T).liftN 1).liftN 1) (.sort w) := by
  have hΓT : OnCtx (T :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  have hx : env.HasType univs (T :: Γ) (.bvar 0) T.lift := .bvar .zero
  have hxv : env.HasType univs (T :: Γ) (.bvar 0) (.sort v) :=
    ((HT.of_l henv hΓ hT).weak henv).defeq hx
  have hΓS : OnCtx (.sort (.succ .zero) :: T :: Γ) (env.IsType univs) :=
    ⟨hΓT, _, HasType.sort (by trivial)⟩
  obtain ⟨w, R⟩ := H.sort_recovery_above hΓT hxv
  change ProofShape.ScopedTypeRecovery Recovery (proofEraseCtx (.sort (.succ .zero) :: T :: Γ))
    (proofErase (.sort (.succ .zero) :: T :: Γ) (.bvar 1)) (.sort w) at R
  rw [show proofErase (.sort (.succ .zero) :: T :: Γ) (.bvar 1) = .bvar 1 from
    if_neg (not_isProof_of_sort hΓS (hxv.weak henv))] at R
  exact ⟨w, R.bvar_compute⟩

/-- With primitive descent, joint re-synthesis already implies strengthening
of a literal-sort equation across a front block. The two test binders join that
same block, so descent removes all of them at once. This is only a necessary
fragment: no reduction of PropFront to literal-sort equations is asserted. -/
theorem JointCarrierDomainResynthesis.sort_front_descend
    (hstep : ErasedScopedPrimitiveDescent Recovery)
    (H : JointCarrierDomainResynthesis Recovery Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n 0 Γ Γ')
    (hT : env.HasType univs Γ T (.sort u))
    (HT : env.IsDefEqU univs Γ' (T.liftN n) (.sort v)) :
    env.IsDefEqU univs Γ T (.sort v) := by
  have hTw := hT.weakN henv W
  obtain ⟨w, R⟩ := H.sort_exposure_above hΓ' hTw HT
  rw [proofErase_liftN hΓ hΓ' W hT] at R
  simp only [ProofShape.liftN_add] at R
  have hΓT : OnCtx (T.liftN n :: Γ') (env.IsType univs) := ⟨hΓ', u, hTw⟩
  have hΓS : OnCtx (.sort (.succ .zero) :: T.liftN n :: Γ') (env.IsType univs) :=
    ⟨hΓT, _, HasType.sort (by trivial)⟩
  obtain ⟨out, HE, Eout⟩ := proofErase_scoped_compute_descend hstep hΓ hΓS
    W.cons0.cons0 hT rfl R
  obtain rfl := erase_sort_inv (ProofShape.liftN_sort_inv Eout)
  have HW : env.IsDefEqU univs Γ' (.sort w) (.sort v) :=
    (show env.IsDefEqU univs Γ' (.sort w) (T.liftN n) from
      ⟨_, (HE.weakN henv W).symm⟩).trans henv hΓ' HT
  have hw := HE.hasType.2.sort_inv henv
  have hv := (HT.of_l henv hΓ' hTw).hasType.2.sort_inv henv
  exact (show env.IsDefEqU univs Γ T (.sort w) from ⟨_, HE⟩).trans henv hΓ
    ⟨_, IsDefEq.sortDF hw hv (HW.sort_inv henv hΓ')⟩

end Lean4Lean.VEnv.Strengthening
