import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeFreshTypeBoundary

/-! # Computation cannot repair native dependence on an inserted binder

Descent holds through an arbitrary source computation followed by native
recovery. The two relations may differ, provided both descend.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params]

/-- No future computed image of a term typed below insertion can natively
recover a retained application argument naming the inserted binder. Thus
waiting for an exactly recoverable pivot cannot repair this assignment. -/
theorem computed_native_recovery_no_inserted_argument
    (hsource : ErasedScopedPrimitiveDescent Source)
    (htarget : ErasedScopedPrimitiveDescent Target)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T)
    (hj : k ≤ j) (hj' : j < k+n)
    (RC : ScopedCompute Source (proofEraseCtx Γ') (proofErase Γ' (e.liftN n k)) image) :
    ¬ ScopedTypeRecovery Target (proofEraseCtx Γ') image (.app f (.bvar j)) := by
  rw [proofErase_liftN hΓ hΓ' W ht] at RC
  obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_descend hsource hΓ hΓ' W ht rfl RC
  have EE' : proofErase Γ' (e'.liftN n k) = image :=
    (proofErase_liftN hΓ hΓ' W HE.hasType.2).trans EE
  rw [← EE']
  exact native_recovery_no_inserted_argument htarget hΓ hΓ' W HE.hasType.2 hj hj'

end Lean4Lean.VEnv.Strengthening
