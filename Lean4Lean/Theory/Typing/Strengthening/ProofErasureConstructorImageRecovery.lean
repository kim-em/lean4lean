import Lean4Lean.Theory.Typing.Strengthening.ProofErasureMaskedConstructorRecovery

/-! # Native family recovery at a constructor reached by whole computation

The path to the literal constructor may be arbitrary. Typed realization at
its endpoint supplies the native family without individual field histories.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params]

/-- Any complete descending computation reaching a saturated unindexed
constructor supplies native recovery of its literal family parameters. The
original source can have any assigned type; neither the source nor the fields
need native certificates. The target recovery language is arbitrary. -/
theorem computed_constructor_image_native
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hx : info.nindices = 0) (hlen : images.length = info.nparams + info.numFields)
    (ht : env.HasType univs Γ e T)
    (R : ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ e)
      (ProofShape.mkApps (.const info.ctorName ls) images)) :
    ScopedTypeRecovery Target (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName ls) images)
      (ProofShape.mkApps (.const s ls) (images.take info.nparams)) := by
  obtain ⟨e', HE, Ee⟩ := proofErase_scoped_compute_realize hstep hΓ ht rfl rfl R
  obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv Ee
  have hn : ¬ IsProof Γ (VExpr.mkApps (.const info.ctorName ls) args) := by
    intro H
    have E := congrArg ProofShape.constHead ((proofErase_eq_proof.2 H).symm.trans Ee)
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at E
    cases E
  have hlen' : args.length = info.nparams + info.numFields := by
    rw [Eargs, List.length_map] at hlen
    exact hlen
  have RN := proofErase_structure_constructor_native (Step := Target) hΓ hi hx hlen' HE.hasType.2 hn
  rw [Ee] at RN
  simpa only [Eargs, ← List.map_take] using RN

/-- Computing the exposed parameter vector converts the recovered family.
Only the parameters need a path; every dependent field stays arbitrary. -/
theorem computed_constructor_image_native_parameters
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hx : info.nindices = 0) (hlen : images.length = info.nparams + info.numFields)
    (ht : env.HasType univs Γ e T)
    (R : ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ e)
      (ProofShape.mkApps (.const info.ctorName ls) images))
    (RP : List.Forall₂ (ScopedCompute Target (proofEraseCtx Γ)) (images.take info.nparams) params) :
    ScopedTypeRecovery Target (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName ls) images) (ProofShape.mkApps (.const s ls) params) :=
  (computed_constructor_image_native hstep hΓ hi hx hlen ht R).convert (.mkApps .refl RP)

end Lean4Lean.VEnv.Strengthening
