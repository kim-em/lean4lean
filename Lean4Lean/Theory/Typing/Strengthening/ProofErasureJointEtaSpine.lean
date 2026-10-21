import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineFirstBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEtaSortExposure

/-! # Removing function eta with arbitrary pending arguments

Exact first-head-beta decomposition lets the short application reproduce the
contractum while the pending arguments follow their original computation paths.
The exact final universe is retained. Only the argument consumed by the selected
eta redex needs recovery; the pending arguments need no recovery or typing premise.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private short_to_contractum from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEtaSortExposure
variable [Params]

omit [Params] in
private theorem compute_spine
    (RF : ScopedCompute Step Δ f g) (RX : List.Forall₂ (ScopedCompute Step Δ) xs ys) :
    ScopedCompute Step Δ (mkApps f xs) (mkApps g ys) := by
  induction RX generalizing f g with
  | nil => exact RF
  | cons RX _ ih => exact ih (.app RF RX)

/-- A selected function eta can be removed from a nonempty application spine
without changing any literal universe it computes to. All later arguments and
the post-beta tail may compute arbitrarily. Recovery is required only for the
original first argument at the original eta domain. -/
theorem proofErase_joint_eta_spine_sort_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (hp : env.HasType univs Γ p A)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ A)) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (mkApps (.lam (proofErase Γ A) (.app ((proofErase Γ f).liftN 1) (etaArgument u)))
        (proofErase Γ p :: xs)) (.sort v) ↔
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (mkApps (proofErase Γ (.app f p)) xs) (.sort v) := by
  constructor
  · intro R
    obtain ⟨A', body, x', xs', RF, RX, RT⟩ := R.lambda_spine_sort erased_joint_union_head
    cases RX with | cons RX RXS =>
      exact (compute_spine (short_to_contractum heq hs hΓ hA hf hn hp HR RX RF) RXS).trans RT
  · intro R
    have hb : env.HasType univs (A :: Γ) (.app f.lift (.bvar 0)) B := by
      simpa only [lift, VExpr.liftN, inst_liftN_bvar] using
        HasType.app (hf.weak henv) (HasType.bvar .zero)
    have E : (ProofShape.app ((proofErase Γ f).liftN 1) (etaArgument u)).inst (proofErase Γ p) =
        proofErase Γ (.app f p) := by
      rw [← proofErase_eta_body hΓ hA hf hn,
        ← proofErase_instN (show OnCtx (A :: Γ) (env.IsType univs) from ⟨hΓ, u, hA⟩)
          hp Ctx.InstN.zero hb]
      simp only [VExpr.inst, VExpr.inst_lift, instVar_zero]
    exact (compute_spine (xs := xs) (show ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) _
      (proofErase Γ (.app f p)) from E ▸ ScopedCompute.beta .beta)
      (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl))).trans R

/-- A literal universe argument has its exact recovery certificate directly.
Eta at such an earlier prefix can therefore be removed with every pending
argument retained, without any semantic head-exposure or recovery premise. -/
theorem proofErase_joint_eta_sort_argument_spine_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hw : w.WF univs)
    (hf : env.HasType univs Γ f (.forallE (.sort (.succ w)) B)) (hn : ¬ IsProof Γ f) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (mkApps (.lam (.sort (.succ w)) (.app ((proofErase Γ f).liftN 1) (.bvar 0)))
        (.sort w :: xs)) (.sort v) ↔
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (mkApps (proofErase Γ (.app f (.sort w))) xs) (.sort v) := by
  have hp : env.HasType univs Γ (.sort w) (.sort (.succ w)) := .sort hw
  have hA : env.HasType univs Γ (.sort (.succ w)) (.sort (.succ (.succ w))) := .sort hw
  have EP : proofErase Γ (.sort w) = .sort w := if_neg (not_isProof_of_sort hΓ hp)
  have EA : proofErase Γ (.sort (.succ w)) = .sort (.succ w) := if_neg (not_isProof_of_sort hΓ hA)
  have HR : ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.sort w)) (proofErase Γ (.sort (.succ w))) := by
    rw [EP, EA]
    exact .sort hw
  have Earg : etaArgument (.succ (.succ w)) = .bvar 0 := by
    unfold etaArgument
    split
    · rename_i H
      have := VLevel.equiv_def.1 H []
      simp [VLevel.eval] at this
    · rfl
  simpa only [EP, EA, Earg] using
    proofErase_joint_eta_spine_sort_iff heq hs hΓ hA hf hn hp (fun _ => HR) (xs := xs) (v := v)

end Lean4Lean.VEnv.Strengthening
