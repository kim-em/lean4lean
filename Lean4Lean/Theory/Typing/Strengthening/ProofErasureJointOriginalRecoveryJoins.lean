import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnionHeadBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointInstSquareBoundary

/-! # Paired computational joins retaining only original argument recovery

A comparison at a computed image would require recovery there. A computational
join of the bodies instead lets each arm instantiate at its own original
recoverable argument and then compute the argument copies. The shared image
need not recover any type, and the original domains may differ.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private lam_inv_aux from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBinderComputation
variable [Params]

/-- Paired body instantiation preserves an existing computational join when
the original arguments recover their respective domains and compute to one
raw image. There is no recovery requirement at the image, no equality premise
on the domains, and no confluence or comparison-composition assumption. -/
theorem proofErase_joint_union_paired_inst_compute_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hΓE : OnCtx (E :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hc : env.HasType univs (E :: Γ) c C)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y E)
    (HRx : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (HRy : ¬ IsProof Γ y → ScopedTypeRecovery (ErasedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ y) (proofErase Γ E))
    (RB : ScopedCompute (ErasedJointUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) body)
    (RC : ScopedCompute (ErasedJointUnion D) (proofEraseCtx (E :: Γ))
      (proofErase (E :: Γ) c) body)
    (RX : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ x) image)
    (RY : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ y) image) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (body.inst image) ∧
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (c.inst y)) (body.inst image) ∧
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) mode
      (proofErase Γ (b.inst x)) (proofErase Γ (c.inst y)) := by
  have RL := proofErase_joint_union_compute_inst_square heq hs hΓA hb hx HRx RB RX
  have RR := proofErase_joint_union_compute_inst_square heq hs hΓE hc hy HRy RC RY
  exact ⟨RL, RR, .compute RL RR (.leaf .refl)⟩

/-- Two typed lambdas that compute to one raw function close paired head beta
at independently recoverable original arguments computing to one raw value.
The value can lose exact recovery during computation. Each original argument
only recovers its own displayed domain; cross-domain recovery is unnecessary.
The function-join premise is stronger than an inferred comparison. -/
theorem proofErase_joint_union_paired_head_beta_compute_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hE : env.HasType univs Γ E (.sort v))
    (hb : env.HasType univs (A :: Γ) b B) (hc : env.HasType univs (E :: Γ) c C)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y E)
    (hnf : ¬ IsProof Γ (.lam A b)) (hng : ¬ IsProof Γ (.lam E c))
    (HRx : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (HRy : ¬ IsProof Γ y → ScopedTypeRecovery (ErasedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ y) (proofErase Γ E))
    (RF : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) fn)
    (RG : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam E c)) fn)
    (RX : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ x) image)
    (RY : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ y) image) :
    ∃ rawA body, fn = .lam rawA body ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) (body.inst image) ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
        (proofErase Γ (c.inst y)) (body.inst image) ∧
      JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) mode
        (proofErase Γ (b.inst x)) (proofErase Γ (c.inst y)) := by
  obtain ⟨A', b', EF, _, RB⟩ := lam_inv_aux heq hs RF hΓ hA hb hnf rfl
    (show .lam (proofErase Γ A) (proofErase (A :: Γ) b) = proofErase Γ (.lam A b) from
      (if_neg hnf).symm)
  obtain ⟨E', c', EG, _, RC⟩ := lam_inv_aux heq hs RG hΓ hE hc hng rfl
    (show .lam (proofErase Γ E) (proofErase (E :: Γ) c) = proofErase Γ (.lam E c) from
      (if_neg hng).symm)
  obtain ⟨rfl, rfl⟩ := ProofShape.lam.inj (EF.symm.trans EG)
  exact ⟨_, _, EG, proofErase_joint_union_paired_inst_compute_join heq hs
    ⟨hΓ, u, hA⟩ ⟨hΓ, v, hE⟩ hb hc hx hy HRx HRy RB RC RX RY⟩

/-- The paired computational result applies even when the common value has no
assigned-type recovery anywhere in the union. In this checked example an eta-
converted neutral variable is the shared image of its identity cover. Every
pair of typed body computations with a shared raw output gives the stated
instantiated join; no image-recovery preservation is hidden in the theorem. -/
theorem proofErase_joint_paired_join_without_image_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' A x y, OnCtx Γ' (env.IsType univs) ∧
      env.HasType univs Γ' x A ∧ env.HasType univs Γ' y A ∧
      ¬ IsProof Γ' x ∧ ProofShape.BetaRed (proofErase Γ' y) (proofErase Γ' x) ∧
      ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' y) (proofErase Γ' A) ∧
      (¬ ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' x) (proofErase Γ' A)) ∧
      ∀ {b c B C out}, env.HasType univs (A :: Γ') b B → env.HasType univs (A :: Γ') c C →
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx (A :: Γ')) (proofErase (A :: Γ') b) out →
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx (A :: Γ')) (proofErase (A :: Γ') c) out →
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ')
          (proofErase Γ' (b.inst y)) (out.inst (proofErase Γ' x)) ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ')
          (proofErase Γ' (c.inst y)) (out.inst (proofErase Γ' x)) ∧
        JointCompare (ErasedJointUnion D) (proofEraseCtx Γ') true
          (proofErase Γ' (b.inst y)) (proofErase Γ' (c.inst y)) := by
  obtain ⟨Γ', x, A, y, hΓ', hx, hy, hn, RY, HR, Hno, _⟩ :=
    proofErase_joint_inst_square_without_image_recovery heq hs hΓ
  refine ⟨Γ', A, x, y, hΓ', hx, hy, hn, RY, HR, Hno, ?_⟩
  intro b c B C out hb hc RB RC
  obtain ⟨u, hA⟩ := hx.isType henv hΓ'
  exact proofErase_joint_union_paired_inst_compute_join heq hs
    ⟨hΓ', u, hA⟩ ⟨hΓ', u, hA⟩ hb hc hy hy (fun _ => HR) (fun _ => HR)
    RB RC (.beta RY) (.beta RY)

end Lean4Lean.VEnv.Strengthening
