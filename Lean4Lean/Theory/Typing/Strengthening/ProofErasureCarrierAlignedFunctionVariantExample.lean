import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedCoreJoint

/-! # Function-to-record guards across changed binder domains

A finite field comparison under the source binder suffices. The target guard
is reconstructed under the new binder, including native application checks in
those field certificates. No substitution-future certificate is supplied.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Ordinary field checks under a function's source domain produce a full
function-to-record guard at a structurally varied domain. Retained fields can
use the entire core checking language, recursively including native applications,
function guards, record guards and finite core computation. -/
theorem carrier_aligned_core_function_record_variant
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hi : env.projections family info) (hp : info.nparams = 0) (hx : info.nindices = 0)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort u))
    (hF : env.HasType univs Γ (.const family ls) (.sort v))
    (hf : env.HasType univs Γ f (.forallE A (.const family ls)))
    (hg : env.HasType univs Γ g (.forallE A (.const family ls)))
    (V : StructuralVariant (proofErase Γ A) (proofErase Γ B))
    (Hfields : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      ComputedJointCompare (fun _ => ErasedIotaPrimitive D) (proofEraseCtx (A :: Γ)) true
        (.proj family i (.app ((proofErase Γ f).liftN 1) (etaArgument u)))
        (.proj family i (.app ((proofErase Γ g).liftN 1) (etaArgument u)))) :
    ComputedJointCarrierGuard (fun _ => ErasedIotaPrimitive D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE B (.const family ls))) (proofErase Γ f) (proofErase Γ g) := by
  have hFA : env.HasType univs (A :: Γ) (.const family ls) (.sort v) := by
    simpa only [VExpr.lift, VExpr.liftN] using (hF.weak henv (B := A)).hasType.1
  have hFB : env.HasType univs (B :: Γ) (.const family ls) (.sort v) := by
    simpa only [VExpr.lift, VExpr.liftN] using (hF.weak henv (B := B)).hasType.1
  have hPiA := HasType.forallE hA hFA
  have hPiB := HasType.forallE hB hFB
  have EFA : proofErase (A :: Γ) (.const family ls) = .const family ls :=
    if_neg (not_isProof_of_sort (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hFA)
  have EFB : proofErase (B :: Γ) (.const family ls) = .const family ls :=
    if_neg (not_isProof_of_sort (Γ := B :: Γ) ⟨hΓ, u, hB⟩ hFB)
  have EPA : proofErase Γ (.forallE A (.const family ls)) = .forallE (proofErase Γ A) (.const family ls) := by
    simp only [proofErase, if_neg (not_isProof_of_sort hΓ hPiA)]
    exact congrArg (ProofShape.forallE (proofErase Γ A)) EFA
  have EPB : proofErase Γ (.forallE B (.const family ls)) = .forallE (proofErase Γ B) (.const family ls) := by
    simp only [proofErase, if_neg (not_isProof_of_sort hΓ hPiB)]
    exact congrArg (ProofShape.forallE (proofErase Γ B)) EFB
  have HG : ComputedJointCarrierGuard (fun _ => ErasedIotaPrimitive D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A (.const family ls))) (proofErase Γ f) (proofErase Γ g) := by
    rw [EPA]
    apply ComputedJointCheck.carrierFunction (.of_typed hΓ hA)
    exact .carrierIntro hi hx (ps := []) (by simp [hp]) hadm Hfields
  apply proofErase_carrier_aligned_core_joint_carrier hs hlevels hcon hΓ hf hg hPiB _ HG
  rw [EPA, EPB]
  exact .forallE V .refl

end Lean4Lean.VEnv.Strengthening
