import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaNativeInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeRetainedInstantiation

/-! # Eta-stage instantiation with retained native images

Proof arguments discharge the fresh image condition automatically. All other
arguments still require their exact native type; no coverage is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening.EtaNativeSubstitution
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions} {n k : Nat}

/-- Computation instantiates with exact recovery only for non-proof arguments. -/
theorem compute_inst_retained (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p A)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedEtaExpansionStage D k)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ A))
    (ht : env.HasType univs (A :: Γ) e T)
    (R : ScopedCompute (ErasedEtaExpansionStage D n) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out) :
    ScopedCompute (ErasedEtaExpansionStage D (n + k)) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) := by
  obtain ⟨u, hA⟩ := hp.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := A)).substEq hΓA hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst,
    ProofShape.Subst.liftN] using compute_subst heq hs hΓ W (erasedSubstAgreement_one hΓA hp)
      (NativeImageTransport.Images.inst_retained hΓ hp HR) ht R

/-- Native recovery also substitutes proof arguments without recovering the
proof marker, while retaining the exact selected result type. -/
theorem recovery_inst_retained (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p A)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedEtaExpansionStage D k)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ A))
    (ht : env.HasType univs (A :: Γ) e T)
    (R : ScopedTypeRecovery (ErasedEtaExpansionStage D n) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out) :
    ScopedTypeRecovery (ErasedEtaExpansionStage D (n + k)) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) := by
  obtain ⟨u, hA⟩ := hp.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := A)).substEq hΓA hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst,
    ProofShape.Subst.liftN] using recovery_subst heq hs hΓ W (erasedSubstAgreement_one hΓA hp)
      (NativeImageTransport.Images.inst_retained hΓ hp HR) ht R

/-- Full aligned comparison admits the same retained-only image condition,
including its common native carrier and dependent guard. -/
theorem aligned_inst_retained (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p A)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedEtaExpansionStage D k)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ A))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : CarrierAlignedCompare (ErasedEtaExpansionStage D n) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    CarrierAlignedCompare (ErasedEtaExpansionStage D (n + k)) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  obtain ⟨u, hA⟩ := hp.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := A)).substEq hΓA hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using
    aligned_subst heq hs hΓ W (erasedSubstAgreement_one hΓA hp)
      (NativeImageTransport.Images.inst_retained hΓ hp HR) ha hb H

/-- A proof argument incurs no additional guard stage for full comparison. -/
theorem aligned_inst_proof (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p A)
    (hproof : IsProof Γ p)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : CarrierAlignedCompare (ErasedEtaExpansionStage D n) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    CarrierAlignedCompare (ErasedEtaExpansionStage D n) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) :=
  aligned_inst_retained (k := 0) heq hs hΓ hp (fun hn => (hn hproof).elim) ha hb H

/-- Independently chosen proofs of the same domain instantiate the two sides
of full aligned comparison at the original stage. Their equality needs no
separate comparison certificate because both images erase to the proof marker. -/
theorem aligned_inst_proofs (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p A) (hq : env.HasType univs Γ q A)
    (hproof : IsProof Γ p)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : CarrierAlignedCompare (ErasedEtaExpansionStage D n) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    CarrierAlignedCompare (ErasedEtaExpansionStage D n) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst q)) := by
  obtain ⟨u, hA⟩ := hp.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have H' := aligned_inst_proof heq hs hΓ hp hproof ha hb H
  have hproofq := isProof_of_common_type hΓ hp hq hproof
  rw [proofErase_instN hΓA hp Ctx.InstN.zero hb, proofErase_eq_proof.2 hproof] at H'
  rw [proofErase_instN hΓA hq Ctx.InstN.zero hb, proofErase_eq_proof.2 hproofq]
  exact H'

end Lean4Lean.VEnv.Strengthening.EtaNativeSubstitution
