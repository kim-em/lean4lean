import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureRecord
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparedRecord

/-! # Full future record guards at compared carriers

An actual future comparison of the record type with a target type exposes
the registered family at every future target reduct. Stored future common
field comparisons survive changes to both majors. Typed replay transfers
universe-dependent proof-field metadata without general carrier conversion.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

private theorem compared_record_beta
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const family ls) args) out)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hU : env.HasType univs Γ U (.sort v))
    (ha : env.HasType univs Γ a A)
    (HC : BetaStableFamily (fun Δ => JointCompare Step Δ mode)
      (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ U))
    (EA : proofErase Γ A = ProofShape.mkApps (.const family ls) ps)
    (HF : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      BetaStableFamily (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ)
        (.proj family i (proofErase Γ a)) (.proj family i b))
    (RC : ProofShape.BetaRed (proofErase Γ U) C)
    (RA : ProofShape.BetaRed (proofErase Γ a) p) (RB : ProofShape.BetaRed b q) :
    JointCarrierGuard Step (proofEraseCtx Γ) C p q := by
  obtain ⟨U', PU, EU⟩ := proofErase_beta_replay hΓ hU RC
  obtain ⟨a', PA, Ea⟩ := proofErase_beta_replay hΓ ha RA
  have HT : JointCompare Step (proofEraseCtx Γ) mode (proofErase Γ A) (proofErase Γ U') := by
    rw [EU]
    exact HC.1 .refl RC
  have HG := proofErase_joint_compared_record_guard hstep hn hi hx hp hadm hΓ hA
    (beta_eq hΓ hU PU).hasType.2 (beta_eq hΓ ha PA).hasType.2 HT EA
    (b := q) (fun i hj hf => by
      rw [Ea]
      exact (HF i hj hf).1 (.proj RA) (.proj RB))
  simpa only [EU, Ea] using HG

/-- Future comparison with a displayed record transports all retained future
common field certificates to a full future guard at the target carrier. The
target may compute before exposing the family, with changed parameters and
levels. Only the left major needs an actual source typing; no computational
join of the carriers or majors is required. -/
theorem proofErase_future_compared_record_guard
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const family ls) args) out)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hU : env.HasType univs Γ U (.sort v))
    (ha : env.HasType univs Γ a A)
    (HC : BetaStableFamily (fun Δ => JointCompare Step Δ mode)
      (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ U))
    (EA : proofErase Γ A = ProofShape.mkApps (.const family ls) ps)
    (HF : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      BetaStableFamily (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ)
        (.proj family i (proofErase Γ a)) (.proj family i b)) :
    BetaStableCarrier Step (proofEraseCtx Γ) (proofErase Γ U) (proofErase Γ a) b := by
  refine ⟨fun RC RA RB => compared_record_beta hstep hn hi hx hp hadm hΓ hA hU ha HC EA HF RC RA RB, ?_⟩
  intro Δ' τ C p q W RC RA RB
  have HT := HC.subst W
  have HF' := fun i hj hn => (HF i hj hn).subst W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  have EA' : proofErase Γ₀ (A.subst σ) =
      ProofShape.mkApps (.const family ls) (ps.map (fun x => x.subst τ)) := by
    rw [proofErase_subst_with hΓ₀ WS hA ES, EA, ProofShape.subst_mkApps, ProofShape.subst]
  rw [← proofErase_subst_with hΓ₀ WS hA ES, ← proofErase_subst_with hΓ₀ WS hU ES, ← EΓ₀] at HT
  simp only [ProofShape.subst] at HF'
  rw [← proofErase_subst_with hΓ₀ WS ha ES, ← EΓ₀] at HF'
  rw [← proofErase_subst_with hΓ₀ WS hU ES] at RC
  rw [← proofErase_subst_with hΓ₀ WS ha ES] at RA
  rw [← EΓ₀]
  exact compared_record_beta hstep hn hi hx (by simpa only [List.length_map] using hp) hadm
    hΓ₀ (hA.subst henv WS) (hU.subst henv WS) (ha.subst henv WS) HT EA' HF' RC RA RB

/-- The concrete canonical-Eq joint union supports this future record
conversion without unresolved substitution or carrier-transport premises.
Only the particular registered family must be excluded from unfolding. -/
theorem proofErase_future_union_compared_record_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hU : env.HasType univs Γ U (.sort v))
    (ha : env.HasType univs Γ a A)
    (HC : BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ mode)
      (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ U))
    (EA : proofErase Γ A = ProofShape.mkApps (.const family ls) ps)
    (HF : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true) (proofEraseCtx Γ)
        (.proj family i (proofErase Γ a)) (.proj family i b)) :
    BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ U) (proofErase Γ a) b := by
  apply proofErase_future_compared_record_guard (erased_joint_union_descent heq hs)
    ?_ hi hx hp hadm hΓ hA hU ha HC EA HF
  intro Δ ls args out H
  exact erased_joint_union_no_rigid heq (henv.projectionRigid hi) hD H (constHead_mkApps _ _)

end Lean4Lean.VEnv.Strengthening
