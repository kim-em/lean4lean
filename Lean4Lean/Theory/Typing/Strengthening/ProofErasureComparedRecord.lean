import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDomainExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointSemanticConversion

/-! # Record guards transported through an actual carrier comparison

A displayed record carrier exposes the same family on the target side of a
typed comparison. Ordinary projection comparisons survive unchanged. Actual
source and target typings justify the universe-dependent proof-field metadata.
The source carrier need not be a subsingleton and may have dependent fields.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private infer_raw from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport
open private record_conversion_metadata
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointSemanticConversion
variable [Params]

/-- A supplied type comparison transports a record guard whose retained fields
use ordinary common comparison. The target may first compute to the record
family, with changed levels and parameters. Only the left endpoint needs a
source typing to transfer proof-field metadata; right-endpoint soundness is
checked when the resulting guard is consumed. No semantic head law is assumed. -/
theorem proofErase_joint_compared_record_guard
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const family ls) args) out)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hU : env.HasType univs Γ U (.sort v))
    (ha : env.HasType univs Γ a A)
    (HC : JointCompare Step (proofEraseCtx Γ) mode (proofErase Γ A) (proofErase Γ U))
    (EA : proofErase Γ A = ProofShape.mkApps (.const family ls) ps)
    (HF : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      JointCompare Step (proofEraseCtx Γ) true
        (.proj family i (proofErase Γ a)) (.proj family i b)) :
    JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ U) (proofErase Γ a) b := by
  have HC := proofErase_joint_types_inferred hstep hΓ hA hU HC
  have HE := infer_raw hstep HC hΓ hA hU rfl rfl rfl
    (not_isProof_of_sort hΓ hA) (not_isProof_of_sort hΓ hU)
  have HC' := HC
  rw [EA] at HC'
  obtain ⟨ls', ps', R, hlen⟩ := HC'.const_spine_exposure hn
  obtain ⟨F, HU, EF⟩ := proofErase_scoped_compute_realize hstep hΓ hU rfl rfl R
  obtain ⟨args', rfl, Eargs'⟩ := proofErase_const_spine_inv EF
  obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv EA
  have hp₀ : args.length = info.nparams := by
    have H := congrArg List.length Eargs
    simp only [List.length_map] at H
    omega
  have hp₁ : args'.length = info.nparams := by
    have H := congrArg List.length Eargs'
    simp only [List.length_map] at H
    omega
  have haF := ha.defeqU_r henv hΓ ((show env.IsDefEqU univs Γ _ _ from ⟨_, HE⟩).trans
    henv hΓ ⟨_, HU⟩)
  obtain ⟨hadm', hflags⟩ := record_conversion_metadata hΓ hi hp₀ hp₁ hx ha haF hadm
  apply JointCheck.carrierCompute R
  apply JointCheck.carrierIntro hi hx (hlen.trans hp) hadm'
  intro i hj hnt
  exact HF i hj (fun H => hnt (hflags i hj H))

/-- Recovery plus an actual comparison with the assigned function type selects
a Pi whose domain accepts the given record field comparisons. No exact-domain
recovery, parameter join, or global carrier conversion theorem is needed. -/
theorem proofErase_joint_compared_recovery_record_guard
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const family ls) args) out)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (ha : env.HasType univs Γ a A)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (HC : JointCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = ProofShape.mkApps (.const family ls) ps)
    (HF : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      JointCompare Step (proofEraseCtx Γ) true
        (.proj family i (proofErase Γ a)) (.proj family i b)) :
    ∃ D C, ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) (.forallE D C) ∧
      JointCarrierGuard Step (proofEraseCtx Γ) D (proofErase Γ a) b := by
  obtain ⟨D, C, hfDC, RD, HD⟩ := proofErase_joint_recovered_pi_domain hstep hhead hΓ hf R HC
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
  obtain ⟨_, hDC⟩ := hfDC.isType henv hΓ
  obtain ⟨⟨_, hD⟩, _, _⟩ := hDC.forallE_inv henv
  exact ⟨_, _, RD, proofErase_joint_compared_record_guard hstep hn hi hx hp hadm
    hΓ hA hD ha HD EA HF⟩

/-- The record argument case constructs the actual application comparison.
The input certificates are a function comparison, one recovery, its comparison
with the assigned Pi, and the ordinary comparisons of retained record fields. -/
theorem proofErase_joint_application_of_compared_recovery_record
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const family ls) args) out)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (ha : env.HasType univs Γ a A)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (HC : JointCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = ProofShape.mkApps (.const family ls) ps)
    (HF : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      JointCompare Step (proofEraseCtx Γ) true
        (.proj family i (proofErase Γ a)) (.proj family i b))
    (Hfg : JointCompare Step (proofEraseCtx Γ) false (proofErase Γ f) g) :
    JointCompare Step (proofEraseCtx Γ) resultMode
      (.app (proofErase Γ f) (proofErase Γ a)) (.app g b) := by
  obtain ⟨D, C, RD, HG⟩ := proofErase_joint_compared_recovery_record_guard
    hstep hhead hn hi hx hp hadm hΓ hf ha R HC EA HF
  exact .appCarrier RD Hfg HG

/-- At every finite joint stage, an actual type comparison transports exposed
record field checks at that same stage. No lower-stage beta-stability premise
is required; only the particular family must be excluded from unfolding. -/
theorem proofErase_joint_stage_compared_record_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hU : env.HasType univs Γ U (.sort v))
    (ha : env.HasType univs Γ a A)
    (HC : JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ) mode
      (proofErase Γ A) (proofErase Γ U))
    (EA : proofErase Γ A = ProofShape.mkApps (.const family ls) ps)
    (HF : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ) true
        (.proj family i (proofErase Γ a)) (.proj family i b)) :
    JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ U) (proofErase Γ a) b := by
  apply proofErase_joint_compared_record_guard (erased_joint_stage_descent heq hs stage)
    ?_ hi hx hp hadm hΓ hA hU ha HC EA HF
  intro Δ ls args out H
  exact erased_joint_stage_no_rigid heq (henv.projectionRigid hi) hD stage H (constHead_mkApps _ _)

/-- The same record conversion holds in the full joint union, using its actual
input comparison. Primitive substitution and proposition beta stability are
not premises, even though those global union laws remain open. -/
theorem proofErase_joint_union_compared_record_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hU : env.HasType univs Γ U (.sort v))
    (ha : env.HasType univs Γ a A)
    (HC : JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) mode
      (proofErase Γ A) (proofErase Γ U))
    (EA : proofErase Γ A = ProofShape.mkApps (.const family ls) ps)
    (HF : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
      JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
        (.proj family i (proofErase Γ a)) (.proj family i b)) :
    JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ U) (proofErase Γ a) b := by
  apply proofErase_joint_compared_record_guard (erased_joint_union_descent heq hs)
    ?_ hi hx hp hadm hΓ hA hU ha HC EA HF
  intro Δ ls args out H
  exact erased_joint_union_no_rigid heq (henv.projectionRigid hi) hD H (constHead_mkApps _ _)

end Lean4Lean.VEnv.Strengthening
