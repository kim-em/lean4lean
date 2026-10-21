import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEqGeneral
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointPropSingleton
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBetaExchange

/-! # Full joint computational substitution from proposition beta stability

Specialized Eq primitives are general singleton primitives at typed sources.
Together with proposition-guard substitution this covers every primitive of
the existing union. Compatible paths then substitute exactly, and the head-beta
overlap no longer needs recovery of the original or computed argument. The
proposition beta-stability premise itself remains unproved.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Proposition beta stability suffices for typed substitution of every joint
primitive. Eq carrier guards are first encoded as actual general family guards;
no target carrier decoder or domain re-synthesis premise is required. -/
theorem erased_joint_union_subst_of_prop_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D)) :
    ErasedPrimitiveSubstitutionTo (ErasedJointUnion D) (ErasedJointUnion D) := by
  intro Γ Γ₀ σ τ e T out hΓ₀ W E ht H
  rw [proofErase_subst_with hΓ₀ W ht E]
  rcases erased_joint_union_iff.1 H with H | H | H
  · exact .base (erased_joint_union_iff.2 (.inl (erased_iota_primitive_subst H)))
  · exact .base (proofErase_joint_general_substitution_of_prop_beta heq hs Hbeta H
      (ContextSubstitution.of_typed hΓ₀ W E))
  · exact .base (proofErase_joint_general_substitution_of_prop_beta heq hs Hbeta
      (proofErase_joint_prefix_as_general heq hs hregistry W.wf ht H)
      (ContextSubstitution.of_typed hΓ₀ W E))

/-- Under proposition beta stability, arbitrary typed simultaneous substitution
preserves the full joint computation with its exact substituted output. This
is directed transport, not merely an operational join or declarative equality. -/
theorem proofErase_joint_compute_subst_of_prop_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (e.subst σ)) (out.subst τ) :=
  proofErase_scoped_compute_subst_typed (erased_joint_union_descent heq hs)
    (erased_joint_union_subst_of_prop_beta heq hs hregistry Hbeta) hΓ₀ W E ht R

/-- The full head-beta overlap closes under proposition beta stability, even
when neither the original nor computed argument recovers its assigned type.
Lambda annotations and the argument may both change through joint computation.
No raw-confluence or arbitrary recovery-preservation hypothesis is used. -/
theorem proofErase_joint_beta_exchange_of_prop_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.lam A b))
    (RF : ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) functionOut)
    (RX : ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ x) argumentOut) :
    ∃ later A' bodyOut, stage ≤ later ∧ functionOut = .lam A' bodyOut ∧
      ScopedCompute (ErasedJointStage D later) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) (bodyOut.inst argumentOut) ∧
      ProofShape.BetaRed (.app functionOut argumentOut) (bodyOut.inst argumentOut) := by
  obtain ⟨bodyStage, A', bodyOut, _, rfl, _, RB⟩ :=
    proofErase_joint_lam_inv_later heq hs hΓ hA hb hn RF
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have RI := proofErase_joint_compute_subst_of_prop_beta heq hs hregistry Hbeta
    hΓ W (erasedSubstAgreement_one hΓA hx) hb (RB.mono (fun H => ⟨bodyStage, H⟩))
  have RI : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (bodyOut.inst (proofErase Γ x)) := by
    simpa only [VExpr.Subst.liftN, ProofShape.Subst.liftN, VExpr.inst_eq,
      ProofShape.inst_eq_subst] using RI
  obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize
    (erased_joint_stage_descent heq hs bodyStage) hΓA hb rfl rfl RB
  have RX' := proofErase_joint_compute_inst_argument heq hs hΓA HB.hasType.2 hx RX
  rw [proofErase_instN hΓA hx Ctx.InstN.zero HB.hasType.2, EB] at RX'
  have R := RI.trans (RX'.mono (fun H => ⟨stage, H⟩))
  obtain ⟨later, R⟩ := R.finite_stage erased_joint_stage_mono
  exact ⟨max stage later, A', bodyOut, Nat.le_max_left _ _, rfl,
    R.mono (erased_joint_stage_mono (Nat.le_max_right _ _)), .beta⟩

end Lean4Lean.VEnv.Strengthening
