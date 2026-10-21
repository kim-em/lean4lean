import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIdentityRecoveryCover
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedEtaConfluence

/-! # Arbitrary typed instantiation up to a join, conditional on confluence

An identity-redex expansion supplies an exactly recoverable substitution image.
Instantiating the body computation at that image and then contracting its
copies gives a common typed ancestor of the two requested substituted endpoints.
Typed confluence turns this into a common reduct. The confluence assumption is
explicit: this is not a confluence proof or directed substitution transport.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Typed confluence of the joint union suffices for instantiation of every
finite body computation up to a later computational join, with no recovery
premise on the original argument. The conclusion relates the exact original
substituted endpoints, but need not give a directed path between them. This
does not discharge confluence or justify using this lemma circularly in a
confluence proof. -/
theorem proofErase_joint_inst_join_of_confluence
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hcon : ErasedScopedTypedConfluent (ErasedJointUnion D))
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (RB : ScopedCompute (ErasedJointStage D stage) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) out) :
    ∃ later shared, stage ≤ later ∧
      ScopedCompute (ErasedJointStage D later) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) shared ∧
      ScopedCompute (ErasedJointStage D later) (proofEraseCtx Γ)
        (out.inst (proofErase Γ x)) shared := by
  let y := VExpr.app (.lam A (.bvar 0)) x
  obtain ⟨hy, _, RY, HR⟩ := proofErase_identity_recovery_cover
    (Step := ErasedJointStage D 0) hΓA.1 hx
  have hy : env.HasType univs Γ y A := hy
  have RY : ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ y) (proofErase Γ x) := .beta RY
  have RL := proofErase_joint_compute_inst_argument heq hs hΓA hb hy RY
  rw [← proofErase_instN hΓA hx Ctx.InstN.zero hb] at RL
  have RI := proofErase_joint_compute_inst_recoverable heq hs hΓA.1 hy HR hb RB
  simp only [Nat.zero_add] at RI
  obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize
    (erased_joint_stage_descent heq hs stage) hΓA hb rfl rfl RB
  have RR := proofErase_joint_compute_inst_argument heq hs hΓA HB.hasType.2 hy RY
  rw [proofErase_instN hΓA hy Ctx.InstN.zero HB.hasType.2, EB] at RR
  have RT := RI.trans RR
  obtain ⟨shared, HL, HR⟩ := hcon hΓA.1 (hb.instN henv Ctx.InstN.zero hy)
    (RL.mono (fun H => ⟨stage, H⟩)) (RT.mono (fun H => ⟨stage, H⟩))
  obtain ⟨leftStage, HL⟩ := HL.finite_stage erased_joint_stage_mono
  obtain ⟨rightStage, HR⟩ := HR.finite_stage erased_joint_stage_mono
  refine ⟨max stage (max leftStage rightStage), shared, by omega, ?_, ?_⟩
  · exact HL.mono (erased_joint_stage_mono (by omega))
  · exact HR.mono (erased_joint_stage_mono (by omega))

end Lean4Lean.VEnv.Strengthening
