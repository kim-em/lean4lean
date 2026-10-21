import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointContextBeta

/-! # Assembling lambda joins from component joins

The two paths may change the binder annotation independently. Inversion brings
both body paths back to the original context. After joining them there,
proposition beta stability transports their residuals to the two output
contexts. Thus local confluence at the original annotation and body suffices
at the lambda; global confluence is not assumed or proved.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem union_lam_inv
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hn : ¬ IsProof Γ (.lam A b))
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) out) :
    ∃ A' b', out = .lam A' b' ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ A) A' ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx (A :: Γ))
        (proofErase (A :: Γ) b) b' := by
  obtain ⟨stage, R⟩ := R.finite_stage erased_joint_stage_mono
  obtain ⟨later, A', b', _, E, RA, RB⟩ := proofErase_joint_lam_inv_later heq hs hΓ hA hb hn R
  exact ⟨A', b', E, RA.mono (fun H => ⟨later, H⟩), RB.mono (fun H => ⟨later, H⟩)⟩

private theorem assemble_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (RA : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ A) A')
    (RB : ScopedCompute (ErasedJointUnion D) (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) b')
    (JA : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) A' Aout)
    (JB : ScopedCompute (ErasedJointUnion D) (proofEraseCtx (A :: Γ)) b' bout) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (.lam A' b') (.lam Aout bout) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨A₁, HA, EA⟩ := proofErase_scoped_compute_realize
    (erased_joint_union_descent heq hs) hΓ hA rfl rfl RA
  obtain ⟨b₁, HB, EB⟩ := proofErase_scoped_compute_realize
    (erased_joint_union_descent heq hs) hΓA hb rfl rfl RB
  have HT : TypedSource (proofEraseCtx (A :: Γ)) b' :=
    ⟨A :: Γ, b₁, B, hΓA, rfl, HB.hasType.2, EB⟩
  have JB' := proofErase_joint_compute_defeqCtx_of_prop_beta heq hs hregistry Hbeta
    hΓ (.succ .zero HA) HT JB
  apply ScopedCompute.lam JA
  simpa only [proofEraseCtx, EA] using JB'

/-- Under proposition beta stability, confluence at a typed lambda's original
annotation and original body suffices to join any two computations of that
lambda. Component confluence is required only at these two fixed typed sources;
no confluence, comparison closure, or recovery law is assumed for other terms. -/
theorem proofErase_joint_lambda_join_of_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hn : ¬ IsProof Γ (.lam A b))
    (joinA : ∀ {a₁ a₂},
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ A) a₁ →
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ A) a₂ →
      ∃ a₃, ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) a₁ a₃ ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) a₂ a₃)
    (joinB : ∀ {b₁ b₂},
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) b₁ →
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) b₂ →
      ∃ b₃, ScopedCompute (ErasedJointUnion D) (proofEraseCtx (A :: Γ)) b₁ b₃ ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx (A :: Γ)) b₂ b₃)
    (RL : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) left)
    (RR : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) right) :
    ∃ out, ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) left out ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) right out := by
  obtain ⟨AL, bL, rfl, RAL, RBL⟩ := union_lam_inv heq hs hΓ hA hb hn RL
  obtain ⟨AR, bR, rfl, RAR, RBR⟩ := union_lam_inv heq hs hΓ hA hb hn RR
  obtain ⟨Aout, JAL, JAR⟩ := joinA RAL RAR
  obtain ⟨bout, JBL, JBR⟩ := joinB RBL RBR
  exact ⟨.lam Aout bout,
    assemble_residual heq hs hregistry Hbeta hΓ hA hb RAL RBL JAL JBL,
    assemble_residual heq hs hregistry Hbeta hΓ hA hb RAR RBR JAR JBR⟩

end Lean4Lean.VEnv.Strengthening
