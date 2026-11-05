import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalPiComparison

/-! # Instantiated codomain checks for independently annotated Pis

A comparison of whole Pis supplies the ordinary domain alignment and the
computed codomain check. A terminal-valued left domain then permits replacing
the binder by an actual argument at the unchanged stage zero.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Comparing two independently typed Pis with a terminal-valued left domain
compares their codomains after the same actual argument is substituted. Neither
domain equality nor a codomain check is supplied separately, and assigned
universes may differ. This does not assert result comparison for two different
arguments or stability under arbitrary nonterminal substitution. -/
theorem stage_zero_terminal_pi_inst_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HA : TerminalDomain Γ A)
    (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs Γ C (.sort w))
    (hE : env.HasType univs (C :: Γ) E (.sort z))
    (hp : env.HasType univs Γ p A)
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE C E))) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ (B.inst p)) (proofErase Γ (E.inst p)) := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
    erased_static_structure_eta_expansion_stage_descent heq hs 0
  have hPiB := HasType.forallE hA hB
  have hPiE := HasType.forallE hC hE
  have HI := proofErase_computed_joint_types_inferred hstep hΓ hPiB hPiE H
  have HPi := (proofErase_computed_joint_compare_reflect hstep hΓ hPiB hPiE HI).2
    rfl (not_isProof_of_sort hΓ hPiB) (not_isProof_of_sort hΓ hPiE)
  obtain ⟨⟨_, HAC⟩, _, HBE⟩ := HPi.forallE_inv henv hΓ
  have HAC := HAC.toU.of_l henv hΓ hA
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hEv : env.HasType univs (A :: Γ) E (.sort v) := HBE.toU.of_l henv hΓA hB |>.hasType.2
  have HB := stage_zero_terminal_pi_codomains_compare heq hs hΓ HA hA HAC hB hE H
  have WS := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := A)).substEq hΓA hp
  have HTP : TerminalImage Γ p :=
    (show TerminalImage (A :: Γ) (.bvar 0) from HA).subst hΓ WS
  exact stage_zero_compare_inst_terminal heq hs hΓ hp HTP hB hEv HB

end Lean4Lean.VEnv.Strengthening
