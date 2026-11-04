import Lean4Lean.Theory.Typing.Strengthening.ProofErasureMaskedConstructorRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedEtaBeta

/-! # Native recovery at guarded expansion targets

Function eta recovers the selected Pi at its target by lifting the original
native certificate and applying it to the correctly erased fresh variable.
The typed eta substitution identity handles proof domains. Together with
constructor recovery, both eta rules preserve their selected native guard.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- A function-eta target recovers its exact selected Pi, including dependent
proof domains. Only renaming of native guards is required; no native image or
source-stability assumption is used. -/
theorem proofErase_function_eta_output_native
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hinclude : ∀ {Δ a b}, Source Δ a b → Target Δ a b)
    (hrename : ∀ {Δ Δ' a b τ}, Target Δ a b → ContextRenaming Δ Δ' τ →
      Target Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ f T)
    (RN : ScopedTypeRecovery Source (proofEraseCtx Γ) (proofErase Γ f) (.forallE A B))
    (SD : DomainSort (proofEraseCtx Γ) A u) :
    ScopedTypeRecovery Target (proofEraseCtx Γ)
      (.lam A (.app ((proofErase Γ f).liftN 1) (etaArgument u))) (.forallE A B) := by
  have W : Ctx.LiftN 0 0 Γ Γ := .zero []
  obtain ⟨D, C, hfD, ED, EC⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ hΓ W ht
    (by simpa only [ProofShape.liftN_zero] using RN)
  simp only [ProofShape.liftN_zero] at ED EC
  obtain ⟨_, hPi⟩ := hfD.isType henv hΓ
  obtain ⟨⟨_, hD⟩, _, hC⟩ := hPi.forallE_inv henv
  have hD := DomainSort.descend (by simpa only [ProofShape.liftN_zero, ED] using SD) hΓ hΓ W hD
  have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
  have RL := (RN.mono hinclude).rename hrename (ContextRenaming.of_liftN hΓ hΓD Ctx.LiftN.one)
  simp only [subst_bvar_liftN, ProofShape.liftN] at RL
  have RB := ScopedTypeRecovery.app (a := etaArgument u) RL
  rw [← EC, proofErase_eta_inst hΓ hD hC] at RB
  simpa only [proofEraseCtx, ED, EC] using ScopedTypeRecovery.lam RB

/-- Every subsequent native type conversion can be retained after function
eta, because the selected Pi itself is recovered exactly. -/
theorem proofErase_function_eta_output_convert
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hinclude : ∀ {Δ a b}, Source Δ a b → Target Δ a b)
    (hrename : ∀ {Δ Δ' a b τ}, Target Δ a b → ContextRenaming Δ Δ' τ →
      Target Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ f T)
    (RN : ScopedTypeRecovery Source (proofEraseCtx Γ) (proofErase Γ f) (.forallE A B))
    (SD : DomainSort (proofEraseCtx Γ) A u)
    (RC : ScopedCompute Target (proofEraseCtx Γ) (.forallE A B) out) :
    ScopedTypeRecovery Target (proofEraseCtx Γ)
      (.lam A (.app ((proofErase Γ f).liftN 1) (etaArgument u))) out :=
  (proofErase_function_eta_output_native hstep hinclude hrename hΓ ht RN SD).convert RC

/-- Function eta at the next stage preserves its exact Pi guard at the old
stage, even when that guard already contains arbitrary structure eta. -/
theorem static_function_eta_output_previous_stage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ f T)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n)
      (proofEraseCtx Γ) (proofErase Γ f) (.forallE A B))
    (SD : DomainSort (proofEraseCtx Γ) A u) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n+1)) (proofEraseCtx Γ)
        (proofErase Γ f) (.lam A (.app ((proofErase Γ f).liftN 1) (etaArgument u))) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx Γ)
        (.lam A (.app ((proofErase Γ f).liftN 1) (etaArgument u))) (.forallE A B) := by
  exact ⟨.base (.inr (.inr (.inr (.inr (.inl (.intro RN SD)))))),
    proofErase_function_eta_output_native (erased_static_structure_eta_expansion_stage_descent heq hs n)
      (fun H => H) (erased_static_structure_eta_expansion_stage_rename heq hs n) hΓ ht RN SD⟩

end Lean4Lean.VEnv.Strengthening
