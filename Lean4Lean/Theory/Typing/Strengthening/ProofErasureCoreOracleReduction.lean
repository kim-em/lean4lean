import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDomainPullback
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureQuotCoreConfluence
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPiExposure

/-! # Forward variable recovery through a reduced ordinary-core oracle

Exact output preservation fails even for beta annotation reduction. Typed
confluence of the repaired ordinary core instead supplies a new recovered
output reached from the old output. This preserves exposed Pi heads. The result
is for the fresh variable and ordinary core, not full joint re-synthesis.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

omit [Params] in
private theorem forget_scope (H : ScopedCompute (fun _ => Step) Δ a b) : Compute Step a b := by
  induction H with
  | base H => exact .base H
  | beta H => exact .beta H
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | proj _ ih => exact .proj ih
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂

/-- Reducing the fresh oracle annotation preserves variable recovery after
possibly computing its selected output further. Typed core confluence resolves
the fork between the annotation reduction and the original recovery path. -/
theorem proofErase_quot_core_variable_recovery_forward
    (hq : QuotRegistered env) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (RA : ScopedCompute (ErasedJointStage (ErasedQuotCore.definitions hq) 0)
      (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ B))
    (R : ScopedTypeRecovery (ErasedJointStage (ErasedQuotCore.definitions hq) 0)
      (proofEraseCtx (A :: Γ)) (.bvar 0) out) :
    ∃ shared, ScopedTypeRecovery (ErasedJointStage (ErasedQuotCore.definitions hq) 0)
        (proofEraseCtx (B :: Γ)) (.bvar 0) shared ∧
      ScopedCompute (ErasedJointStage (ErasedQuotCore.definitions hq) 0)
        (proofEraseCtx (B :: Γ)) out shared := by
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, v, hB⟩
  have RL := RA.rename (fun H _ => erased_iota_primitive_subst H)
    (ContextRenaming.of_liftN hΓ hΓB Ctx.LiftN.one)
  simp only [subst_bvar_liftN] at RL
  have RN := R.bvar_compute
  simp only [proofEraseCtx, contextOracle, TypeOracle.cons] at RN
  have EA := proofErase_liftN hΓ hΓB Ctx.LiftN.one hA
  have RL' : Compute (ErasedQuotCore.Step hq) (proofErase (B :: Γ) A.lift)
      ((proofErase Γ B).liftN 1) := by
    rw [EA]
    exact forget_scope RL
  have RN' : Compute (ErasedQuotCore.Step hq) (proofErase (B :: Γ) A.lift) out := by
    rw [EA]
    exact forget_scope RN
  obtain ⟨shared, HB, Hout⟩ := ErasedQuotCore.confluent hq hcon hΓB (hA.weak henv) RL' RN'
  refine ⟨shared, .convert .bvar ?_, Hout.scoped (fun H => .base H)⟩
  simpa only [proofEraseCtx, contextOracle, TypeOracle.cons] using
    (HB.scoped (Step' := ErasedJointStage (ErasedQuotCore.definitions hq) 0)
      (Δ := proofEraseCtx (B :: Γ)) (fun H => .base H))

/-- An exposed recovered Pi remains exposed after reducing its variable's
annotation in the repaired ordinary core. The new domain and codomain may
change; this theorem does not assert transfer of an argument carrier guard. -/
theorem proofErase_quot_core_variable_pi_forward
    (hq : QuotRegistered env) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (RA : ScopedCompute (ErasedJointStage (ErasedQuotCore.definitions hq) 0)
      (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ B))
    (R : ScopedTypeRecovery (ErasedJointStage (ErasedQuotCore.definitions hq) 0)
      (proofEraseCtx (A :: Γ)) (.bvar 0) (.forallE domain codomain)) :
    ∃ domain' codomain', ScopedTypeRecovery (ErasedJointStage (ErasedQuotCore.definitions hq) 0)
      (proofEraseCtx (B :: Γ)) (.bvar 0) (.forallE domain' codomain') := by
  obtain ⟨shared, HR, HC⟩ := proofErase_quot_core_variable_recovery_forward hq hcon hΓ hA hB RA R
  obtain ⟨domain', codomain', rfl⟩ := HC.forallE_head (fun H => erased_joint_union_head ⟨0, H⟩)
  exact ⟨domain', codomain', HR⟩

end Lean4Lean.VEnv.Strengthening
