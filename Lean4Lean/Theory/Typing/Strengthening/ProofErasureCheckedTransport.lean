import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCheckedComparison
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredSubstitution

/-! # Transport for checked erased comparison

The checking rule keeps the endpoint oracles distinct beneath lambdas. Renaming
is unconditional; substitution uses the same exact-image recovery invariant as
the underlying inferred recovery, rather than assuming arbitrary typed closure.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
namespace ProofShape

/-- Symmetry exchanges both endpoint oracles. -/
theorem CheckedCompare.symm (H : CheckedCompare Step σ τ mode a b) :
    CheckedCompare Step τ σ mode b a := by
  induction H with
  | base H => exact .base H.symm
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | etaL HR _ HE ih => exact .etaR HR ih HE
  | etaR HR _ HE ih => exact .etaL HR ih HE
  | lamCommon _ ih => exact .lamCommon ih
  | recover RA RB _ _ ihT ihC => exact .recover RB RA ihT ihC
  | compute Ra Rb _ ih => exact .compute Rb Ra ih

/-- An inferred certificate can also be checked at common endpoint types. -/
theorem CheckedCompare.common (H : CheckedCompare Step σ τ mode a b) :
    CheckedCompare Step σ τ true a b := by
  induction H with
  | base H => exact .base H.common
  | app Hf Ha => exact .app Hf Ha
  | proj H => exact .proj H
  | lam HA _ _ ihb => exact .lam HA ihb
  | forallE HA HB => exact .forallE HA HB
  | etaL HR HD HE => exact .etaL HR HD HE
  | etaR HR HD HE => exact .etaR HR HD HE
  | lamCommon H => exact .lamCommon H
  | recover RA RB HT HC => exact .recover RA RB HT HC
  | compute Ra Rb _ ih => exact .compute Ra Rb ih

/-- Checked comparison weakens along both type oracles without changing mode. -/
theorem CheckedCompare.liftN
    (hstep : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (H : CheckedCompare Step σ τ mode a b)
    (hσ : TypeOracle.Renames n k σ σ') (hτ : TypeOracle.Renames n k τ τ') :
    CheckedCompare Step σ' τ' mode (a.liftN n k) (b.liftN n k) := by
  induction H generalizing k σ' τ' with
  | base H => exact .base (H.liftN hstep hσ hτ)
  | app _ _ ihf iha => exact .app (ihf hσ hτ) (iha hσ hτ)
  | proj _ ih => exact .proj (ih hσ hτ)
  | lam _ _ ihA ihb => exact .lam (ihA hσ hτ) (ihb hσ.cons hτ.cons)
  | forallE _ _ ihA ihB => exact .forallE (ihA hσ hτ) (ihB hσ.cons hτ.cons)
  | etaL HR _ HE ih => exact .etaL (HR.liftN hstep hτ) (ih hσ hτ) HE.liftN
  | etaR HR _ HE ih => exact .etaR (HR.liftN hstep hσ) (ih hσ hτ) HE.liftN
  | lamCommon _ ih => exact .lamCommon (ih hσ.cons hτ.cons)
  | recover RA RB _ _ ihT ihC =>
    exact .recover (RA.liftN hstep hσ) (RB.liftN hstep hτ) (ihT hσ hτ) (ihC hσ hτ)
  | compute Ra Rb _ ih => exact .compute (Ra.liftN hstep) (Rb.liftN hstep) (ih hσ hτ)

/-- Exactly recoverable substitution images preserve checking and inference,
including the mode switch through recovered endpoint types. -/
theorem CheckedCompare.subst_of_recovery
    (hweak : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (hsubst : ∀ {a b} {σ : Subst}, Step a b → Step (a.subst σ) (b.subst σ))
    (H : CheckedCompare Step κ τ mode a b)
    (hκ : TypeOracle.RecoverableSubst Step κ κ' σ)
    (hτ : TypeOracle.RecoverableSubst Step τ τ' σ) :
    CheckedCompare Step κ' τ' mode (a.subst σ) (b.subst σ) := by
  induction H generalizing σ κ' τ' with
  | base H => exact .base (H.subst_of_recovery hweak hsubst hκ hτ)
  | app _ _ ihf iha => exact .app (ihf hκ hτ) (iha hκ hτ)
  | proj _ ih => exact .proj (ih hκ hτ)
  | lam _ _ ihA ihb => exact .lam (ihA hκ hτ) (ihb (hκ.cons hweak) (hτ.cons hweak))
  | forallE _ _ ihA ihB => exact .forallE (ihA hκ hτ) (ihB (hκ.cons hweak) (hτ.cons hweak))
  | etaL HR _ HE ih => exact .etaL (HR.subst_of_recovery hweak hsubst hτ) (ih hκ hτ) HE.subst
  | etaR HR _ HE ih => exact .etaR (HR.subst_of_recovery hweak hsubst hκ) (ih hκ hτ) HE.subst
  | lamCommon _ ih => exact .lamCommon (ih (hκ.cons hweak) (hτ.cons hweak))
  | recover RA RB _ _ ihT ihC =>
    exact .recover (RA.subst_of_recovery hweak hsubst hκ)
      (RB.subst_of_recovery hweak hsubst hτ) (ihT hκ hτ) (ihC hκ hτ)
  | compute Ra Rb _ ih => exact .compute (Ra.subst hsubst) (Rb.subst hsubst) (ih hκ hτ)
end ProofShape

/-- Concrete checked comparison weakens at the same finite computational stage. -/
theorem ErasedCheckedComparison.weakN (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n k Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ErasedCheckedComparison D stage mode Γ a b) :
    ErasedCheckedComparison D stage mode Γ' (a.liftN n k) (b.liftN n k) := by
  unfold ErasedCheckedComparison at H ⊢
  rw [proofErase_liftN hΓ hΓ' W ha, proofErase_liftN hΓ hΓ' W hb]
  exact H.liftN (fun h => erased_compared_K_stage_liftN stage h)
    (erasedTypeOracle_renames hΓ hΓ' W) (erasedTypeOracle_renames hΓ hΓ' W)

end Lean4Lean.VEnv.Strengthening
