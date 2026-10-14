import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCheckedTransport

/-! # Oracle-free checking certificates

This fragment adds common-type lambda checking to the original raw comparison.
It deliberately has no type-recovery premises, so arbitrary raw substitution
remains valid. It can therefore guard recursive computational stages directly.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
namespace ProofShape

/-- Raw compatible comparison with a common-type lambda checking rule. The
inferred rules still compare displayed domains and function positions. -/
inductive RawCheckedCompare (Step : ProofShape → ProofShape → Prop) :
    Bool → ProofShape → ProofShape → Prop where
  | base : Compare Step mode a b → RawCheckedCompare Step mode a b
  | app : RawCheckedCompare Step false f f' → RawCheckedCompare Step true a a' →
      RawCheckedCompare Step mode (.app f a) (.app f' a')
  | proj : RawCheckedCompare Step false m m' → RawCheckedCompare Step mode (.proj s i m) (.proj s i m')
  | lam : RawCheckedCompare Step false A A' → RawCheckedCompare Step mode b b' →
      RawCheckedCompare Step mode (.lam A b) (.lam A' b')
  | lamCommon : RawCheckedCompare Step true b b' →
      RawCheckedCompare Step true (.lam A b) (.lam A' b')
  | forallE : RawCheckedCompare Step false A A' → RawCheckedCompare Step false B B' →
      RawCheckedCompare Step mode (.forallE A B) (.forallE A' B')
  | compute : Compute Step a a' → Compute Step b b' → RawCheckedCompare Step mode a' b' →
      RawCheckedCompare Step mode a b

/-- Oracle-free certificates embed under any two endpoint oracles. -/
theorem RawCheckedCompare.checked (H : RawCheckedCompare Step mode a b) :
    CheckedCompare Step σ τ mode a b := by
  induction H generalizing σ τ with
  | base H => exact .base (.base H)
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | lamCommon _ ih => exact .lamCommon ih
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | compute Ra Rb _ ih => exact .compute Ra Rb ih

/-- The raw checking relation is symmetric. -/
theorem RawCheckedCompare.symm (H : RawCheckedCompare Step mode a b) :
    RawCheckedCompare Step mode b a := by
  induction H with
  | base H => exact .base H.symm
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | lamCommon _ ih => exact .lamCommon ih
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | compute Ra Rb _ ih => exact .compute Rb Ra ih

/-- Inferred raw certificates can be checked at common endpoint types. -/
theorem RawCheckedCompare.common (H : RawCheckedCompare Step mode a b) :
    RawCheckedCompare Step true a b := by
  induction H with
  | base H => exact .base H.common
  | app Hf Ha => exact .app Hf Ha
  | proj H => exact .proj H
  | lam HA _ _ ihb => exact .lam HA ihb
  | lamCommon H => exact .lamCommon H
  | forallE HA HB => exact .forallE HA HB
  | compute Ra Rb _ ih => exact .compute Ra Rb ih

/-- Enlarging computation preserves all checking certificates. -/
theorem RawCheckedCompare.mono (hstep : ∀ {a b}, Step a b → Step' a b)
    (H : RawCheckedCompare Step mode a b) : RawCheckedCompare Step' mode a b := by
  induction H with
  | base H => exact .base (H.mono hstep)
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | lamCommon _ ih => exact .lamCommon ih
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | compute Ra Rb _ ih => exact .compute (Ra.mono hstep) (Rb.mono hstep) ih

/-- Raw substitution needs no typing or exact-image recovery premise. -/
theorem RawCheckedCompare.subst
    (hstep : ∀ {a b} {σ : Subst}, Step a b → Step (a.subst σ) (b.subst σ))
    (H : RawCheckedCompare Step mode a b) :
    RawCheckedCompare Step mode (a.subst σ) (b.subst σ) := by
  induction H generalizing σ with
  | base H => exact .base (H.subst hstep)
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | lamCommon _ ih => exact .lamCommon ih
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | compute Ra Rb _ ih => exact .compute (Ra.subst hstep) (Rb.subst hstep) ih

/-- The fragment weakens without changing the computational stage. -/
theorem RawCheckedCompare.liftN
    (hstep : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (H : RawCheckedCompare Step mode a b) :
    RawCheckedCompare Step mode (a.liftN n k) (b.liftN n k) := by
  induction H generalizing k with
  | base H => exact .base (H.liftN hstep)
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | lamCommon _ ih => exact .lamCommon ih
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | compute Ra Rb _ ih => exact .compute (Ra.liftN hstep) (Rb.liftN hstep) ih
end ProofShape

/-- The oracle-free fragment descends by its checked embedding. Source typing
and common endpoint type conversion are used only at replay. -/
theorem proofErase_rawChecked_compare_descend (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.RawCheckedCompare Step mode
      ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k)) :
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → env.IsDefEqU univs Γ a b) := by
  have hσ : ErasedOracleTyping Γ (erasedTypeOracle Γ') n k :=
    ErasedOracleAbove.typing (ErasedOracleValid.above (erasedTypeOracle_valid hΓ') hΓ hΓ' W)
  exact proofErase_checked_compare_descend hstep hΓ hΓ' W hσ hσ ha hb H.checked

end Lean4Lean.VEnv.Strengthening
