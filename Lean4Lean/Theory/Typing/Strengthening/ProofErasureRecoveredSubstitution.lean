import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredWeakening

/-! # Substitution by exactly recoverable erased images

Arbitrary typed substitution need not preserve a selected recovery output. This
restricted law supplies recovery for each substitution image at the substituted
oracle entry. The invariant extends under the distinct endpoint annotations.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Each substituted variable image recovers its substituted oracle assignment. -/
def TypeOracle.RecoverableSubst (Step : ProofShape → ProofShape → Prop)
    (κ τ : TypeOracle) (σ : Subst) : Prop :=
  ∀ i, TypeRecovery Step τ (σ i) ((κ i).subst σ)

/-- Exact image recovery extends beneath a retained annotation. The new bound
variable uses its displayed domain, while old images and their types weaken. -/
theorem TypeOracle.RecoverableSubst.cons
    (hweak : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (H : TypeOracle.RecoverableSubst Step κ τ σ) :
    TypeOracle.RecoverableSubst Step (κ.cons A) (τ.cons (A.subst σ)) σ.lift := by
  intro i
  cases i with
  | zero =>
    simp only [Subst.lift, TypeOracle.cons, lift_subst_lift]
    exact .bvar
  | succ i =>
    simp only [Subst.lift, TypeOracle.cons, lift_subst_lift]
    apply (H i).liftN hweak
    intro j
    simp only [liftVar, Nat.not_lt_zero, if_false, Nat.add_comm, TypeOracle.cons]

/-- Substitution preserves a selected recovery output when all variable images
already recover their exact substituted assignments. -/
theorem TypeRecovery.subst_of_recovery
    (hweak : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (hsubst : ∀ {a b} {σ : Subst}, Step a b → Step (a.subst σ) (b.subst σ))
    (H : TypeRecovery Step κ e T) (hσ : TypeOracle.RecoverableSubst Step κ τ σ) :
    TypeRecovery Step τ (e.subst σ) (T.subst σ) := by
  induction H generalizing σ τ with
  | bvar => exact hσ _
  | sort hu => exact .sort hu
  | const hc hw hn =>
    rw [proofErase_closed_subst ((henv.ordered.closedC hc).instL)]
    exact .const hc hw hn
  | lam _ ih => exact .lam (ih (hσ.cons hweak))
  | app _ ih =>
    rw [subst_inst]
    exact .app (ih hσ)
  | forallE _ _ ihA ihB => exact .forallE (ihA hσ) (ihB (hσ.cons hweak))
  | convert _ RC ih => exact .convert (ih hσ) (RC.subst hsubst)

/-- Both comparison modes survive homogeneous raw substitution with exactly
recoverable images for each endpoint oracle. Binder domains remain distinct. -/
theorem RecoveredCompare.subst_of_recovery
    (hweak : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (hsubst : ∀ {a b} {σ : Subst}, Step a b → Step (a.subst σ) (b.subst σ))
    (H : RecoveredCompare Step κ τ mode a b)
    (hκ : TypeOracle.RecoverableSubst Step κ κ' σ)
    (hτ : TypeOracle.RecoverableSubst Step τ τ' σ) :
    RecoveredCompare Step κ' τ' mode (a.subst σ) (b.subst σ) := by
  induction H generalizing σ κ' τ' with
  | base H => exact .base (H.subst hsubst)
  | app _ _ ihf iha => exact .app (ihf hκ hτ) (iha hκ hτ)
  | proj _ ih => exact .proj (ih hκ hτ)
  | lam _ _ ihA ihb => exact .lam (ihA hκ hτ) (ihb (hκ.cons hweak) (hτ.cons hweak))
  | forallE _ _ ihA ihB => exact .forallE (ihA hκ hτ) (ihB (hκ.cons hweak) (hτ.cons hweak))
  | etaL HR _ HE ih => exact .etaL (HR.subst_of_recovery hweak hsubst hτ) (ih hκ hτ) HE.subst
  | etaR HR _ HE ih => exact .etaR (HR.subst_of_recovery hweak hsubst hκ) (ih hκ hτ) HE.subst
  | compute Ra Rb _ ih => exact .compute (Ra.subst hsubst) (Rb.subst hsubst) (ih hκ hτ)

/-- One-variable instantiation has exactly recoverable images when its argument
recovers the removed declaration. All older variables remain canonical images. -/
theorem TypeOracle.RecoverableSubst.one (Rx : TypeRecovery Step τ x A) :
    TypeOracle.RecoverableSubst Step (τ.cons A) τ (Subst.one x) := by
  intro i
  cases i with
  | zero =>
    simpa only [TypeOracle.cons, Subst.one, Subst.cons, lift_subst_cons, subst_id] using Rx
  | succ i =>
    simp only [TypeOracle.cons, Subst.one, Subst.cons, lift_subst_cons, subst_id]
    exact .bvar

/-- Exact recovery commutes with beta instantiation of a recoverable argument. -/
theorem TypeRecovery.inst_of_recovery
    (hweak : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (hsubst : ∀ {a b} {σ : Subst}, Step a b → Step (a.subst σ) (b.subst σ))
    (H : TypeRecovery Step (τ.cons A) e T) (Rx : TypeRecovery Step τ x A) :
    TypeRecovery Step τ (e.inst x) (T.inst x) := by
  simpa only [inst_eq_subst, Subst.liftN] using
    H.subst_of_recovery hweak hsubst (TypeOracle.RecoverableSubst.one Rx)

/-- Homogeneous beta instantiation preserves both comparison modes when its
argument recovers each endpoint's selected binder type. -/
theorem RecoveredCompare.inst_of_recovery
    (hweak : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (hsubst : ∀ {a b} {σ : Subst}, Step a b → Step (a.subst σ) (b.subst σ))
    (H : RecoveredCompare Step (κ.cons A) (τ.cons B) mode a b)
    (Rx : TypeRecovery Step κ x A) (Rx' : TypeRecovery Step τ x B) :
    RecoveredCompare Step κ τ mode (a.inst x) (b.inst x) := by
  simpa only [inst_eq_subst, Subst.liftN] using
    H.subst_of_recovery hweak hsubst
      (TypeOracle.RecoverableSubst.one Rx) (TypeOracle.RecoverableSubst.one Rx')

/-- The finite compared-K stages satisfy the primitive transport requirements,
so exactly recoverable images preserve stage and mode. -/
theorem RecoveredCompare.compared_K_subst_of_recovery
    (H : RecoveredCompare (ErasedComparedKStage D stage) κ τ mode a b)
    (hκ : TypeOracle.RecoverableSubst (ErasedComparedKStage D stage) κ κ' σ)
    (hτ : TypeOracle.RecoverableSubst (ErasedComparedKStage D stage) τ τ' σ) :
    RecoveredCompare (ErasedComparedKStage D stage) κ' τ' mode (a.subst σ) (b.subst σ) :=
  H.subst_of_recovery (fun H => erased_compared_K_stage_liftN stage H)
    (fun H => erased_compared_K_stage_subst stage H) hκ hτ

end Lean4Lean.VEnv.Strengthening.ProofShape
