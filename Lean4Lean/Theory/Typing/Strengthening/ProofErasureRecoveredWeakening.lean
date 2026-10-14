import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredComparison

/-! # Weakening contextual erased recovery and comparison

Both endpoint oracles rename with the terms. Their extensions commute with
insertion beneath each retained binder, even when the endpoint annotations
differ. Every finite K stage therefore preserves recovered comparison at the
same stage and mode.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

namespace ProofShape
/-- Pointwise renaming of the types assigned to retained variables. -/
def TypeOracle.Renames (n k : Nat) (σ τ : TypeOracle) : Prop :=
  ∀ i, τ (liftVar n i k) = (σ i).liftN n k

/-- Retaining a binder extends a renaming of type oracles. -/
theorem TypeOracle.Renames.cons (H : TypeOracle.Renames n k σ τ) :
    TypeOracle.Renames n (k+1) (σ.cons A) (τ.cons (A.liftN n k)) := by
  intro i
  cases i with
  | zero =>
    simp only [liftVar_lt (Nat.zero_lt_succ _), TypeOracle.cons]
    exact liftN_comm _ n 1 k 0 (Nat.zero_le _)
  | succ i =>
    simp only [liftVar_succ, TypeOracle.cons, H i]
    exact liftN_comm _ n 1 k 0 (Nat.zero_le _)

variable [Params]

/-- Recovery computations weaken together with their source and context oracle. -/
theorem TypeRecovery.liftN
    (hstep : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (H : TypeRecovery Step σ e T) (hσ : TypeOracle.Renames n k σ τ) :
    TypeRecovery Step τ (e.liftN n k) (T.liftN n k) := by
  induction H generalizing k τ with
  | bvar =>
    simp only [ProofShape.liftN, ← hσ _]
    exact .bvar
  | sort hu => exact .sort hu
  | const hc hw hn =>
    rw [proofErase_closed_liftN ((henv.ordered.closedC hc).instL.mono (Nat.zero_le _))]
    exact .const hc hw hn
  | lam _ ih => exact .lam (ih hσ.cons)
  | app _ ih =>
    have Hinst (B a : ProofShape) : (B.inst a).liftN n k =
        (B.liftN n (k+1)).inst (a.liftN n k) := by
      simpa only [Nat.add_zero] using liftN_instN B a n k 0
    simp only [ProofShape.liftN, Hinst]
    exact .app (ih hσ)
  | forallE _ _ ihA ihB => exact .forallE (ihA hσ) (ihB hσ.cons)
  | convert _ RC ih => exact .convert (ih hσ) (RC.liftN hstep)

/-- Compatible comparison weakens with both endpoint oracles. The mode and
primitive relation stay fixed; no type-recovery completeness is needed. -/
theorem RecoveredCompare.liftN
    (hstep : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (H : RecoveredCompare Step σ τ mode a b)
    (hσ : TypeOracle.Renames n k σ σ') (hτ : TypeOracle.Renames n k τ τ') :
    RecoveredCompare Step σ' τ' mode (a.liftN n k) (b.liftN n k) := by
  induction H generalizing k σ' τ' with
  | base H => exact .base (H.liftN hstep)
  | app _ _ ihf iha => exact .app (ihf hσ hτ) (iha hσ hτ)
  | proj _ ih => exact .proj (ih hσ hτ)
  | lam _ _ ihA ihb => exact .lam (ihA hσ hτ) (ihb hσ.cons hτ.cons)
  | forallE _ _ ihA ihB => exact .forallE (ihA hσ hτ) (ihB hσ.cons hτ.cons)
  | etaL HR _ HE ih => exact .etaL (HR.liftN hstep hτ) (ih hσ hτ) HE.liftN
  | etaR HR _ HE ih => exact .etaR (HR.liftN hstep hσ) (ih hσ hτ) HE.liftN
  | compute Ra Rb _ ih => exact .compute (Ra.liftN hstep) (Rb.liftN hstep) (ih hσ hτ)
end ProofShape

variable [Params]

private theorem erasedTypeOracle_outOfBounds (hi : Γ.length ≤ i) :
    erasedTypeOracle Γ i = .proof := by
  induction Γ generalizing i with
  | nil => rfl
  | cons A Γ ih =>
    cases i with
    | zero => simp at hi
    | succ i =>
      change (erasedTypeOracle Γ i).liftN 1 = .proof
      rw [ih (by simpa using hi)]
      rfl

/-- Canonical erased context oracles rename at every index. Out-of-context
entries remain the default marker; actual entries use typed weakening. -/
theorem erasedTypeOracle_renames (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n k Γ Γ') :
    ProofShape.TypeOracle.Renames n k (erasedTypeOracle Γ) (erasedTypeOracle Γ') := by
  intro i
  by_cases hi : i < Γ.length
  · obtain ⟨A, hl⟩ := Lookup.ofLt hi
    rw [erasedTypeOracle_valid hΓ hl]
    exact ErasedOracleValid.above (erasedTypeOracle_valid hΓ') hΓ hΓ' W hl
  · obtain ⟨Γ₀, As, Δ, Δ', hn, hΔ, hΔ', E, E'⟩ := W.isSuffix
    have hlen : Γ'.length = Γ.length + n ∧ k ≤ Γ.length := by
      rw [E, E']
      simp only [List.length_append]
      omega
    rw [liftVar_le (show k ≤ i by omega), erasedTypeOracle_outOfBounds (by omega),
      erasedTypeOracle_outOfBounds (by omega)]
    rfl

/-- The concrete contextual comparison weakens at the same finite K stage. -/
theorem ErasedRecoveredComparison.weakN (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n k Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ErasedRecoveredComparison D stage mode Γ a b) :
    ErasedRecoveredComparison D stage mode Γ' (a.liftN n k) (b.liftN n k) := by
  unfold ErasedRecoveredComparison at H ⊢
  rw [proofErase_liftN hΓ hΓ' W ha, proofErase_liftN hΓ hΓ' W hb]
  exact H.liftN (fun h => erased_compared_K_stage_liftN stage h)
    (erasedTypeOracle_renames hΓ hΓ' W) (erasedTypeOracle_renames hΓ hΓ' W)

end Lean4Lean.VEnv.Strengthening
