import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextComparison

/-! # Recursive eta coverage without sort recovery

Original typing supplies contextual sort witnesses directly. Thus a recursive
body certificate extends through eta without any recovery-existence hypothesis.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
namespace ProofShape

/-- Inferred contextual certificates can also be checked at common types. -/
theorem ContextCompare.common (H : ContextCompare Step Δ mode a b) :
    ContextCompare Step Δ true a b := by
  induction H with
  | base H => exact .base H.common
  | app Hf Ha => exact .app Hf Ha
  | proj H => exact .proj H
  | lam HA _ _ ih => exact .lam HA ih
  | forallE HA HB => exact .forallE HA HB
  | lamSorted SA SA' HA _ _ ih => exact .lamSorted SA SA' HA ih
  | forallSorted SA SA' HA SB SB' HB => exact .forallSorted SA SA' HA SB SB' HB
  | lamCommon H => exact .lamCommon H
  | etaBodyL S H => exact .etaBodyL S H
  | etaBodyR S H => exact .etaBodyR S H
  | compute Ra Rb _ ih => exact .compute Ra Rb ih
  | symm _ ih => exact ih.symm

/-- Every erased term has a reflexive contextual certificate. -/
theorem ContextCompare.refl : ContextCompare Step Δ mode a a := .base (.base .refl)
end ProofShape

/-- Contextual comparison at the canonical raw context descends through an
arbitrary inserted block. No global type-recovery or sort-exposure premise is
needed for the contextual eta and sorted binder rules. -/
theorem proofErase_context_compare_descendN (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.ContextCompare Step (proofEraseCtx Γ') mode
      (proofErase Γ' (a.liftN n k)) (proofErase Γ' (b.liftN n k))) :
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → ¬ IsProof Γ b → env.IsDefEqU univs Γ a b) := by
  rw [proofErase_liftN hΓ hΓ' W ha, proofErase_liftN hΓ hΓ' W hb] at H
  exact proofErase_context_compare_descend hstep hΓ hΓ' W rfl ha hb H

/-- Typed recursive eta erases directly into contextual comparison. Whole-proof
functions collapse with their expansions; otherwise the domain typing supplies
the exact fresh-argument classification. -/
theorem proofErase_context_etaL (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hf : env.HasType univs Γ f (.forallE A B))
    (H : ProofShape.ContextCompare Step (proofEraseCtx (A :: Γ)) true
      (proofErase (A :: Γ) b) (proofErase (A :: Γ) (.app f.lift (.bvar 0)))) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.lam A b)) (proofErase Γ f) := by
  classical
  have hl : env.HasType univs Γ (.lam A b) (.forallE A B) := .lam hA hb
  by_cases hp : IsProof Γ f
  · obtain ⟨P, hfP, hP⟩ := hp
    have hLP := hl.defeqU_r henv hΓ (hf.uniqU henv hΓ hfP)
    rw [proofErase_eq_proof.2 ⟨P, hLP, hP⟩, proofErase_eq_proof.2 ⟨P, hfP, hP⟩]
    exact .refl
  · have hnl : ¬ IsProof Γ (.lam A b) := by
      rintro ⟨P, hlP, hP⟩
      exact hp ⟨P, hf.defeqU_r henv hΓ (hl.uniqU henv hΓ hlP), hP⟩
    rw [show proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b)
      from if_neg hnl]
    rw [proofErase_eta_body hΓ hA hf hp] at H
    exact .etaBodyL (.of_typed hΓ hA) H

/-- Symmetric recursive eta has the same unconditional typed coverage. -/
theorem proofErase_context_etaR (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hf : env.HasType univs Γ f (.forallE A B))
    (H : ProofShape.ContextCompare Step (proofEraseCtx (A :: Γ)) true
      (proofErase (A :: Γ) (.app f.lift (.bvar 0))) (proofErase (A :: Γ) b)) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true
      (proofErase Γ f) (proofErase Γ (.lam A b)) :=
  (proofErase_context_etaL hΓ hA hb hf H.symm).symm

end Lean4Lean.VEnv.Strengthening
