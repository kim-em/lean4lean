import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCheckedTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryExistence

/-! # Forward coverage of recursive checked eta

A recovered sort for the displayed domain is sufficient to erase a recursive
eta comparison. Proof-valued endpoints collapse together. Recovery existence
supplies such a sort, without requiring any preselected recovered output.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
variable [Params]

/-- A typed recursive eta comparison erases to a checked certificate. The body
certificate is checked in the displayed binder context; the domain recovery
selects the fresh argument. Proof-valued functions require no synthetic body. -/
theorem proofErase_checked_etaL (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ProofShape.TypeRecovery Step σ (proofErase Γ A) (.sort u))
    (H : ProofShape.CheckedCompare Step (σ.cons (proofErase Γ A))
      (τ.cons (proofErase Γ A)) true (proofErase (A :: Γ) b)
      (proofErase (A :: Γ) (.app f.lift (.bvar 0)))) :
    ProofShape.CheckedCompare Step σ τ true (proofErase Γ (.lam A b)) (proofErase Γ f) := by
  classical
  have hl : env.HasType univs Γ (.lam A b) (.forallE A B) := .lam hA hb
  by_cases hp : IsProof Γ f
  · obtain ⟨P, hfP, hP⟩ := hp
    have hLP : env.HasType univs Γ (.lam A b) P :=
      hl.defeqU_r henv hΓ (hf.uniqU henv hΓ hfP)
    rw [proofErase_eq_proof.2 ⟨P, hLP, hP⟩, proofErase_eq_proof.2 ⟨P, hfP, hP⟩]
    exact .base (.base .refl)
  · have hnl : ¬ IsProof Γ (.lam A b) := by
      rintro ⟨P, hlP, hP⟩
      exact hp ⟨P, hf.defeqU_r henv hΓ (hl.uniqU henv hΓ hlP), hP⟩
    rw [show proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b)
      from if_neg hnl]
    rw [proofErase_eta_body hΓ hA hf hp] at H
    exact .etaBodyL R H

/-- The symmetric forward rule recovers the domain sort in the long endpoint's
oracle. It uses the same body certificate with the opposite orientation. -/
theorem proofErase_checked_etaR (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ProofShape.TypeRecovery Step τ (proofErase Γ A) (.sort u))
    (H : ProofShape.CheckedCompare Step (σ.cons (proofErase Γ A))
      (τ.cons (proofErase Γ A)) true
      (proofErase (A :: Γ) (.app f.lift (.bvar 0))) (proofErase (A :: Γ) b)) :
    ProofShape.CheckedCompare Step σ τ true (proofErase Γ f) (proofErase Γ (.lam A b)) :=
  (proofErase_checked_etaL hΓ hA hb hf R H.symm).symm

/-- Recovery existence supplies a literal recovered sort for every typed
original type. Replay reconstructs that exact sort typing; it need not equal
the universe initially used to type the domain. -/
theorem ErasedRecoveryExists.sort_typed (hstep : ErasedPrimitiveDescent Step)
    (H : ErasedRecoveryExists Step) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) :
    ∃ v, env.HasType univs Γ A (.sort v) ∧
      ProofShape.TypeRecovery Step (erasedTypeOracle Γ) (proofErase Γ A) (.sort v) := by
  obtain ⟨_, R⟩ := H hΓ hA (not_isProof_of_sort hΓ hA)
  obtain ⟨v, R⟩ := H.heads.sort hΓ hA R
  obtain ⟨T, hAT, ET⟩ := proofErase_typeRecovery_replay hstep hΓ (erasedTypeOracle_valid hΓ) hA R
  obtain rfl := erase_sort_inv ET
  exact ⟨v, hAT, R⟩

/-- Any-output recovery existence suffices for recursive eta forward coverage.
No chosen-type recovery or substitution closure is assumed. -/
theorem proofErase_checked_etaL_of_recovery (hstep : ErasedPrimitiveDescent Step)
    (Hex : ErasedRecoveryExists Step) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (hf : env.HasType univs Γ f (.forallE A B))
    (H : ProofShape.CheckedCompare Step (erasedTypeOracle (A :: Γ))
      (erasedTypeOracle (A :: Γ)) true (proofErase (A :: Γ) b)
      (proofErase (A :: Γ) (.app f.lift (.bvar 0)))) :
    ProofShape.CheckedCompare Step (erasedTypeOracle Γ) (erasedTypeOracle Γ) true
      (proofErase Γ (.lam A b)) (proofErase Γ f) := by
  obtain ⟨_, hA', R⟩ := Hex.sort_typed hstep hΓ hA
  exact proofErase_checked_etaL hΓ hA' hb hf R H

/-- Symmetric recursive eta coverage follows from the same any-output recovery
hypothesis. -/
theorem proofErase_checked_etaR_of_recovery (hstep : ErasedPrimitiveDescent Step)
    (Hex : ErasedRecoveryExists Step) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (hf : env.HasType univs Γ f (.forallE A B))
    (H : ProofShape.CheckedCompare Step (erasedTypeOracle (A :: Γ))
      (erasedTypeOracle (A :: Γ)) true
      (proofErase (A :: Γ) (.app f.lift (.bvar 0))) (proofErase (A :: Γ) b)) :
    ProofShape.CheckedCompare Step (erasedTypeOracle Γ) (erasedTypeOracle Γ) true
      (proofErase Γ f) (proofErase Γ (.lam A b)) :=
  (proofErase_checked_etaL_of_recovery hstep Hex hΓ hA hb hf H.symm).symm

end Lean4Lean.VEnv.Strengthening
