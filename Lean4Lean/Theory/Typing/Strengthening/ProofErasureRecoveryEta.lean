import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryDescent

/-! # Inferred eta from recovered erased function types

A short endpoint may be any typed expression for which the erased recovery
certificate exposes a Pi. Comparing its recovered domain with the long lambda's
domain makes head eta sound in inferred mode. Both pieces descend from source
typing; equality of the original endpoint types is not a premise.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ProofShape.liftN_lam_inv ProofShape.liftN_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

namespace ProofShape
/-- An inferred head eta certificate keeps source-based Pi recovery and a
recursive inferred-domain comparison. Its variable types come from the oracle. -/
inductive RecoveredEtaHead (Step : ProofShape → ProofShape → Prop)
    (σ : TypeOracle) : ProofShape → ProofShape → Prop where
  | intro : TypeRecovery Step σ f (.forallE D C) → Compare Step false A D →
      EtaHead (.lam A b) f → RecoveredEtaHead Step σ (.lam A b) f
end ProofShape

/-- Original eta has the new inferred certificate whenever the displayed Pi
type is recoverable. Whole-proof collapse remains an identity alternative. -/
theorem proofErase_recovered_eta_forward (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ProofShape.TypeRecovery Step σ (proofErase Γ f) (proofErase Γ (.forallE A B))) :
    proofErase Γ (.lam A (.app f.lift (.bvar 0))) = proofErase Γ f ∨
      ProofShape.RecoveredEtaHead Step σ
        (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) (proofErase Γ f) := by
  rcases proofErase_eta_forward hΓ hf with H | H
  · exact .inl H
  · apply Or.inr
    have hn : ¬ IsProof Γ (.lam A (.app f.lift (.bvar 0))) := by
      intro hp
      obtain ⟨_, _, HE, _⟩ := H.shape
      rw [proofErase_eq_proof.2 hp] at HE
      cases HE
    have EL : proofErase Γ (.lam A (.app f.lift (.bvar 0))) =
        .lam (proofErase Γ A) (proofErase (A :: Γ) (.app f.lift (.bvar 0))) := if_neg hn
    obtain ⟨_, hPi⟩ := hf.isType henv hΓ
    have EPi : proofErase Γ (.forallE A B) =
        .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
      if_neg (not_isProof_of_sort hΓ hPi)
    rw [EPi] at R
    rw [EL] at H ⊢
    exact .intro R .refl H

/-- A variable whose declared type is already a Pi supplies the recovered short
endpoint directly. No lambda shape or separate domain-conversion premise is
required for this concrete inferred-eta case. -/
theorem proofErase_lookup_eta_forward (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ i (.forallE A B)) :
    proofErase Γ (.lam A (.app (VExpr.bvar i).lift (.bvar 0))) = proofErase Γ (.bvar i) ∨
      ProofShape.RecoveredEtaHead Step (erasedTypeOracle Γ)
        (proofErase Γ (.lam A (.app (VExpr.bvar i).lift (.bvar 0)))) (proofErase Γ (.bvar i)) := by
  have hf : env.HasType univs Γ (.bvar i) (.forallE A B) := .bvar hl
  by_cases hp : IsProof Γ (.bvar i)
  · have hpl := (isProof_congr hΓ (IsDefEq.eta hf)).2 hp
    exact .inl ((proofErase_eq_proof.2 hpl).trans (proofErase_eq_proof.2 hp).symm)
  · apply proofErase_recovered_eta_forward hΓ hf
    rw [show proofErase Γ (.bvar i) = .bvar i from if_neg hp,
      ← erasedTypeOracle_valid hΓ hl]
    exact .bvar

/-- Recovery of an exposed erased Pi reconstructs its original domain and
codomain below the insertion, as well as a lower typing of the short function. -/
theorem proofErase_recovered_pi_descend_of_oracleTyping (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hσ : ErasedOracleTyping Γ σ n k)
    (hf : env.HasType univs Γ f T)
    (R : ProofShape.TypeRecovery Step σ ((proofErase Γ f).liftN n k) (.forallE A B)) :
    ∃ D C, env.HasType univs Γ f (.forallE D C) ∧
      (proofErase Γ D).liftN n k = A ∧ (proofErase (D :: Γ) C).liftN n (k+1) = B := by
  obtain ⟨F, hfF, EF⟩ := proofErase_typeRecovery_descend_of_oracleTyping hstep hΓ hΓ' W hσ hf R
  obtain ⟨_, _, Es, EA, EB⟩ := ProofShape.liftN_forallE_inv EF
  obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv Es
  exact ⟨D, C, hfF, by simpa only [← ED] using EA, by simpa only [← EC] using EB⟩

/-- Exact lookup agreement specializes typed-oracle Pi recovery. -/
theorem proofErase_recovered_pi_descend (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hσ : ErasedOracleAbove Γ σ n k)
    (hf : env.HasType univs Γ f T)
    (R : ProofShape.TypeRecovery Step σ ((proofErase Γ f).liftN n k) (.forallE A B)) :
    ∃ D C, env.HasType univs Γ f (.forallE D C) ∧
      (proofErase Γ D).liftN n k = A ∧ (proofErase (D :: Γ) C).liftN n (k+1) = B :=
  proofErase_recovered_pi_descend_of_oracleTyping hstep hΓ hΓ' W hσ.typing hf R

/-- Recovered inferred eta descends for independently typed endpoints. The short
endpoint need not be a lambda; its recovered Pi supplies the missing lower domain.
No equality of endpoint types or inhabitant of a removed binder is assumed. -/
theorem proofErase_recovered_eta_descend (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hσ : ErasedOracleAbove Γ σ n k)
    (he : env.HasType univs Γ e T) (hf : env.HasType univs Γ f U)
    (H : ProofShape.RecoveredEtaHead Step σ
      ((proofErase Γ e).liftN n k) ((proofErase Γ f).liftN n k)) :
    env.IsDefEqU univs Γ e f := by
  generalize Ee : (proofErase Γ e).liftN n k = es at H
  generalize Ef : (proofErase Γ f).liftN n k = fs at H
  cases H with
  | intro HR HD HE =>
    obtain ⟨_, _, Es, EA, Eb⟩ := ProofShape.liftN_lam_inv Ee
    obtain ⟨A, b, rfl, _, EAA, Ebb⟩ := erase_lam_inv Es
    rw [← EAA] at EA
    obtain ⟨D, C, hfPi, ED, EC⟩ :=
      proofErase_recovered_pi_descend hstep hΓ hΓ' W hσ hf (Ef ▸ HR)
    obtain ⟨⟨_, hA⟩, _, _⟩ := he.lam_inv henv hΓ
    obtain ⟨⟨_, hD⟩, _⟩ := (hfPi.isType henv hΓ).forallE_inv henv
    have HAD := (proofErase_compare_descend hstep hΓ hΓ' W hA hD
      (by simpa only [EA, ED] using HD)).2 rfl (not_isProof_of_sort hΓ hA)
    have HE' : ProofShape.EtaHead ((proofErase Γ (.lam A b)).liftN n k)
        ((proofErase Γ f).liftN n k) := by simpa only [Ee, Ef] using HE
    exact proofErase_eta_head_infer hΓ he hfPi HAD HE'.of_liftN

/-- The canonical context oracle instantiates inferred eta below a binder block.
This specializes to every finite recursive K stage with its checked descent. -/
theorem proofErase_compared_K_recovered_eta (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n k Γ Γ')
    (he : env.HasType univs Γ e T) (hf : env.HasType univs Γ f U)
    (H : ProofShape.RecoveredEtaHead (ErasedComparedKStage D stage) (erasedTypeOracle Γ')
      (proofErase Γ' (e.liftN n k)) (proofErase Γ' (f.liftN n k))) :
    env.IsDefEqU univs Γ e f := by
  rw [proofErase_liftN hΓ hΓ' W he, proofErase_liftN hΓ hΓ' W hf] at H
  exact proofErase_recovered_eta_descend (erased_compared_K_stage_descent heq hs stage)
    hΓ hΓ' W (ErasedOracleValid.above (erasedTypeOracle_valid hΓ') hΓ hΓ' W) he hf H

end Lean4Lean.VEnv.Strengthening
