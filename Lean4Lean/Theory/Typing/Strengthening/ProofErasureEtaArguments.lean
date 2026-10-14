import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryEta

/-! # Recovering the erased fresh argument of recursive eta

A recursive eta comparison must know whether its synthetic fresh argument is a
bound variable or a proof marker. Recovering a sort for the displayed domain
supplies precisely that classification, including below binder insertion.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_sort_inv ProofShape.liftN_sort_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison

open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives

namespace ProofShape
/-- The fresh variable erases exactly when its domain's sort is Prop. -/
noncomputable def etaArgument (u : VLevel) : ProofShape := by
  classical
  exact if u ≈ .zero then .proof else .bvar 0

/-- Insertion beneath the retained eta binder preserves its fresh argument. -/
theorem etaArgument_liftN : (etaArgument u).liftN n (k+1) = etaArgument u := by
  unfold etaArgument
  split <;> simp only [ProofShape.liftN, liftVar, Nat.zero_lt_succ, if_true]

/-- Substitution lifted beneath the eta binder preserves its fresh argument. -/
theorem etaArgument_subst {σ : Subst} : (etaArgument u).subst σ.lift = etaArgument u := by
  unfold etaArgument
  split <;> rfl
end ProofShape

variable [Params]

/-- Proofness of a fresh variable is determined by any sort typing of its domain.
The converse uses type uniqueness, not strengthening or an inhabitant below. -/
theorem isProof_fresh_iff (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) :
    IsProof (A :: Γ) (.bvar 0) ↔ u ≈ .zero := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hx : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  constructor
  · rintro ⟨P, hxP, hP⟩
    have hAP := hx.uniqU henv hΓA hxP
    have hA0 := (hAP.of_r henv hΓA hP).hasType.1
    exact ((hA.weak henv).uniqU henv hΓA hA0).sort_inv henv hΓA
  · intro hu
    have hA0 : env.HasType univs Γ A (.sort .zero) :=
      (IsDefEq.sortDF (hA.sort_r henv hΓ) (by trivial) hu).defeq hA
    exact ⟨_, hx, hA0.weak henv⟩

/-- A domain sort typing determines the exact erased fresh argument. -/
theorem proofErase_fresh_argument (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) :
    proofErase (A :: Γ) (.bvar 0) = ProofShape.etaArgument u := by
  unfold proofErase ProofShape.etaArgument
  rw [isProof_fresh_iff hΓ hA]

/-- Recovering a literal sort for a domain reconstructs that sort typing below
insertion. Only source typing of the domain is supplied below. -/
theorem proofErase_recovered_sort_descend (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hσ : ErasedOracleTyping Γ σ n k)
    (hA : env.HasType univs Γ A T)
    (R : ProofShape.TypeRecovery Step σ ((proofErase Γ A).liftN n k) (.sort u)) :
    env.HasType univs Γ A (.sort u) := by
  obtain ⟨S, hAS, ES⟩ := proofErase_typeRecovery_descend_of_oracleTyping hstep hΓ hΓ' W hσ hA R
  obtain rfl := erase_sort_inv (ProofShape.liftN_sort_inv ES)
  exact hAS

/-- The typed eta body has exactly the argument selected by its recovered
sort. The short endpoint is supplied; no arbitrary erased representative is
invented for a marker. -/
theorem proofErase_eta_body (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f) :
    proofErase (A :: Γ) (.app f.lift (.bvar 0)) =
      .app ((proofErase Γ f).liftN 1) (ProofShape.etaArgument u) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hnb : ¬ IsProof (A :: Γ) (.app f.lift (.bvar 0)) :=
    fun hp => hn ((isProof_congr hΓ (IsDefEq.eta hf)).1 (hp.lam hΓ hA))
  rw [show proofErase (A :: Γ) (.app f.lift (.bvar 0)) =
    .app (proofErase (A :: Γ) f.lift) (proofErase (A :: Γ) (.bvar 0)) from if_neg hnb]
  rw [proofErase_liftN hΓ hΓA Ctx.LiftN.one hf, proofErase_fresh_argument hΓ hA]

/-- The exact eta-body recipe commutes with an outer binder insertion. -/
theorem proofErase_eta_body_liftN (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f) :
    (proofErase (A :: Γ) (.app f.lift (.bvar 0))).liftN n (k+1) =
      .app (((proofErase Γ f).liftN n k).liftN 1) (ProofShape.etaArgument u) := by
  rw [proofErase_eta_body hΓ hA hf hn]
  simp only [ProofShape.liftN, ProofShape.etaArgument_liftN]
  rw [ProofShape.liftN_comm _ n 1 k 0 (Nat.zero_le _)]

end Lean4Lean.VEnv.Strengthening
