import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreCarrierReduction

/-! # Typed context conversion with forward-computing raw oracles

Every source realization admits a context-converted target realization. Oracle
entries also compute forward in the repaired ordinary core. This stronger raw
invariant extends under a binder whose annotation itself computes forward.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]
namespace ErasedQuotCore

/-- Context conversion realizable at every source erasure, together with forward
computation of every oracle entry. This does not assert arbitrary conversion
can be witnessed by computation. -/
structure ContextReduction (hq : QuotRegistered env) (Δ Δ' : List ProofShape) : Prop where
  interpretation : ∀ {Γ}, OnCtx Γ (env.IsType univs) → proofEraseCtx Γ = Δ →
    ∃ Γ', OnCtx Γ' (env.IsType univs) ∧ proofEraseCtx Γ' = Δ' ∧ IsDefEqCtx env univs [] Γ Γ'
  lookup : ∀ i, Compute (Step hq) (contextOracle Δ i) (contextOracle Δ' i)

/-- Actual context conversion and computed oracles supply the raw invariant.
Other source realizations convert through equality of their erased contexts. -/
theorem ContextReduction.of_defeqCtx (hq : QuotRegistered env)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, Compute (Step hq) (contextOracle (proofEraseCtx Γ) i)
      (contextOracle (proofEraseCtx Γ') i)) :
    ContextReduction hq (proofEraseCtx Γ) (proofEraseCtx Γ') := by
  refine ⟨?_, HO⟩
  intro Γ₀ hΓ₀ EΓ₀
  exact ⟨Γ', hΓ', rfl, (proofEraseCtx_defeq hΓ₀ hΓ EΓ₀).trans_empty henv W⟩

/-- Sort witnesses transport to the converted raw context without changing
syntax or universe. -/
theorem ContextReduction.sort (W : ContextReduction hq Δ Δ') (S : DomainSort Δ A u) :
    DomainSort Δ' A u := by
  obtain ⟨Γ, a, hΓ, EΓ, ha, Ea⟩ := S
  obtain ⟨Γ', hΓ', EΓ', HC⟩ := W.interpretation hΓ EΓ
  exact ⟨Γ', a, hΓ', EΓ', ha.defeqDFC henv HC, (proofErase_defeqCtx hΓ HC ha).symm.trans Ea⟩

/-- Ordinary-core computation preserves the universe of a realized domain. -/
theorem domainSort_compute (hq : QuotRegistered env)
    (S : DomainSort Δ A u) (R : Compute (Step hq) A B) : DomainSort Δ B u := by
  obtain ⟨Γ, a, hΓ, EΓ, ha, Ea⟩ := S
  obtain ⟨b, _, hb, Eb⟩ := replay hq hΓ ha (by simpa only [Ea] using R)
  exact ⟨Γ, b, hΓ, EΓ, hb, Eb⟩

/-- Context-oracle reduction extends beneath a domain reduced in the target
context. Source typing and replay supply the actual converted target binder;
no syntactic original representative of the raw reduct is assumed. -/
theorem ContextReduction.cons_compute (W : ContextReduction hq Δ Δ')
    (R : Compute (Step hq) A B) : ContextReduction hq (A :: Δ) (B :: Δ') := by
  refine ⟨?_, ?_⟩
  · intro Γ hΓ EΓ
    cases Γ with
    | nil => cases EΓ
    | cons C Γ =>
      obtain ⟨EC, EΓ⟩ := List.cons.inj EΓ
      obtain ⟨hΓ, u, hC⟩ := hΓ
      obtain ⟨Γ', hΓ', EΓ', HC⟩ := W.interpretation hΓ EΓ
      have hC' := hC.defeqDFC henv HC
      have EC' := (proofErase_defeqCtx hΓ HC hC).symm.trans EC
      obtain ⟨C', HR, hC'', EC''⟩ := replay hq hΓ' hC' (by simpa only [EC'] using R)
      have HE := HR.simAt (sound hq) hΓ' _ hC'
      refine ⟨C' :: Γ', ⟨hΓ', u, hC''⟩, ?_, .succ HC (HE.defeqDFC henv (HC.symm henv.ordered))⟩
      simp only [proofEraseCtx, EC'', EΓ']
  · intro i
    cases i with
    | zero => exact R.liftN (fun H => erased_iota_primitive_liftN H)
    | succ i => exact (W.lookup i).liftN (fun H => erased_iota_primitive_liftN H)

/-- An unchanged displayed binder is the reflexive-domain case. -/
theorem ContextReduction.cons (W : ContextReduction hq Δ Δ') :
    ContextReduction hq (A :: Δ) (A :: Δ') := W.cons_compute .refl

end ErasedQuotCore
end Lean4Lean.VEnv.Strengthening
