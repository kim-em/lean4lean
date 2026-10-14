import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaArguments

/-! # Ambient sort witnesses for erased eta arguments

Recovering a literal sort computationally is sufficient but unnecessary for
classifying a fresh eta argument. An ambient typed representative of the erased
domain also determines that classification below insertion. This uses equality
of erasures, ordinary weakening, and uniqueness; no sort exposure is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Independently sort-typed representatives of the same erasure have
semantically equal universe levels. Their source syntax may differ in proofs. -/
theorem proofErase_sort_levels (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (E : proofErase Γ a = proofErase Γ b) : u ≈ v := by
  obtain ⟨_, H⟩ := (proofErase_reflect hΓ ha hb E).2 (not_isProof_of_sort hΓ ha)
  have HB := ((H.defeq hΓ).of_l henv hΓ ha).hasType.2
  exact (HB.uniqU henv hΓ hb).sort_inv henv hΓ

/-- A sort typing of any ambient representative of the lifted erased domain
fixes the lower domain's sort. The witness need not be the original weakening
and requires no computation or recovery certificate. -/
theorem proofErase_sort_witness_descend (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n k Γ Γ')
    (hA : env.HasType univs Γ A (.sort v))
    (he : env.HasType univs Γ' e (.sort u))
    (E : proofErase Γ' e = (proofErase Γ A).liftN n k) :
    env.HasType univs Γ A (.sort u) := by
  have hAw := hA.weakN henv W
  have EE : proofErase Γ' (A.liftN n k) = proofErase Γ' e :=
    (proofErase_liftN hΓ hΓ' W hA).trans E.symm
  have hu := proofErase_sort_levels hΓ' hAw he EE
  exact (IsDefEq.sortDF (hA.sort_r henv hΓ) (he.sort_r henv hΓ') hu).defeq hA

/-- The fresh argument selected by an ambient sort witness is already correct
below insertion. This is weaker than computational recovery of that sort. -/
theorem proofErase_fresh_argument_of_sort_witness
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hA : env.HasType univs Γ A (.sort v))
    (he : env.HasType univs Γ' e (.sort u))
    (E : proofErase Γ' e = (proofErase Γ A).liftN n k) :
    proofErase (A :: Γ) (.bvar 0) = ProofShape.etaArgument u :=
  proofErase_fresh_argument hΓ (proofErase_sort_witness_descend hΓ hΓ' W hA he E)

/-- Recursive eta's synthetic body has the expected erased shape using only
an ambient sort witness for its domain. Integrating these witnesses into a
contextual certificate does not require the global sort-recovery clause. -/
theorem proofErase_eta_body_of_sort_witness
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hA : env.HasType univs Γ A (.sort v))
    (he : env.HasType univs Γ' e (.sort u))
    (E : proofErase Γ' e = (proofErase Γ A).liftN n k)
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f) :
    (proofErase (A :: Γ) (.app f.lift (.bvar 0))).liftN n (k+1) =
      .app (((proofErase Γ f).liftN n k).liftN 1) (ProofShape.etaArgument u) :=
  proofErase_eta_body_liftN hΓ (proofErase_sort_witness_descend hΓ hΓ' W hA he E) hf hn

end Lean4Lean.VEnv.Strengthening
