import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextCoverage
import Lean4Lean.Theory.Typing.Strengthening.BidirectionalCompositionBoundary

/-! # Typed beta transport and strict normal coverage

Contextual certificates support ordinary same-argument substitution and retain
computation at every comparison position. They include the full bidirectional
normal fragment and the checked pair excluding every normal certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A body comparison transports through two beta redexes with the same typed
argument, preserving its mode and without recovering the argument's type. -/
theorem proofErase_context_beta
    (hsubst : ∀ {a b} {τ : ProofShape.Subst}, Step a b → Step (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hb' : env.HasType univs (A :: Γ) b' B')
    (hx : env.HasType univs Γ x A)
    (H : ProofShape.ContextCompare Step (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) b) (proofErase (A :: Γ) b')) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ (.app (.lam A b) x)) (proofErase Γ (.app (.lam A b') x)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have HC := proofErase_context_compare_instN hsubst hΓA hx Ctx.InstN.zero hb hb' H
  have hl := HasType.app (HasType.lam hA hb) hx
  have hr := HasType.app (HasType.lam hA hb') hx
  exact .compute (.beta (proofErase_beta_forward hΓ hl .beta))
    (.beta (proofErase_beta_forward hΓ hr .beta)) HC

/-- The new relation strictly includes the bidirectional normal fragment.
The witness has a common original type in the empty context and needs only
beta computation, so no primitive-step assumptions are necessary. -/
theorem context_compare_strict_normal :
    ∃ a b T, env.HasType univs [] a T ∧ env.HasType univs [] b T ∧
      ProofShape.ContextCompare Step (proofEraseCtx []) true (proofErase [] a) (proofErase [] b) ∧
      ∀ n, ¬ BiNormal true n [] a b := by
  obtain ⟨a, b, c, T, ha, _, hc, _, _, hn, H⟩ := bidirectional_typed_nontransitivity (Step := Step)
  exact ⟨a, c, T, ha, hc, .base H, hn⟩

end Lean4Lean.VEnv.Strengthening
