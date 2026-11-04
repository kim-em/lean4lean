import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTransparentExpansionResidual

/-! # Common core reducts of typed contextual computation

Root joins extend through compatible computation when the target core is
confluent at typed sources. Replay supplies the typed middle term needed to
compose joins; no confluence of the source relation is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

namespace ProofShape
/-- Two raw shapes have an exact common reduct in a context-independent core. -/
def ComputeJoin (Core : ProofShape → ProofShape → Prop) (a b : ProofShape) : Prop :=
  ∃ shared, Compute Core a shared ∧ Compute Core b shared

/-- Every raw shape joins itself. -/
theorem ComputeJoin.refl : ComputeJoin Core a a := ⟨a, .refl, .refl⟩
/-- The two branches of an exact join can be exchanged. -/
theorem ComputeJoin.symm (H : ComputeJoin Core a b) : ComputeJoin Core b a := by
  obtain ⟨out, RA, RB⟩ := H
  exact ⟨out, RB, RA⟩
/-- A forward core path supplies a join. -/
theorem ComputeJoin.of_compute (R : Compute Core a b) : ComputeJoin Core a b := ⟨b, R, .refl⟩
/-- Independent function and argument joins combine. -/
theorem ComputeJoin.app (H : ComputeJoin Core f g) (K : ComputeJoin Core x y) :
    ComputeJoin Core (.app f x) (.app g y) := by
  obtain ⟨f', RF, RG⟩ := H
  obtain ⟨x', RX, RY⟩ := K
  exact ⟨_, .app RF RX, .app RG RY⟩
/-- Independent annotation and body joins combine under a lambda. -/
theorem ComputeJoin.lam (H : ComputeJoin Core A D) (K : ComputeJoin Core b c) :
    ComputeJoin Core (.lam A b) (.lam D c) := by
  obtain ⟨X, RA, RD⟩ := H
  obtain ⟨y, RB, RC⟩ := K
  exact ⟨_, .lam RA RB, .lam RD RC⟩
/-- Independent domain and codomain joins combine under a Pi. -/
theorem ComputeJoin.forallE (H : ComputeJoin Core A D) (K : ComputeJoin Core B C) :
    ComputeJoin Core (.forallE A B) (.forallE D C) := by
  obtain ⟨X, RA, RD⟩ := H
  obtain ⟨Y, RB, RC⟩ := K
  exact ⟨_, .forallE RA RB, .forallE RD RC⟩
/-- Projection preserves a join of major premises. -/
theorem ComputeJoin.proj (H : ComputeJoin Core a b) : ComputeJoin Core (.proj s i a) (.proj s i b) := by
  obtain ⟨out, RA, RB⟩ := H
  exact ⟨_, .proj RA, .proj RB⟩
/-- Core substitution closure transports both branches without native images. -/
theorem ComputeJoin.subst (hsubst : ∀ {a b σ}, Core a b → Core (a.subst σ) (b.subst σ))
    (H : ComputeJoin Core a b) : ComputeJoin Core (a.subst σ) (b.subst σ) := by
  obtain ⟨out, RA, RB⟩ := H
  exact ⟨_, RA.subst hsubst, RB.subst hsubst⟩
end ProofShape

variable [Params]
/-- Confluence of the context-independent target core only at actual typed
source erasures. This is supplied by the ordinary-core confluence theorems. -/
def TypedCoreConfluence (Core : ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ e T a b}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
    Compute Core (proofErase Γ e) a → Compute Core (proofErase Γ e) b →
    ∃ shared, Compute Core a shared ∧ Compute Core b shared

/-- A typed middle endpoint is enough to compose joins. The outer endpoints
need no independently supplied representatives or common typing. -/
theorem ProofShape.ComputeJoin.trans_typed (hc : TypedCoreConfluence Core)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (H : ComputeJoin Core a (proofErase Γ e)) (K : ComputeJoin Core (proofErase Γ e) b) :
    ComputeJoin Core a b := by
  obtain ⟨left, RA, RL⟩ := H
  obtain ⟨right, RR, RB⟩ := K
  obtain ⟨out, HL, HR⟩ := hc hΓ ht RL RR
  exact ⟨out, RA.trans HL, RB.trans HR⟩

/-- Typed contextual paths preserve exact core joinability whenever each
primitive does. Source replay, rather than source confluence or normalization,
supplies every intermediate typing needed for transitive composition. -/
theorem proofErase_scoped_compute_core_join
    (hstep : ErasedScopedPrimitiveDescent Step) (hc : TypedCoreConfluence Core)
    (hroot : ∀ {Γ e T Δ a b}, Step Δ a b → OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ e T → proofEraseCtx Γ = Δ → proofErase Γ e = a → ComputeJoin Core a b)
    (R : ScopedCompute Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source) : ComputeJoin Core source out := by
  induction R generalizing Γ e T with
  | base R => exact hroot R hΓ ht EΓ Ee
  | beta R => exact .of_compute (.beta R)
  | trans R S ihR ihS =>
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize hstep hΓ ht EΓ Ee R
    have H := ihR hΓ ht EΓ Ee
    have K := ihS hΓ HE.hasType.2 EΓ EE
    rw [← EE] at H K
    exact H.trans_typed hc hΓ HE.hasType.2 K
  | app RF RX ihf ihx =>
    obtain ⟨f, x, rfl, _, EF, EX⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
    exact (ihf hΓ hf EΓ EF).app (ihx hΓ hx EΓ EX)
  | proj RM ihm =>
    obtain ⟨m, rfl, _, EM⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact (ihm hΓ hm.hasType.2 EΓ EM).proj
  | lam RA RB ihA ihb =>
    obtain ⟨A, b, rfl, _, EA, EB⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    exact (ihA hΓ hA EΓ EA).lam
      (ihb (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hb (by simp only [proofEraseCtx, EA, EΓ]) EB)
  | forallE RA RB ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    exact (ihA hΓ hA EΓ EA).forallE
      (ihB (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hB (by simp only [proofEraseCtx, EA, EΓ]) EB)

end Lean4Lean.VEnv.Strengthening
