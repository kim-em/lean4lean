import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreRawEtaTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrefixOnly

/-! # Checked prefix/core peaks for computational and displayed eta guards

Endpoint guards witnessed by a literal join or displayed eta transport through
arbitrary ordinary argument computation. Prefix contraction and such argument
computation therefore form a literal commuting square at the first K stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
variable [Params]
namespace ErasedCore

/-- A core endpoint guard ending in a literal join or displayed function eta.
This is a specified fragment of raw checking, not a completeness assumption. -/
inductive EndpointGuard : ProofShape → ProofShape → Prop where
  | join : ProofShape.Compute Step a shared → ProofShape.Compute Step b shared → EndpointGuard a b
  | eta : ProofShape.Compute Step a a' → ProofShape.Compute Step b b' →
      ProofShape.EtaHead a' b' → EndpointGuard a b
  | symm : EndpointGuard a b → EndpointGuard b a

/-- Every selected endpoint guard is accepted by raw checking. -/
theorem EndpointGuard.rawChecked (H : EndpointGuard a b) :
    ProofShape.RawCheckedCompare Step true a b := by
  induction H with
  | join HA HB => exact .compute HA HB (.base .refl)
  | eta HA HB HE => exact .compute HA HB (.base (.etaL HE))
  | symm _ ih => exact ih.symm

/-- Typed endpoint guards in this fragment survive arbitrary independent core
computation with a raw checking certificate at the same computational stage. -/
theorem EndpointGuard.forward
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (H : EndpointGuard (proofErase Γ a) (proofErase Γ b))
    (RA : ProofShape.Compute Step (proofErase Γ a) a')
    (RB : ProofShape.Compute Step (proofErase Γ b) b') :
    ProofShape.RawCheckedCompare Step true a' b' := by
  generalize EA : proofErase Γ a = sa at H
  generalize EB : proofErase Γ b = sb at H
  induction H generalizing a b T a' b' with
  | join HA HB => exact join_guard_forward hcon hΓ ha hb (EA ▸ HA) (EB ▸ HB) RA RB
  | eta HA HB HE => exact head_eta_join_raw_forward hcon hΓ ha hb (EA ▸ HA) (EB ▸ HB) HE RA RB
  | symm H ih => exact (ih hb ha RB RA EB EA).symm

/-- At stage one, contracting a typed prefix with a selected endpoint guard and
computing any of its five arguments form a literal square. The left residual
computes the generated proof domain and minor; the right residual uses the
transported guard. No normalization or contextual-to-raw conversion is assumed. -/
theorem prefix_core_square
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v w α a M m b))
    (HG : EndpointGuard (proofErase Γ a) (proofErase Γ b))
    (Rα : ProofShape.Compute Step (proofErase Γ α) α')
    (Ra : ProofShape.Compute Step (proofErase Γ a) a')
    (RM : ProofShape.Compute Step (proofErase Γ M) M')
    (Rm : ProofShape.Compute Step (proofErase Γ m) m')
    (Rb : ProofShape.Compute Step (proofErase Γ b) b') :
    let S := ErasedPrefixOnlyStage definitions 1
    let source := proofErase Γ (eqRecBeforeMajor v w α a M m b)
    let initial := ProofShape.lam
      (ProofShape.eqProofType w (proofErase Γ α) (proofErase Γ a) (proofErase Γ b))
      ((proofErase Γ m).liftN 1)
    let computed := ProofShape.eqRecBeforeMajor v w α' a' M' m' b'
    let target := ProofShape.lam (ProofShape.eqProofType w α' a' b') (m'.liftN 1)
    ProofShape.Compute S source initial ∧ ProofShape.Compute S source computed ∧
      ProofShape.Compute S initial target ∧ ProofShape.Compute S computed target := by
  dsimp only
  obtain ⟨_, _, _, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have HC := HG.forward hcon hΓ ha hb Ra Rb
  have ES := proofErase_const_spine hΓ (args := [α, a, M, m, b]) ht hn
  change proofErase Γ (eqRecBeforeMajor v w α a M m b) =
    ProofShape.eqRecBeforeMajor v w (proofErase Γ α) (proofErase Γ a)
      (proofErase Γ M) (proofErase Γ m) (proofErase Γ b) at ES
  rw [ES]
  have embed {x y} (H : ProofShape.Compute Step x y) :
      ProofShape.Compute (ErasedPrefixOnlyStage definitions 1) x y :=
    H.mono (fun H => .inl H)
  have Rargs : ProofShape.Compute Step
      (ProofShape.eqRecBeforeMajor v w (proofErase Γ α) (proofErase Γ a)
        (proofErase Γ M) (proofErase Γ m) (proofErase Γ b))
      (ProofShape.eqRecBeforeMajor v w α' a' M' m' b') :=
    .app (.app (.app (.app (.app .refl Rα) Ra) RM) Rm) Rb
  have Rdomain : ProofShape.Compute Step
      (ProofShape.eqProofType w (proofErase Γ α) (proofErase Γ a) (proofErase Γ b))
      (ProofShape.eqProofType w α' a' b') := .app (.app (.app .refl Rα) Ra) Rb
  exact ⟨.base (.inr (.intro HG.rawChecked)), embed Rargs,
    embed (.lam Rdomain (Rm.liftN (fun H => erased_iota_primitive_liftN H))),
    .base (.inr (.intro HC))⟩

end ErasedCore
end Lean4Lean.VEnv.Strengthening
