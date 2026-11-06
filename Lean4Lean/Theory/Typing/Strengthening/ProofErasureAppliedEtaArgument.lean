import Lean4Lean.Theory.Typing.Strengthening.ProofErasureHereditaryArgumentHistory

/-! # Applied eta supplies an ordinary argument history

Once the eta-expanded function is applied, its wrapper contracts by beta.
This admits further typed consumers and core/cast history composition without
promoting a bare eta comparison to directed computation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Applying a typed eta expansion to its argument gives an ordinary-core
argument history at the actual instantiated result type. Proof-domain arguments
are handled by typed erasure of the original beta step. -/
theorem ArgumentHistory.applied_eta
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f (.forallE A B))
    (hx : env.HasType univs Γ x A) :
    ArgumentHistory D n Γ (B.inst x)
      (proofErase Γ (.app (.lam A (.app f.lift (.bvar 0))) x))
      (proofErase Γ (.app f x)) := by
  have ht := (IsDefEq.eta hf).hasType.1.app hx
  apply ArgumentHistory.core hΓ ht
  apply ProofShape.Compute.beta
  apply proofErase_beta_forward hΓ ht
  simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar, Nat.lt_irrefl, ↓reduceIte,
    VExpr.liftN_zero] using
    (VExpr.BetaRed.beta (A := A) (b := .app f.lift (.bvar 0)) (a := x))

omit [Params] in
/-- Every typed consumer of the applied eta pair has a hereditary stage-zero
computation. This allows arbitrary later typed substitutions and full-core
paths, and can be composed with the existing certified cast histories. -/
theorem EnvironmentCore.hereditary_applied_eta_consumer
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ A B f x t T}, env.HasCanonicalEq → OnCtx Γ (env.IsType U) →
      env.HasType U Γ f (.forallE A B) → env.HasType U Γ x A →
      env.HasType U (B.inst x :: Γ) t T →
      CoreFamilyCast.Hereditary definitions 0 .compute (proofEraseCtx Γ)
        (proofErase Γ (t.inst (.app (.lam A (.app f.lift (.bvar 0))) x)))
        (proofErase Γ (t.inst (.app f x))) := by
  letI := henv.params U
  intro Γ A B f x t T heq hΓ hf hx ht
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  have R := ArgumentHistory.applied_eta (D := definitions) (n := 0) hΓ hf hx
  have HI := (R.interpret heq sound (levelCompatible (fun H => H)) (fun H => H)
    (typed_level_core_confluence (fun H => H)) hlookup (hr.eqRec_target heq hn).2.1 (no_eqRec heq)).2 ht
  have hleft := (IsDefEq.eta hf).hasType.1.app hx
  have hright := hf.app hx
  have hΓT : OnCtx (B.inst x :: Γ) (env.IsType U) := ⟨hΓ, hright.isType henv hΓ⟩
  rw [← proofErase_instN hΓT hleft Ctx.InstN.zero ht,
    ← proofErase_instN hΓT hright Ctx.InstN.zero ht] at HI
  exact HI

end Lean4Lean.VEnv.Strengthening
