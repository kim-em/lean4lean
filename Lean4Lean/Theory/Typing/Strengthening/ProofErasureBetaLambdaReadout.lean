import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSpineRecoveryTransport

/-! # Domain readout through literal-lambda beta wrappers

A finite nest of explicit lambda applications can expose a lambda without
recovering any substituted argument. Native Pi inversion follows its domain
through the same substitutions. This concerns head exposure, not normalization
of arbitrary bodies or arguments.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation

namespace ProofShape
/-- A literal lambda, possibly returned through finitely many explicit
lambda applications. Arguments and the final lambda body are unrestricted.
The indices record the exact domain and body exposed by head beta. -/
inductive BetaLambdaReadout : ProofShape → ProofShape → ProofShape → Prop where
  | lam : BetaLambdaReadout (.lam A b) A b
  | beta : BetaLambdaReadout e B c →
      BetaLambdaReadout (.app (.lam A e) a) (B.inst a) (c.inst a 1)

/-- The recorded readout is reached by a finite beta computation. -/
theorem BetaLambdaReadout.beta_path (H : BetaLambdaReadout e A b) : BetaRed e (.lam A b) := by
  induction H with
  | lam => exact .refl
  | beta _ ih =>
    refine BetaRed.beta.trans ?_
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst] using
      ih.subst (σ := ProofShape.Subst.one _)
end ProofShape

variable [Params]
/-- Every core-native output of a beta-lambda readout is a Pi. Its selected
domain is a forward core reduct of the exposed domain. In particular, no native
certificate for any beta argument is needed to track that selected domain. -/
theorem proofErase_beta_lambda_native_domain
    (hpi : ∀ {A B out}, ¬ Core (.forallE A B) out)
    (hsubst : ∀ {a b τ}, Core a b → Core (a.subst τ) (b.subst τ))
    (H : BetaLambdaReadout source A b)
    (R : ScopedTypeRecovery (fun _ => Core) Δ source out) :
    ∃ X Y, out = .forallE X Y ∧ Compute Core A X := by
  induction H generalizing Δ out with
  | lam =>
    obtain ⟨B, _, RP⟩ := R.lam_compute
    obtain ⟨X, Y, E, RX, _⟩ := RP.core_forget.pi_parts hpi
    exact ⟨X, Y, E, RX⟩
  | @beta e B c A a H ih =>
    obtain ⟨F, G, RF, RC⟩ := R.app_origin
    obtain ⟨Z, RZ, RFG⟩ := RF.lam_compute
    obtain ⟨F', G', EFG, _, RG⟩ := RFG.core_forget.pi_parts hpi
    cases EFG
    obtain ⟨B', C', rfl, RB⟩ := ih RZ
    obtain ⟨B'', C'', rfl, RB', _⟩ := RG.pi_parts hpi
    have RC' : Compute Core (.forallE (B''.inst a) (C''.inst a 1)) out := by
      simpa only [ProofShape.inst] using RC.core_forget
    obtain ⟨X, Y, E, RX, _⟩ := RC'.pi_parts hpi
    refine ⟨X, Y, E, Compute.trans ?_ RX⟩
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
      (RB.trans RB').subst hsubst (σ := ProofShape.Subst.one a)

end Lean4Lean.VEnv.Strengthening
