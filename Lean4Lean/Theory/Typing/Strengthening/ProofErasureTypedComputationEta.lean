import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationBinders

/-! # Function eta in typed computation chains

The generic variable's declaration supplies exact native recovery. Its eta step
is instantiated using typed computation-chain substitution, which uses a beta
fork instead of transporting the native guard to the actual function.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Every ordinary function eta equation has a typed computation chain,
without native coverage of the actual function or any fork-joining premise.
Proof functions and proof input domains are included. -/
theorem TypedComputationEq.eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) :
    TypedComputationEq D Γ f (.lam A (.app f.lift (.bvar 0))) (.forallE A B) := by
  obtain ⟨u, hG⟩ := hf.isType henv hΓ
  have hΓG : OnCtx (.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, u, hG⟩
  have hg : env.HasType univs (.forallE A B :: Γ) (.bvar 0) (VExpr.forallE A B).lift := .bvar .zero
  have RG := static_structure_exact_native_eta (D := D) hΓG hg
    (fun hn => proofErase_scoped_lookup_recovery hΓG .zero hn .refl)
  have HG := TypedComputationEq.step (IsDefEq.eta hg).symm RG
  have HI := HG.inst heq hs hΓ hG hf
  simpa [VExpr.inst, VExpr.instVar, VExpr.inst_liftN, VExpr.lift, VExpr.liftN, liftVar] using HI

/-- Proof irrelevance is a computation-chain edge because both proof payloads
erase to the same marker. No fork-joining premise is involved. -/
theorem TypedComputationEq.proof_irrel
    (hP : env.HasType univs Γ P (.sort .zero))
    (ha : env.HasType univs Γ a P) (hb : env.HasType univs Γ b P) :
    TypedComputationEq D Γ a b P := by
  apply TypedComputationEq.of_erasure_eq (.proofIrrel hP ha hb)
  rw [proofErase_eq_proof.2 ⟨P, ha, hP⟩, proofErase_eq_proof.2 ⟨P, hb, hP⟩]

end Lean4Lean.VEnv.Strengthening
