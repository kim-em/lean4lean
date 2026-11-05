import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeBetaPrimitiveResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureBetaSquares
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSteps
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaHistoryEtaSquare
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureLambdaResidual

/-! # All one-step competitors of a certified root beta contraction

The competitor may act at the whole redex, at the function root, in either
lambda component, or in the argument. The original native argument is needed
only when a body computation must cross the cut. Residual endpoints need no new
native coverage. This local square does not yet compose across arbitrary paths.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A primitive root step on a retained literal lambda is beta-neutral when
that function is applied: wrappers contract, and native eta beta-restores the
original body under its selected annotation before the outer cut contracts.
The supplied raw argument is arbitrary and needs no native or typing witness. -/
theorem literal_lambda_primitive_application_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hn : ¬ IsProof Γ (.lam A b))
    (RP : ErasedStaticStructureEtaExpansionUnion D (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) expanded) (arg : ProofShape) :
    ProofShape.BetaRed (.app expanded arg) ((proofErase (A :: Γ) b).inst arg) := by
  have EF : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) := if_neg hn
  rcases computed_lambda_primitive_expansion heq hs hΓ hA hb hn (HasType.lam hA hb) .refl RP with Rβ | RE
  · rw [EF] at Rβ
    exact (ProofShape.BetaRed.app Rβ .refl).trans .beta
  · rw [EF] at RE
    obtain ⟨_, _, Rβ⟩ := static_structure_lambda_eta_component_residual heq hs hΓ hA hb hn RE
    exact (ProofShape.BetaRed.app Rβ .refl).trans .beta

/-- Contracting an initially certified retained beta redex joins every
one-occurrence computation from that same source. This covers all primitive
families and all compatible positions, using the single-step presentation
proved equivalent to ScopedCompute. It does not claim certification of later
residual cuts or confluence of arbitrary finite paths. -/
theorem native_root_beta_step_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (R : ScopedStep (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam A b) x)) out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out shared := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hnf := not_isProof_fn hΓ (HasType.lam hA hb) hx hn
  have EF : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) := if_neg hnf
  have EE : proofErase Γ (.app (.lam A b) x) =
      .app (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) (proofErase Γ x) := by
    rw [show proofErase Γ (.app (.lam A b) x) = .app _ _ from if_neg hn, EF]
  have EI := proofErase_instN hΓA hx Ctx.InstN.zero hb
  rw [EE] at R
  cases R with
  | primitive RP =>
    obtain ⟨shared, RR, Rβ⟩ := native_root_beta_primitive_residual heq hs hΓ hA hb hx hn HR (EE ▸ RP)
    exact ⟨shared, .base RR, .beta Rβ⟩
  | beta => exact ⟨_, EI ▸ ScopedCompute.refl, .refl⟩
  | appL RF =>
    cases RF with
    | primitive RP =>
      exact ⟨_, .refl, .beta (EI ▸ literal_lambda_primitive_application_beta heq hs hΓ hA hb hnf (EF ▸ RP) _)⟩
    | lamDomain RA =>
      exact ⟨_, .refl, .beta (EI ▸ ProofShape.BetaRed.beta)⟩
    | lamBody RB =>
      rename_i outB
      have RB' : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
          (proofErase (A :: Γ) b) outB := by simpa only [proofEraseCtx] using RB.compute
      exact ⟨_, static_structure_body_argument_square heq hs hΓA hb hx HR RB' .refl, .beta .beta⟩
  | appR RX =>
    exact ⟨_, proofErase_static_structure_compute_inst_argument heq hs hΓA hb hx RX.compute, .beta .beta⟩

end Lean4Lean.VEnv.Strengthening
