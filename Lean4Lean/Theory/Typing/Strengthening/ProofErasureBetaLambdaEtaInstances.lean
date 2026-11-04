import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaLambdaEtaStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEnvironmentCore
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaBetaSquares
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreBetaSquare

/-! # Concrete beta-lambda eta confluence and beta squares

The augmented environment core discharges all collection and confluence
interfaces. Whole function paths may use eta before finite literal-lambda beta
readouts; argument computation may use the full eta union.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Whole-function beta squares remain valid with beta-lambda eta throughout
the function path and its guards. The argument may use arbitrary full-eta
computation, with no native evidence at either argument endpoint. -/
theorem proofErase_beta_lambda_eta_function_beta_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D)) (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.lam A b))
    (RF : ScopedCompute (ErasedBetaLambdaEtaUnion D Recovery) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) outF)
    (RX : ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ∃ shared, ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) shared ∧
      Compute (ErasedLevelCore D) (.app outF outX) shared := by
  have E : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) := if_neg hn
  obtain ⟨shared, RL, RR⟩ := proofErase_beta_lambda_eta_union_join
    hs hlevels hcon hD hc hr hΓ (HasType.lam hA hb) (E ▸ RF)
  rw [E] at RL
  obtain ⟨X, y, rfl, _, RB⟩ := RL.level_core_lam_inv
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨stage, RX⟩ := RX.finite_stage (Stages := ErasedEtaExpansionStage D)
    (fun {n m} hle {Δ a b} H => erased_eta_expansion_stage_mono hle H)
  have RXB := proofErase_eta_compute_inst_argument heq hs hΓA hb hx RX
  have RB' : Compute (ErasedLevelCore D)
      ((proofErase (A :: Γ) b).inst outX) (y.inst outX) := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
      RB.subst (fun H => erased_level_core_subst H) (σ := ProofShape.Subst.one outX)
  refine ⟨y.inst outX, (RXB.mono (fun H => ⟨stage, H⟩)).trans (RB'.scoped ?_),
    (Compute.app RR .refl).trans (.beta .beta)⟩
  intro Δ a b H
  exact .base ⟨0, .inl H⟩

namespace EnvironmentCore
/-- The augmented actual collection supports the enlarged beta-lambda eta
union, with the full eta union available inside base identity guards. -/
theorem beta_lambda_eta_union_confluent
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedBetaLambdaEtaUnion definitions (ErasedEtaExpansionUnion definitions))
      (proofEraseCtx Γ) (proofErase Γ e) a)
    (S : ScopedCompute (ErasedBetaLambdaEtaUnion definitions (ErasedEtaExpansionUnion definitions))
      (proofEraseCtx Γ) (proofErase Γ e) b) :
    ComputeJoin (ErasedLevelCore definitions) a b :=
  proofErase_beta_lambda_eta_union_confluent sound (levelCompatible hcon) hcon no_rigid
    (typed_core_confluence hcon) (erased_eta_expansion_union_descent heq sound)
    (erased_eta_expansion_union_descent heq sound) hΓ ht R S

/-- The same augmented collection supports the whole-function beta square
without global quotient registration or native argument coverage. -/
theorem beta_lambda_eta_function_beta_square
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.lam A b))
    (RF : ScopedCompute (ErasedBetaLambdaEtaUnion definitions (ErasedEtaExpansionUnion definitions))
      (proofEraseCtx Γ) (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) outF)
    (RX : ScopedCompute (ErasedEtaExpansionUnion definitions) (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ∃ shared, ScopedCompute (ErasedEtaExpansionUnion definitions) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) shared ∧
      Compute (ErasedLevelCore definitions) (.app outF outX) shared :=
  proofErase_beta_lambda_eta_function_beta_square heq sound (levelCompatible hcon) hcon no_rigid
    (typed_core_confluence hcon) (erased_eta_expansion_union_descent heq sound) hΓ hA hb hx hn RF RX
end EnvironmentCore

omit [Params] in
/-- Every actual well-formed environment with canonical Eq supplies the
enlarged confluence theorem, including its optional quotient and registered
structure equations. No additional declaration assumptions remain. -/
theorem proofErase_environment_beta_lambda_eta_confluence {E : VEnv} (hE : E.WF)
    (heq : E.HasCanonicalEq) (U : Nat) :
    letI := hE.params U
    ∀ {Γ e T a b}, OnCtx Γ (E.IsType U) → E.HasType U Γ e T →
      ScopedCompute (ErasedBetaLambdaEtaUnion EnvironmentCore.definitions
        (ErasedEtaExpansionUnion EnvironmentCore.definitions)) (proofEraseCtx Γ) (proofErase Γ e) a →
      ScopedCompute (ErasedBetaLambdaEtaUnion EnvironmentCore.definitions
        (ErasedEtaExpansionUnion EnvironmentCore.definitions)) (proofEraseCtx Γ) (proofErase Γ e) b →
      ComputeJoin (ErasedLevelCore EnvironmentCore.definitions) a b := by
  letI := hE.params U
  intro Γ e T a b hΓ ht R S
  exact EnvironmentCore.beta_lambda_eta_union_confluent heq (fun H => H) hΓ ht R S

end Lean4Lean.VEnv.Strengthening
