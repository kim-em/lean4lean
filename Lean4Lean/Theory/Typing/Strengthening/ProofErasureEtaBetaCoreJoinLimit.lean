import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaBetaPiBoundary

/-! # Why beta-lambda core-join stages cannot cover all head-beta eta peaks

Native Pi evidence on both sides is insufficient. The typed identity-wrapper
example cannot be joined by any finite depth of the core-joinable beta-lambda
eta union, although it has an explicit stage-one join in the full eta system.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- If typed paths of two relations admit core joins, a common endpoint of
those paths forces a core join of their sources. Replay of the left path gives
the actual typed middle needed to compose joins. -/
theorem proofErase_core_join_of_scoped_common
    (hleft : ErasedScopedPrimitiveDescent Left) (hc : TypedCoreConfluence Core)
    (hlj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Left (proofEraseCtx Γ) (proofErase Γ e) out → ComputeJoin Core (proofErase Γ e) out)
    (hrj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Right (proofEraseCtx Γ) (proofErase Γ e) out → ComputeJoin Core (proofErase Γ e) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T) (hf : env.HasType univs Γ f U)
    (RE : ScopedCompute Left (proofEraseCtx Γ) (proofErase Γ e) shared)
    (RF : ScopedCompute Right (proofEraseCtx Γ) (proofErase Γ f) shared) :
    ComputeJoin Core (proofErase Γ e) (proofErase Γ f) := by
  obtain ⟨s, HS, ES⟩ := proofErase_scoped_compute_realize hleft hΓ he rfl rfl RE
  have JL := hlj hΓ he RE
  have JR := hrj hΓ hf RF
  rw [← ES] at JL JR
  exact JL.trans_typed hc hΓ HS.hasType.2 JR.symm

/-- Arbitrary beta exposure of a lambda cannot replace the explicit readout
restriction in the core-join invariant. Even native Pi recovery at both original
beta endpoints does not suffice: no finite beta-lambda eta stages join this peak.
The full eta system joins it at stage one, so the obstruction is to the invariant
and fragment, not to full eta confluence or declarative strengthening. -/
theorem beta_lambda_eta_union_misses_typed_beta_peak
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D)) (hr : ErasedScopedPrimitiveDescent Recovery) :
    ∃ Γ e T expanded, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ e T ∧
      (∃ A b, BetaRed (proofErase Γ e) (.lam A b)) ∧
      NativeEtaExpansion (ErasedEtaExpansionStage D 0) (proofEraseCtx Γ) (proofErase Γ e) expanded ∧
      (∀ shared, ScopedCompute (ErasedBetaLambdaEtaUnion D Recovery) (proofEraseCtx Γ)
          (proofErase Γ e) shared →
        ¬ ScopedCompute (ErasedBetaLambdaEtaUnion D Recovery) (proofEraseCtx Γ) expanded shared) ∧
      ∃ shared, ScopedCompute (ErasedEtaExpansionStage D 1) (proofEraseCtx Γ) (proofErase Γ e) shared ∧
        BetaRed expanded shared := by
  obtain ⟨Γ, e, f, T, A, b, expanded, _, hΓ, he, _, _, Ef, RB, _, _, Rη, Hno, Hrepair⟩ :=
    EtaBetaPiBoundary.typed_pi_beta_core_failure_and_eta_repair D
  refine ⟨Γ, e, T, expanded, hΓ, he, ⟨A, b, by simpa only [Ef] using RB⟩, Rη, ?_, ?_⟩
  · intro shared RE RF
    obtain ⟨g, HG, EG⟩ := proofErase_scoped_compute_realize
      (erased_nativeEtaExpansion_descent (erased_eta_expansion_stage_descent heq hs 0))
      hΓ he rfl rfl (.base Rη)
    have HG' : env.HasType univs Γ g T := HG.hasType.2
    have HJ := proofErase_core_join_of_scoped_common
      (erased_beta_lambda_eta_union_descent hs hr) (proofErase_level_core_confluent hs hlevels hcon hc)
      (fun hΓ ht R => proofErase_beta_lambda_eta_union_join hs hlevels hcon hD hc hr hΓ ht R)
      (fun hΓ ht R => proofErase_beta_lambda_eta_union_join hs hlevels hcon hD hc hr hΓ ht R)
      hΓ he HG' RE (EG ▸ RF)
    exact Hno (by simpa only [EG] using HJ)
  · obtain ⟨shared, RF, RL⟩ := Hrepair
    exact ⟨shared, (ScopedCompute.beta RB).trans RF, RL⟩

omit [Params] in
/-- The limitation and its stage-one repair hold in every actual canonical-Eq
environment for the full augmented core, without additional declarations. -/
theorem proofErase_environment_beta_eta_core_limit {E : VEnv} (hE : E.WF)
    (heq : E.HasCanonicalEq) (U : Nat) :
    letI := hE.params U
    ∃ Γ e T expanded, OnCtx Γ (E.IsType U) ∧ E.HasType U Γ e T ∧
      (∃ A b, BetaRed (proofErase Γ e) (.lam A b)) ∧
      NativeEtaExpansion (ErasedEtaExpansionStage EnvironmentCore.definitions 0)
        (proofEraseCtx Γ) (proofErase Γ e) expanded ∧
      (∀ shared, ScopedCompute (ErasedBetaLambdaEtaUnion EnvironmentCore.definitions
          (ErasedEtaExpansionUnion EnvironmentCore.definitions)) (proofEraseCtx Γ)
          (proofErase Γ e) shared →
        ¬ ScopedCompute (ErasedBetaLambdaEtaUnion EnvironmentCore.definitions
          (ErasedEtaExpansionUnion EnvironmentCore.definitions)) (proofEraseCtx Γ) expanded shared) ∧
      ∃ shared, ScopedCompute (ErasedEtaExpansionStage EnvironmentCore.definitions 1)
          (proofEraseCtx Γ) (proofErase Γ e) shared ∧ BetaRed expanded shared := by
  letI := hE.params U
  exact beta_lambda_eta_union_misses_typed_beta_peak heq EnvironmentCore.sound
    (EnvironmentCore.levelCompatible (fun H => H)) (fun H => H) EnvironmentCore.no_rigid
    (EnvironmentCore.typed_core_confluence (fun H => H))
    (erased_eta_expansion_union_descent heq EnvironmentCore.sound)

end Lean4Lean.VEnv.Strengthening
