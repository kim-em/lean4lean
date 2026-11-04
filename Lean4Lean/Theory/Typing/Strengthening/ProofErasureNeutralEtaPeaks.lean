import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSpineEtaDiamond
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaEtaBetaSquare

/-! # Neutral eta peaks followed by independent lambda-eta paths

The short neutral source need not core-join its eta expansion. Instead, the
two long forms core-join each other, and typed replay composes that diamond
with computations on either long branch. Inner guard and continuation paths
allow arbitrarily nested eta on literal lambdas.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Two eta expansions of a typed variable/constant application spine meet
in the level core. Their native guards may use independent lambda-eta unions.
Arguments need no native recovery, purity, or normalization hypothesis. -/
theorem proofErase_spine_lambda_eta_guard_diamond
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hr : ErasedScopedPrimitiveDescent Recovery) (hr' : ErasedScopedPrimitiveDescent Recovery')
    (H : NativeEtaSpine (proofErase Γ e))
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (RL : NativeEtaExpansion (ErasedLambdaEtaUnion D Recovery) (proofEraseCtx Γ) (proofErase Γ e) a)
    (RR : NativeEtaExpansion (ErasedLambdaEtaUnion D Recovery') (proofEraseCtx Γ) (proofErase Γ e) b) :
    ComputeJoin (ErasedLevelCore D) a b :=
  proofErase_spine_native_eta_diamond (erased_lambda_eta_union_descent hs hr)
    (erased_lambda_eta_union_descent hs hr') (proofErase_level_core_confluent hs hlevels hcon hc)
    (fun H => erased_level_core_no_pi H) (fun H => erased_level_core_subst H)
    (fun hΓ ht R => proofErase_lambda_eta_union_join hs hlevels hcon hc hr hΓ ht R)
    (fun hΓ ht R => proofErase_lambda_eta_union_join hs hlevels hcon hc hr' hΓ ht R)
    H hΓ he RL RR

/-- A neutral eta peak remains joined after independent lambda-eta union
computations on both long branches. All four base identity guard relations
may differ; each needs only source descent. This is a root peak theorem,
not closure under further neutral eta or arbitrary singleton-prefix steps. -/
theorem proofErase_spine_lambda_eta_peak_join
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hr : ErasedScopedPrimitiveDescent Recovery) (hr' : ErasedScopedPrimitiveDescent Recovery')
    (hk : ErasedScopedPrimitiveDescent Continue) (hk' : ErasedScopedPrimitiveDescent Continue')
    (H : NativeEtaSpine (proofErase Γ e))
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (RL : NativeEtaExpansion (ErasedLambdaEtaUnion D Recovery) (proofEraseCtx Γ) (proofErase Γ e) a)
    (RR : NativeEtaExpansion (ErasedLambdaEtaUnion D Recovery') (proofEraseCtx Γ) (proofErase Γ e) b)
    (RA : ScopedCompute (ErasedLambdaEtaUnion D Continue) (proofEraseCtx Γ) a outA)
    (RB : ScopedCompute (ErasedLambdaEtaUnion D Continue') (proofEraseCtx Γ) b outB) :
    ComputeJoin (ErasedLevelCore D) outA outB := by
  have HJ := proofErase_spine_lambda_eta_guard_diamond hs hlevels hcon hc hr hr' H hΓ he RL RR
  obtain ⟨eA, hA, EA⟩ := proofErase_scoped_compute_realize
    (erased_nativeEtaExpansion_descent (erased_lambda_eta_union_descent hs hr))
    hΓ he rfl rfl (.base RL)
  obtain ⟨eB, hB, EB⟩ := proofErase_scoped_compute_realize
    (erased_nativeEtaExpansion_descent (erased_lambda_eta_union_descent hs hr'))
    hΓ he rfl rfl (.base RR)
  have htA : env.HasType univs Γ eA T := hA.hasType.2
  have htB : env.HasType univs Γ eB T := hB.hasType.2
  rw [← EA, ← EB] at HJ
  have JA := proofErase_lambda_eta_union_join hs hlevels hcon hc hk hΓ htA (EA ▸ RA)
  have JB := proofErase_lambda_eta_union_join hs hlevels hcon hc hk' hΓ htB (EB ▸ RB)
  have hc' : TypedCoreConfluence (ErasedLevelCore D) :=
    proofErase_level_core_confluent hs hlevels hcon hc
  exact (JA.symm.trans_typed hc' hΓ htA HJ).trans_typed hc' hΓ htB JB

namespace StoredCore
/-- Stored definitions discharge the core laws. Every base identity guard
may use the full eta expansion union, while the inner eta roots and the
post-peak computations remain the literal-lambda eta union. -/
theorem neutral_eta_peak_join
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (H : NativeEtaSpine (proofErase Γ e))
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (RL : NativeEtaExpansion (ErasedLambdaEtaUnion (Definitions.ofEnv env univs henv)
        (ErasedEtaExpansionUnion (Definitions.ofEnv env univs henv)))
      (proofEraseCtx Γ) (proofErase Γ e) a)
    (RR : NativeEtaExpansion (ErasedLambdaEtaUnion (Definitions.ofEnv env univs henv)
        (ErasedEtaExpansionUnion (Definitions.ofEnv env univs henv)))
      (proofEraseCtx Γ) (proofErase Γ e) b)
    (RA : ScopedCompute (ErasedLambdaEtaUnion (Definitions.ofEnv env univs henv)
        (ErasedEtaExpansionUnion (Definitions.ofEnv env univs henv))) (proofEraseCtx Γ) a outA)
    (RB : ScopedCompute (ErasedLambdaEtaUnion (Definitions.ofEnv env univs henv)
        (ErasedEtaExpansionUnion (Definitions.ofEnv env univs henv))) (proofEraseCtx Γ) b outB) :
    ComputeJoin (ErasedLevelCore (Definitions.ofEnv env univs henv)) outA outB :=
  proofErase_spine_lambda_eta_peak_join (Definitions.ofEnv_sound henv)
    (Definitions.ofEnv_levelCompatible henv) hcon (typed_core_confluence hcon)
    (erased_eta_expansion_union_descent heq (Definitions.ofEnv_sound henv))
    (erased_eta_expansion_union_descent heq (Definitions.ofEnv_sound henv))
    (erased_eta_expansion_union_descent heq (Definitions.ofEnv_sound henv))
    (erased_eta_expansion_union_descent heq (Definitions.ofEnv_sound henv)) H hΓ he RL RR RA RB
end StoredCore

omit [Params] in
/-- Actual well-formed environments with canonical Eq satisfy the neutral
spine peak theorem without additional quotient-registration or core axioms. -/
theorem proofErase_environment_neutral_eta_peak_join {E : VEnv} (hE : E.WF)
    (heq : E.HasCanonicalEq) (U : Nat) :
    letI := hE.params U
    ∀ {Γ e T a b outA outB}, OnCtx Γ (E.IsType U) → E.HasType U Γ e T →
      NativeEtaSpine (proofErase Γ e) →
      NativeEtaExpansion (ErasedLambdaEtaUnion (Definitions.ofEnv E U hE)
        (ErasedEtaExpansionUnion (Definitions.ofEnv E U hE))) (proofEraseCtx Γ) (proofErase Γ e) a →
      NativeEtaExpansion (ErasedLambdaEtaUnion (Definitions.ofEnv E U hE)
        (ErasedEtaExpansionUnion (Definitions.ofEnv E U hE))) (proofEraseCtx Γ) (proofErase Γ e) b →
      ScopedCompute (ErasedLambdaEtaUnion (Definitions.ofEnv E U hE)
        (ErasedEtaExpansionUnion (Definitions.ofEnv E U hE))) (proofEraseCtx Γ) a outA →
      ScopedCompute (ErasedLambdaEtaUnion (Definitions.ofEnv E U hE)
        (ErasedEtaExpansionUnion (Definitions.ofEnv E U hE))) (proofEraseCtx Γ) b outB →
      ComputeJoin (ErasedLevelCore (Definitions.ofEnv E U hE)) outA outB := by
  letI := hE.params U
  intro Γ e T a b outA outB hΓ he H RL RR RA RB
  exact StoredCore.neutral_eta_peak_join heq (fun H => H) H hΓ he RL RR RA RB

end Lean4Lean.VEnv.Strengthening
