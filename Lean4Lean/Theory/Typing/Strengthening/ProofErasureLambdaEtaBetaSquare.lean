import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaEtaStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreBetaSquare
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaBetaSquares

/-! # Whole-function beta squares with nested lambda eta

The function path may mix ordinary and universe computation, controlled beta
expansion and arbitrarily nested native eta on literal lambdas. Its level-core
readout substitutes freely. The argument may compute in the full eta union;
neither its original nor its computed value needs native recovery.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- A variable and its native eta expansion cannot share a level-core
reduct. Thus the core-join method genuinely excludes neutral eta; extending
the stage grammar to those roots requires a different target invariant. -/
theorem native_eta_variable_not_level_core_join
    (R : NativeEtaExpansion Recovery Δ (.bvar i) out) :
    ¬ ComputeJoin (ErasedLevelCore D) (.bvar i) out := by
  rintro ⟨shared, RL, RR⟩
  have HN : NormalSyntax (ErasedLevelCore D) (.bvar i) := by
    refine ⟨?_, trivial⟩
    intro out H
    rcases H with H | H
    · exact (erased_iota_primitive_head H).elim
    · cases H
  have E := HN.fixed RL
  rw [E] at RR
  cases R
  obtain ⟨_, _, E, _, _⟩ := RR.level_core_lam_inv
  cases E

/-- A whole lambda-eta path from a retained lambda has a level-core readout
with separate original-domain and original-body histories. -/
theorem proofErase_lambda_eta_union_lambda_readout
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D)) (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hn : ¬ IsProof Γ (.lam A b))
    (RF : ScopedCompute (ErasedLambdaEtaUnion D Recovery) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) outF) :
    ∃ X y, Compute (ErasedLevelCore D) outF (.lam X y) ∧
      Compute (ErasedLevelCore D) (proofErase Γ A) X ∧
      Compute (ErasedLevelCore D) (proofErase (A :: Γ) b) y := by
  have E : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) := if_neg hn
  obtain ⟨shared, RL, RR⟩ := proofErase_lambda_eta_union_join hs hlevels hcon hc hr hΓ
    (HasType.lam hA hb) (E ▸ RF)
  rw [E] at RL
  obtain ⟨X, y, rfl, RA, RB⟩ := RL.level_core_lam_inv
  exact ⟨X, y, RR, RA, RB⟩

/-- Whole function computation, including nested lambda eta, and arbitrary
full-eta argument computation meet the original head-beta contractum. The
computed-application branch uses only level-core steps. No argument recovery
or image-coverage premise occurs at either endpoint. -/
theorem proofErase_lambda_eta_function_beta_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D)) (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.lam A b))
    (RF : ScopedCompute (ErasedLambdaEtaUnion D Recovery) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) outF)
    (RX : ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ∃ shared, ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) shared ∧
      Compute (ErasedLevelCore D) (.app outF outX) shared := by
  obtain ⟨X, y, RF', _, RB⟩ := proofErase_lambda_eta_union_lambda_readout
    hs hlevels hcon hc hr hΓ hA hb hn RF
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨stage, RX⟩ := RX.finite_stage (Stages := ErasedEtaExpansionStage D)
    (fun {n m} hle {Δ a b} H => erased_eta_expansion_stage_mono hle H)
  have RXB := proofErase_eta_compute_inst_argument heq hs hΓA hb hx RX
  have RB' : Compute (ErasedLevelCore D)
      ((proofErase (A :: Γ) b).inst outX) (y.inst outX) := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
      RB.subst (fun H => erased_level_core_subst H) (σ := ProofShape.Subst.one outX)
  refine ⟨y.inst outX, (RXB.mono (fun H => ⟨stage, H⟩)).trans (RB'.scoped ?_),
    (Compute.app RF' .refl).trans (.beta .beta)⟩
  intro Δ a b H
  exact .base ⟨0, .inl H⟩

namespace StoredCore
/-- Stored definitions discharge the ordinary confluence and universe
compatibility hypotheses. Base identity guards may use the entire eta union. -/
theorem lambda_eta_union_confluent
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedLambdaEtaUnion (Definitions.ofEnv env univs henv)
        (ErasedEtaExpansionUnion (Definitions.ofEnv env univs henv)))
      (proofEraseCtx Γ) (proofErase Γ e) a)
    (S : ScopedCompute (ErasedLambdaEtaUnion (Definitions.ofEnv env univs henv)
        (ErasedEtaExpansionUnion (Definitions.ofEnv env univs henv)))
      (proofEraseCtx Γ) (proofErase Γ e) b) :
    ComputeJoin (ErasedLevelCore (Definitions.ofEnv env univs henv)) a b :=
  proofErase_lambda_eta_union_confluent (Definitions.ofEnv_sound henv)
    (Definitions.ofEnv_levelCompatible henv) hcon (typed_core_confluence hcon)
    (erased_eta_expansion_union_descent heq (Definitions.ofEnv_sound henv))
    (erased_eta_expansion_union_descent heq (Definitions.ofEnv_sound henv)) hΓ ht R S

/-- The whole-function beta square likewise specializes to stored definitions
with arbitrary full-eta argument paths and full-eta base identity guards. -/
theorem lambda_eta_function_beta_square
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.lam A b))
    (RF : ScopedCompute (ErasedLambdaEtaUnion (Definitions.ofEnv env univs henv)
        (ErasedEtaExpansionUnion (Definitions.ofEnv env univs henv))) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) outF)
    (RX : ScopedCompute (ErasedEtaExpansionUnion (Definitions.ofEnv env univs henv))
      (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ∃ shared, ScopedCompute (ErasedEtaExpansionUnion (Definitions.ofEnv env univs henv))
        (proofEraseCtx Γ) (proofErase Γ (b.inst x)) shared ∧
      Compute (ErasedLevelCore (Definitions.ofEnv env univs henv)) (.app outF outX) shared :=
  proofErase_lambda_eta_function_beta_square heq (Definitions.ofEnv_sound henv)
    (Definitions.ofEnv_levelCompatible henv) hcon (typed_core_confluence hcon)
    (erased_eta_expansion_union_descent heq (Definitions.ofEnv_sound henv)) hΓ hA hb hx hn RF RX
end StoredCore

omit [Params] in
/-- Every actual well-formed environment with canonical Eq supplies the
concrete lambda-eta confluence instance. No additional quotient registration,
definition compatibility, or abstract pattern correctness premise remains. -/
theorem proofErase_environment_lambda_eta_confluence {E : VEnv} (hE : E.WF)
    (heq : E.HasCanonicalEq) (U : Nat) :
    letI := hE.params U
    ∀ {Γ e T a b}, OnCtx Γ (E.IsType U) → E.HasType U Γ e T →
      ScopedCompute (ErasedLambdaEtaUnion (Definitions.ofEnv E U hE)
        (ErasedEtaExpansionUnion (Definitions.ofEnv E U hE))) (proofEraseCtx Γ) (proofErase Γ e) a →
      ScopedCompute (ErasedLambdaEtaUnion (Definitions.ofEnv E U hE)
        (ErasedEtaExpansionUnion (Definitions.ofEnv E U hE))) (proofEraseCtx Γ) (proofErase Γ e) b →
      ComputeJoin (ErasedLevelCore (Definitions.ofEnv E U hE)) a b := by
  letI := hE.params U
  intro Γ e T a b hΓ ht R S
  exact StoredCore.lambda_eta_union_confluent heq (fun H => H) hΓ ht R S

end Lean4Lean.VEnv.Strengthening
