import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEnvironmentCore
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaEtaNativeTransport

/-! # Beta and native-eta transport for the augmented actual environment core

The same concrete collection supports quotient-prefix replay, nested lambda
eta confluence, whole-function beta squares, and native guard transport. There
is no global quotient-registration assumption. Common native image premises
remain explicit, because universal non-eta common coverage has been refuted.
-/
namespace Lean4Lean.VEnv.Strengthening.EnvironmentCore
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- The complete actual environment collection discharges the ordinary confluence and universe
compatibility hypotheses. Base identity guards may use the entire eta union. -/
theorem lambda_eta_union_confluent
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedLambdaEtaUnion definitions
        (ErasedEtaExpansionUnion definitions))
      (proofEraseCtx Γ) (proofErase Γ e) a)
    (S : ScopedCompute (ErasedLambdaEtaUnion definitions
        (ErasedEtaExpansionUnion definitions))
      (proofEraseCtx Γ) (proofErase Γ e) b) :
    ComputeJoin (ErasedLevelCore definitions) a b :=
  proofErase_lambda_eta_union_confluent sound
    (levelCompatible hcon) hcon (typed_core_confluence hcon)
    (erased_eta_expansion_union_descent heq sound)
    (erased_eta_expansion_union_descent heq sound) hΓ ht R S

/-- The whole-function beta square likewise specializes to the actual environment core
with arbitrary full-eta argument paths and full-eta base identity guards. -/
theorem lambda_eta_function_beta_square
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.lam A b))
    (RF : ScopedCompute (ErasedLambdaEtaUnion definitions
        (ErasedEtaExpansionUnion definitions)) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) outF)
    (RX : ScopedCompute (ErasedEtaExpansionUnion definitions)
      (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ∃ shared, ScopedCompute (ErasedEtaExpansionUnion definitions)
        (proofEraseCtx Γ) (proofErase Γ (b.inst x)) shared ∧
      Compute (ErasedLevelCore definitions) (.app outF outX) shared :=
  proofErase_lambda_eta_function_beta_square heq sound
    (levelCompatible hcon) hcon (typed_core_confluence hcon)
    (erased_eta_expansion_union_descent heq sound) hΓ hA hb hx hn RF RX

/-- Native eta with nested lambda-eta guards transports under actual joined
images for the complete environment collection. All declaration interfaces
are proved; only the stated image evidence is supplied by the caller. -/
theorem native_eta_lambda_guard_subst
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (hf : env.HasType univs Γ f T)
    (HI : LevelCoreNative.Images definitions Γ Γ₀ τ)
    (R : NativeEtaExpansion (ErasedLambdaEtaUnion definitions (ErasedEtaExpansionUnion definitions))
      (proofEraseCtx Γ) (proofErase Γ f) out) :
    ∃ shared, ScopedCompute (ErasedEtaExpansionUnion definitions) (proofEraseCtx Γ₀)
        ((proofErase Γ f).subst τ) shared ∧
      ScopedCompute (ErasedEtaExpansionUnion definitions) (proofEraseCtx Γ₀)
        (out.subst τ) shared :=
  LevelCoreNative.native_eta_lambda_guard_subst heq sound (levelCompatible hcon) no_rigid
    (typed_core_confluence hcon) hcon (erased_eta_expansion_union_descent heq sound) hΓ₀ W ES hf HI R


/-- First-stage singleton/Eq body computation meets arbitrary full-eta
argument computation in the same augmented environment core. The original
argument may use nested lambda eta for recovery; its computed endpoint
requires no native certificate. -/
theorem stage_one_body_eta_argument_square
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (RN : ScopedTypeRecovery (ErasedLambdaEtaUnion definitions (ErasedEtaExpansionUnion definitions))
      (proofEraseCtx Γ) (proofErase Γ x) native)
    (HJ : ComputeJoin (ErasedLevelCore definitions) (proofErase Γ A) native)
    (RB : ScopedCompute (ErasedLevelRecoveredStage definitions 1) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) outB)
    (RX : ScopedCompute (ErasedEtaExpansionUnion definitions) (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ScopedCompute (ErasedEtaExpansionUnion definitions) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (outB.inst outX) :=
  LevelCoreNative.stage_one_body_eta_argument_square heq sound (levelCompatible hcon) no_rigid
    (typed_core_confluence hcon) hcon (erased_eta_expansion_union_descent heq sound) hΓA hb hx RN HJ RB RX

end Lean4Lean.VEnv.Strengthening.EnvironmentCore
