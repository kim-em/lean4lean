import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSpineEtaResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaEtaBetaSquare

/-! # Native eta versus computation in arbitrary spine arguments

A fixed variable/constant head permits arbitrary lambda-eta computations in
each argument. Recovery is constructed at the computed spine. One stage-one
eta expansion there joins the original long branch by level-core computation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

namespace ProofShape
/-- Computation in the arguments of a fixed variable/constant application
spine. Each argument path may be arbitrary compatible contextual computation. -/
inductive NativeSpineCompute (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) : ProofShape → ProofShape → Prop where
  | bvar : NativeSpineCompute Step Δ (.bvar i) (.bvar i)
  | const : NativeSpineCompute Step Δ (.const c ls) (.const c ls)
  | app : NativeSpineCompute Step Δ f g → ScopedCompute Step Δ a b →
      NativeSpineCompute Step Δ (.app f a) (.app g b)

/-- The explicit spine paths are actual compatible computation paths. -/
theorem NativeSpineCompute.compute (H : NativeSpineCompute Step Δ a b) : ScopedCompute Step Δ a b := by
  induction H with
  | bvar | const => exact .refl
  | app _ RA ih => exact .app ih RA

/-- Successive argument computations remain within the fixed-head relation. -/
theorem NativeSpineCompute.trans (H : NativeSpineCompute Step Δ a b)
    (K : NativeSpineCompute Step Δ b c) : NativeSpineCompute Step Δ a c := by
  induction H generalizing c with
  | bvar => cases K; exact .bvar
  | const => cases K; exact .const
  | app _ RA ih => cases K with | app KF KA => exact .app (ih KF) (RA.trans KA)
end ProofShape

variable [Params]
/-- Typed argument paths with core joins supply the structural spine join.
Typing is needed only at the original source; argument endpoint certificates
and independent typings at the changed spine are not required. -/
theorem proofErase_spine_compute_core_join
    (hjoin : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ e) out → ComputeJoin Core (proofErase Γ e) out)
    (H : NativeSpineCompute Step Δ source target)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source) : NativeSpineJoin Core source target := by
  induction H generalizing e T with
  | bvar => exact .bvar
  | const => exact .const
  | app HF HA ih =>
    obtain ⟨f, a, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
    refine .app (ih hf Ef) ?_
    have HA' := HA
    rw [← EΓ, ← Ea] at HA'
    simpa only [Ea] using hjoin hΓ ha HA'

/-- The eta/argument-computation peak closes without a native certificate
for the computed source or any argument. The original guard and argument paths
may use independent unbounded lambda-eta unions. The computed short branch needs
only stage one, regardless of their finite depths; the original long branch
uses only the level core. The head is not unfolded or beta-contracted. -/
theorem proofErase_spine_lambda_eta_square
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hr : ErasedScopedPrimitiveDescent Recovery) (ha : ErasedScopedPrimitiveDescent Arguments)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (R : NativeEtaExpansion (ErasedLambdaEtaUnion D Recovery)
      (proofEraseCtx Γ) (proofErase Γ e) expanded)
    (H : NativeSpineCompute (ErasedLambdaEtaUnion D Arguments)
      (proofEraseCtx Γ) (proofErase Γ e) target) :
    ∃ shared, Compute (ErasedLevelCore D) expanded shared ∧
      ScopedCompute (ErasedEtaExpansionStage D 1) (proofEraseCtx Γ) target shared := by
  have HJ := proofErase_spine_compute_core_join
    (fun hΓ ht R => proofErase_lambda_eta_union_join hs hlevels hcon hc ha hΓ ht R)
    H hΓ he rfl rfl
  obtain ⟨expanded', RE, shared, RL, RR⟩ := proofErase_spine_native_eta_residual
    (erased_lambda_eta_union_descent hs hr) (erased_level_core_descent hs)
    (proofErase_level_core_confluent hs hlevels hcon hc)
    (fun H => erased_level_core_no_pi H) (fun H => erased_level_core_subst H)
    (fun hΓ ht R => proofErase_lambda_eta_union_join hs hlevels hcon hc hr hΓ ht R) hΓ he HJ R
  refine ⟨shared, RL, (ScopedCompute.base ?_).trans (RR.scoped (fun H => .base (.inl (.inl H))))⟩
  exact .inr (.inr (.inr (.inr (RE.mono (fun H => .inl H)))))

/-- The source-changing eta square also absorbs arbitrary lambda-eta
computation on the original long branch. The computed short branch still
closes at stage one, with no target native recovery assumption. -/
theorem proofErase_spine_lambda_eta_continuation_square
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hr : ErasedScopedPrimitiveDescent Recovery) (ha : ErasedScopedPrimitiveDescent Arguments)
    (hk : ErasedScopedPrimitiveDescent Continue)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (R : NativeEtaExpansion (ErasedLambdaEtaUnion D Recovery)
      (proofEraseCtx Γ) (proofErase Γ e) expanded)
    (H : NativeSpineCompute (ErasedLambdaEtaUnion D Arguments)
      (proofEraseCtx Γ) (proofErase Γ e) target)
    (K : ScopedCompute (ErasedLambdaEtaUnion D Continue) (proofEraseCtx Γ) expanded out) :
    ∃ shared, Compute (ErasedLevelCore D) out shared ∧
      ScopedCompute (ErasedEtaExpansionStage D 1) (proofEraseCtx Γ) target shared := by
  obtain ⟨shared, RL, RT⟩ := proofErase_spine_lambda_eta_square hs hlevels hcon hc hr ha hΓ he R H
  obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize
    (erased_nativeEtaExpansion_descent (erased_lambda_eta_union_descent hs hr))
    hΓ he rfl rfl (.base R)
  have ht : env.HasType univs Γ e' T := HE.hasType.2
  have JK := proofErase_lambda_eta_union_join hs hlevels hcon hc hk hΓ ht (EE ▸ K)
  obtain ⟨final, RO, RS⟩ := JK.symm.trans_typed
    (proofErase_level_core_confluent hs hlevels hcon hc) hΓ ht (.of_compute (EE ▸ RL))
  exact ⟨final, RO, RT.trans (RS.scoped (fun H => .base (.inl (.inl H))))⟩

namespace StoredCore
/-- Stored definitions supply the square with full-eta identity guards and
no additional native image coverage or quotient-registration hypothesis. -/
theorem spine_eta_square
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (R : NativeEtaExpansion (ErasedLambdaEtaUnion (Definitions.ofEnv env univs henv)
        (ErasedEtaExpansionUnion (Definitions.ofEnv env univs henv)))
      (proofEraseCtx Γ) (proofErase Γ e) expanded)
    (H : NativeSpineCompute (ErasedLambdaEtaUnion (Definitions.ofEnv env univs henv)
        (ErasedEtaExpansionUnion (Definitions.ofEnv env univs henv)))
      (proofEraseCtx Γ) (proofErase Γ e) target) :
    ∃ shared, Compute (ErasedLevelCore (Definitions.ofEnv env univs henv)) expanded shared ∧
      ScopedCompute (ErasedEtaExpansionStage (Definitions.ofEnv env univs henv) 1)
        (proofEraseCtx Γ) target shared :=
  proofErase_spine_lambda_eta_square (Definitions.ofEnv_sound henv)
    (Definitions.ofEnv_levelCompatible henv) hcon (typed_core_confluence hcon)
    (erased_eta_expansion_union_descent heq (Definitions.ofEnv_sound henv))
    (erased_eta_expansion_union_descent heq (Definitions.ofEnv_sound henv)) hΓ he R H
end StoredCore

omit [Params] in
/-- Every well-formed canonical-Eq environment supplies the source-changing
neutral eta square, with native recovery required only on the original branch. -/
theorem proofErase_environment_spine_eta_square {E : VEnv} (hE : E.WF)
    (heq : E.HasCanonicalEq) (U : Nat) :
    letI := hE.params U
    ∀ {Γ e T expanded target}, OnCtx Γ (E.IsType U) → E.HasType U Γ e T →
      NativeEtaExpansion (ErasedLambdaEtaUnion (Definitions.ofEnv E U hE)
        (ErasedEtaExpansionUnion (Definitions.ofEnv E U hE)))
        (proofEraseCtx Γ) (proofErase Γ e) expanded →
      NativeSpineCompute (ErasedLambdaEtaUnion (Definitions.ofEnv E U hE)
        (ErasedEtaExpansionUnion (Definitions.ofEnv E U hE)))
        (proofEraseCtx Γ) (proofErase Γ e) target →
      ∃ shared, Compute (ErasedLevelCore (Definitions.ofEnv E U hE)) expanded shared ∧
        ScopedCompute (ErasedEtaExpansionStage (Definitions.ofEnv E U hE) 1)
          (proofEraseCtx Γ) target shared := by
  letI := hE.params U
  intro Γ e T expanded target hΓ he R H
  exact StoredCore.spine_eta_square heq (fun H => H) hΓ he R H

end Lean4Lean.VEnv.Strengthening
