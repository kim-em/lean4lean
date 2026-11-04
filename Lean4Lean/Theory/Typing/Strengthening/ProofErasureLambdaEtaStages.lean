import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaEtaCoreJoin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreExpansion

/-! # Arbitrarily nested native eta on literal lambdas

Ordinary computation, universe conversion and controlled beta expansion form
the base. Each next stage admits native eta on literal lambda sources using
the entire preceding stage for its type guard. Typed paths at every finite
depth have common level-core reducts. Eta on neutral sources is not included.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- The next eta layer requires a literal lambda source. Its type guard may
use all earlier layers, including computation inside dependent annotations.
Identity guards at the base use the independent Recovery relation. -/
def ErasedLambdaEtaStage (D : Definitions)
    (Recovery : List ProofShape → ProofShape → ProofShape → Prop) :
    Nat → List ProofShape → ProofShape → ProofShape → Prop
  | 0 => ErasedLevelCoreExpansion D Recovery
  | n+1 => fun Δ a b => ErasedLambdaEtaStage D Recovery n Δ a b ∨
      (∃ A body, a = .lam A body) ∧ NativeEtaExpansion (ErasedLambdaEtaStage D Recovery n) Δ a b

/-- Earlier layers embed without changing endpoints or contexts. -/
theorem erased_lambda_eta_stage_mono (hle : n ≤ m)
    (H : ErasedLambdaEtaStage D Recovery n Δ a b) : ErasedLambdaEtaStage D Recovery m Δ a b := by
  induction hle with
  | refl => exact H
  | step _ ih => exact .inl ih

/-- Every stage retains ordinary source-typed descent. The source-shape
restriction is unnecessary for replay; it is used only for core joining. -/
theorem erased_lambda_eta_stage_descent (hs : D.Sound env univs)
    (hr : ErasedScopedPrimitiveDescent Recovery) :
    ∀ stage, ErasedScopedPrimitiveDescent (ErasedLambdaEtaStage D Recovery stage) := by
  intro stage
  induction stage with
  | zero => exact erased_level_core_expansion_descent hs hr
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht R
    rcases R with R | ⟨_, R⟩
    · exact ih hΓ hΓ' W ht R
    · exact erased_nativeEtaExpansion_descent ih hΓ hΓ' W ht R

/-- Neither ordinary nor universe primitives consume a Pi head. -/
theorem erased_level_core_no_pi (H : ErasedLevelCore D (.forallE A B) out) : False := by
  rcases H with H | H
  · exact (erased_iota_primitive_head H).elim
  · cases H

/-- All typed paths at every finite lambda-eta guard depth have a common
level-core reduct. The induction follows the native guard depth; no native
image coverage, normalization, or source-relation confluence is assumed. -/
theorem proofErase_lambda_eta_stage_join
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hr : ErasedScopedPrimitiveDescent Recovery) : ∀ stage {Γ e T out},
    OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
    ScopedCompute (ErasedLambdaEtaStage D Recovery stage) (proofEraseCtx Γ) (proofErase Γ e) out →
    ComputeJoin (ErasedLevelCore D) (proofErase Γ e) out := by
  intro stage
  induction stage with
  | zero => exact fun hΓ ht R => proofErase_level_core_expansion_join hs hlevels hcon hc hr hΓ ht R
  | succ stage ih =>
    intro Γ e T out hΓ ht R
    apply proofErase_scoped_compute_core_join (erased_lambda_eta_stage_descent hs hr (stage+1))
      (proofErase_level_core_confluent hs hlevels hcon hc) (R := R) (hΓ := hΓ) (ht := ht) (EΓ := rfl) (Ee := rfl)
    intro Γ e T Δ a b H hΓ ht EΓ Ee
    rcases H with H | ⟨⟨A, body, rfl⟩, Hη⟩
    · simpa only [Ee] using ih hΓ ht (by simpa only [EΓ, Ee] using ScopedCompute.base H)
    · obtain ⟨A', b', rfl, hn, EA, Eb⟩ := erase_lam_inv Ee
      obtain ⟨⟨_, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
      have HJ := proofErase_native_eta_lambda_core_join
        (erased_lambda_eta_stage_descent hs hr stage) (fun hΓ ht R => ih hΓ ht R)
        (fun H => erased_level_core_no_pi H) hΓ hA hb hn
        (by simpa only [EΓ, Ee] using Hη)
      simpa only [Ee] using HJ

/-- Finite lambda-eta depth may vary throughout a computation. -/
def ErasedLambdaEtaUnion (D : Definitions)
    (Recovery : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  ∃ stage, ErasedLambdaEtaStage D Recovery stage Δ a b

/-- The union retains source-typed replay at the original actual type. -/
theorem erased_lambda_eta_union_descent (hs : D.Sound env univs)
    (hr : ErasedScopedPrimitiveDescent Recovery) :
    ErasedScopedPrimitiveDescent (ErasedLambdaEtaUnion D Recovery) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht ⟨stage, H⟩
  exact erased_lambda_eta_stage_descent hs hr stage hΓ hΓ' W ht H

/-- Arbitrary finite interleavings of all lambda-eta stages remain core
joinable, with no common bound supplied by the caller. -/
theorem proofErase_lambda_eta_union_join
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedLambdaEtaUnion D Recovery) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ComputeJoin (ErasedLevelCore D) (proofErase Γ e) out := by
  obtain ⟨stage, R⟩ := R.finite_stage (Stages := ErasedLambdaEtaStage D Recovery)
    (fun {n m} hle {Δ a b} H => erased_lambda_eta_stage_mono hle H)
  exact proofErase_lambda_eta_stage_join hs hlevels hcon hc hr stage hΓ ht R

/-- Two arbitrary paths in the union meet using only level-core computation.
Their identity-guard relations may differ and need not themselves be confluent. -/
theorem proofErase_lambda_eta_union_confluent
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hr : ErasedScopedPrimitiveDescent Recovery) (hr' : ErasedScopedPrimitiveDescent Recovery')
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedLambdaEtaUnion D Recovery) (proofEraseCtx Γ) (proofErase Γ e) a)
    (S : ScopedCompute (ErasedLambdaEtaUnion D Recovery') (proofEraseCtx Γ) (proofErase Γ e) b) :
    ComputeJoin (ErasedLevelCore D) a b :=
  (proofErase_lambda_eta_union_join hs hlevels hcon hc hr hΓ ht R).symm.trans_typed
    (proofErase_level_core_confluent hs hlevels hcon hc) hΓ ht
    (proofErase_lambda_eta_union_join hs hlevels hcon hc hr' hΓ ht S)

/-- Ordinary actual substitution preserves a whole lambda-eta path up to
a common level-core reduct. No native evidence for any image is required. -/
theorem proofErase_lambda_eta_union_subst_join
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedLambdaEtaUnion D Recovery) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ComputeJoin (ErasedLevelCore D) (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
  have H := (proofErase_lambda_eta_union_join hs hlevels hcon hc hr W.wf ht R).subst
    (fun H => erased_level_core_subst H) (σ := τ)
  rwa [← proofErase_subst_with hΓ₀ W ht ES] at H

/-- These layers are genuine subrelations of the full native-eta union when
the base identity guards use a subrelation of that union. The source-lambda
restriction only narrows the existing eta primitive; it adds no new rule. -/
theorem erased_lambda_eta_stage_into_eta_union
    (hrec : ∀ {Δ a b}, Recovery Δ a b → ErasedEtaExpansionUnion D Δ a b) :
    ∀ stage {Δ a b}, ErasedLambdaEtaStage D Recovery stage Δ a b → ErasedEtaExpansionUnion D Δ a b := by
  intro stage
  induction stage with
  | zero =>
    intro Δ a b H
    rcases H with (H | H) | H | H
    · exact ⟨0, .inl (.inl H)⟩
    · exact ⟨0, .inl (.inr H)⟩
    · exact ⟨0, .inr H⟩
    · cases H with
      | intro RN =>
        obtain ⟨n, RN⟩ := (RN.mono hrec).finite_stage (Stages := ErasedEtaExpansionStage D)
          (fun {n m} hle {Δ a b} H => erased_eta_expansion_stage_mono hle H)
        exact ⟨n+1, .inr (.inr (.inr (.inl (.intro RN))))⟩
  | succ stage ih =>
    intro Δ a b H
    rcases H with H | ⟨_, H⟩
    · exact ih H
    · exact erased_eta_expansion_union_eta (H.mono ih)

/-- No uniform finite eta-stage bound is needed to embed the union. -/
theorem erased_lambda_eta_union_into_eta_union
    (hrec : ∀ {Δ a b}, Recovery Δ a b → ErasedEtaExpansionUnion D Δ a b)
    (H : ErasedLambdaEtaUnion D Recovery Δ a b) : ErasedEtaExpansionUnion D Δ a b := by
  obtain ⟨stage, H⟩ := H
  exact erased_lambda_eta_stage_into_eta_union hrec stage H

end Lean4Lean.VEnv.Strengthening
