import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaLambdaEtaCoreJoin

/-! # Nested eta on sources exposed by literal-lambda beta wrappers

Every native guard may use all preceding stages. Eta sources include literal
lambdas and finite beta-lambda readouts. All typed paths still have level-core
common reducts, so arbitrary nesting needs no native-image coverage assumption.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Native eta may precede a finite beta-lambda readout. The independent
base identity guards are unchanged, and new eta guards use preceding stages. -/
def ErasedBetaLambdaEtaStage (D : Definitions)
    (Recovery : List ProofShape → ProofShape → ProofShape → Prop) :
    Nat → List ProofShape → ProofShape → ProofShape → Prop
  | 0 => ErasedLevelCoreExpansion D Recovery
  | n+1 => fun Δ a b => ErasedBetaLambdaEtaStage D Recovery n Δ a b ∨
      (∃ A body, BetaLambdaReadout a A body) ∧ NativeEtaExpansion (ErasedBetaLambdaEtaStage D Recovery n) Δ a b

/-- Earlier stages embed at every later index. -/
theorem erased_beta_lambda_eta_stage_mono (hle : n ≤ m)
    (H : ErasedBetaLambdaEtaStage D Recovery n Δ a b) : ErasedBetaLambdaEtaStage D Recovery m Δ a b := by
  induction hle with
  | refl => exact H
  | step _ ih => exact .inl ih

/-- Source-typed replay needs no assumption on the shape of the beta readout. -/
theorem erased_beta_lambda_eta_stage_descent (hs : D.Sound env univs)
    (hr : ErasedScopedPrimitiveDescent Recovery) :
    ∀ stage, ErasedScopedPrimitiveDescent (ErasedBetaLambdaEtaStage D Recovery stage) := by
  intro stage
  induction stage with
  | zero => exact erased_level_core_expansion_descent hs hr
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht R
    rcases R with R | ⟨_, R⟩
    · exact ih hΓ hΓ' W ht R
    · exact erased_nativeEtaExpansion_descent ih hΓ hΓ' W ht R

/-- Guard depth induction extends core joins from literal lambdas to finite
beta-lambda readouts. Arguments and exposed bodies need no native certificates. -/
theorem proofErase_beta_lambda_eta_stage_join
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hr : ErasedScopedPrimitiveDescent Recovery) : ∀ stage {Γ e T out},
    OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
    ScopedCompute (ErasedBetaLambdaEtaStage D Recovery stage) (proofEraseCtx Γ) (proofErase Γ e) out →
    ComputeJoin (ErasedLevelCore D) (proofErase Γ e) out := by
  intro stage
  induction stage with
  | zero => exact fun hΓ ht R => proofErase_level_core_expansion_join hs hlevels hcon hc hr hΓ ht R
  | succ stage ih =>
    intro Γ e T out hΓ ht R
    apply proofErase_scoped_compute_core_join (erased_beta_lambda_eta_stage_descent hs hr (stage+1))
      (proofErase_level_core_confluent hs hlevels hcon hc) (R := R) (hΓ := hΓ) (ht := ht) (EΓ := rfl) (Ee := rfl)
    intro Γ e T Δ a b H hΓ ht EΓ Ee
    rcases H with H | ⟨⟨A, body, HB⟩, Hη⟩
    · simpa only [Ee] using ih hΓ ht (by simpa only [EΓ, Ee] using ScopedCompute.base H)
    · have HJ := proofErase_native_eta_beta_lambda_core_join hs hlevels hcon hD hc
        (erased_beta_lambda_eta_stage_descent hs hr stage) (fun hΓ ht R => ih hΓ ht R)
        hΓ ht (Ee ▸ HB) (by simpa only [EΓ, Ee] using Hη)
      simpa only [Ee] using HJ

/-- Finite guard depths may vary along a path. -/
def ErasedBetaLambdaEtaUnion (D : Definitions)
    (Recovery : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  ∃ stage, ErasedBetaLambdaEtaStage D Recovery stage Δ a b

/-- The union retains source-typed descent. -/
theorem erased_beta_lambda_eta_union_descent (hs : D.Sound env univs)
    (hr : ErasedScopedPrimitiveDescent Recovery) :
    ErasedScopedPrimitiveDescent (ErasedBetaLambdaEtaUnion D Recovery) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht ⟨stage, H⟩
  exact erased_beta_lambda_eta_stage_descent hs hr stage hΓ hΓ' W ht H

/-- Every whole typed path, with unbounded finite guard and beta-readout depths,
has a common level-core reduct with its source. -/
theorem proofErase_beta_lambda_eta_union_join
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D)) (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedBetaLambdaEtaUnion D Recovery) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ComputeJoin (ErasedLevelCore D) (proofErase Γ e) out := by
  obtain ⟨stage, R⟩ := R.finite_stage (Stages := ErasedBetaLambdaEtaStage D Recovery)
    (fun {n m} hle {Δ a b} H => erased_beta_lambda_eta_stage_mono hle H)
  exact proofErase_beta_lambda_eta_stage_join hs hlevels hcon hD hc hr stage hΓ ht R

/-- Independent paths and independent identity-guard relations meet in the core. -/
theorem proofErase_beta_lambda_eta_union_confluent
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hr : ErasedScopedPrimitiveDescent Recovery) (hr' : ErasedScopedPrimitiveDescent Recovery')
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedBetaLambdaEtaUnion D Recovery) (proofEraseCtx Γ) (proofErase Γ e) a)
    (S : ScopedCompute (ErasedBetaLambdaEtaUnion D Recovery') (proofEraseCtx Γ) (proofErase Γ e) b) :
    ComputeJoin (ErasedLevelCore D) a b :=
  (proofErase_beta_lambda_eta_union_join hs hlevels hcon hD hc hr hΓ ht R).symm.trans_typed
    (proofErase_level_core_confluent hs hlevels hcon hc) hΓ ht
    (proofErase_beta_lambda_eta_union_join hs hlevels hcon hD hc hr' hΓ ht S)

/-- Actual substitution preserves whole paths up to a core join without any
native recovery hypotheses for the substitution images. -/
theorem proofErase_beta_lambda_eta_union_subst_join
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D)) (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedBetaLambdaEtaUnion D Recovery) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ComputeJoin (ErasedLevelCore D) (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
  have H := (proofErase_beta_lambda_eta_union_join hs hlevels hcon hD hc hr W.wf ht R).subst
    (fun H => erased_level_core_subst H) (σ := τ)
  rwa [← proofErase_subst_with hΓ₀ W ht ES] at H

/-- All former literal-lambda stages embed at the same finite index. -/
theorem erased_lambda_eta_into_beta_lambda_eta : ∀ stage {Δ a b},
    ErasedLambdaEtaStage D Recovery stage Δ a b → ErasedBetaLambdaEtaStage D Recovery stage Δ a b := by
  intro stage
  induction stage with
  | zero => exact id
  | succ stage ih =>
    intro Δ a b H
    rcases H with H | ⟨⟨A, body, rfl⟩, H⟩
    · exact .inl (ih H)
    · exact .inr ⟨⟨A, body, .lam⟩, H.mono ih⟩

/-- The broader shape restriction still uses exactly the existing native eta
primitive, so these stages embed into the full eta union. -/
theorem erased_beta_lambda_eta_stage_into_eta_union
    (hrec : ∀ {Δ a b}, Recovery Δ a b → ErasedEtaExpansionUnion D Δ a b) :
    ∀ stage {Δ a b}, ErasedBetaLambdaEtaStage D Recovery stage Δ a b → ErasedEtaExpansionUnion D Δ a b := by
  intro stage
  induction stage with
  | zero => exact erased_lambda_eta_stage_into_eta_union hrec 0
  | succ stage ih =>
    intro Δ a b H
    rcases H with H | ⟨_, H⟩
    · exact ih H
    · exact erased_eta_expansion_union_eta (H.mono ih)

end Lean4Lean.VEnv.Strengthening
