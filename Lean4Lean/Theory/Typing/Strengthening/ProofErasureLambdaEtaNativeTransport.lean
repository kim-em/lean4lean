import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaLevelCoreJoinedSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaEtaBetaSquare

/-! # Native transport through nested lambda eta

Literal-lambda eta has a common level-core reduct at every finite guard depth.
Transfer native recovery through those joins, keeping ordinary output residuals
so that dependent Pi and projection heads remain exact. This admits lambda eta
inside native guards; it does not assert neutral-eta core joins or coverage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]
namespace LevelCoreNative

/-- Native recovery with nested literal-lambda eta, ordinary, universe, and
controlled expansion paths collapses to level-core recovery with an ordinary output residual.
The recovery guards themselves may use any descending relation. -/
theorem lambda_eta_recovery
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D)) (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedTypeRecovery (ErasedLambdaEtaUnion D Recovery)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ out', ScopedTypeRecovery (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) (proofErase Γ e) out' ∧
      ProofShape.Compute (ErasedIotaPrimitive D) out out' :=
  recovery_of_compute_join hs hlevels hcon hD hc (erased_lambda_eta_union_descent hs hr)
    (fun hΓ ht R => proofErase_lambda_eta_union_join hs hlevels hcon hc hr hΓ ht R) R hΓ ht rfl rfl

/-- A lambda-eta native output joined to the assigned type supplies a level-core
native ordinary reduct of that assigned type. Both original join branches may
compute, and no exact assigned-type native recovery is required. -/
theorem lambda_eta_recovery_align
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D)) (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedTypeRecovery (ErasedLambdaEtaUnion D Recovery)
      (proofEraseCtx Γ) (proofErase Γ e) out)
    (HJ : ComputeJoin (ErasedLevelCore D) (proofErase Γ T) out) :
    ∃ native, ScopedTypeRecovery (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) (proofErase Γ e) native ∧
      ProofShape.Compute (ErasedIotaPrimitive D) (proofErase Γ T) native := by
  obtain ⟨core, RN, RC⟩ := lambda_eta_recovery hs hlevels hcon hD hc hr hΓ ht R
  obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay
    (erased_lambda_eta_union_descent hs hr) hΓ ht R
  obtain ⟨_, hA⟩ := heA.isType henv hΓ
  have K : ComputeJoin (ErasedLevelCore D) out core :=
    .of_compute (RC.mono (fun H => Or.inl H))
  rw [← EA] at HJ K
  have J := HJ.trans_typed (proofErase_level_core_confluent hs hlevels hcon hc) hΓ hA
    (by simpa only [EA] using K)
  obtain ⟨_, hT⟩ := ht.isType henv hΓ
  exact of_join hs hlevels hcon hΓ hT RN (by simpa only [EA] using J)

/-- Joined substitution images transport a native eta step even when its
selected type is recovered through arbitrarily nested literal-lambda eta.
The eta source itself is arbitrary; only eta inside the guard is restricted. -/
theorem native_eta_lambda_guard_subst
    (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (hf : env.HasType univs Γ f T)
    (HI : Images D Γ Γ₀ τ)
    (R : NativeEtaExpansion (ErasedLambdaEtaUnion D Recovery)
      (proofEraseCtx Γ) (proofErase Γ f) out) :
    ∃ shared, ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ₀)
        ((proofErase Γ f).subst τ) shared ∧
      ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ₀)
        (out.subst τ) shared := by
  cases R with
  | intro RN SD =>
    obtain ⟨native, RI, RP⟩ := lambda_eta_recovery hs hlevels hcon hRigid hc hr W.wf hf RN
    obtain ⟨native', RI', RP'⟩ := recovery_subst hs hlevels hRigid hc hcon RI hΓ₀ W ES hf rfl rfl HI
    rw [← proofErase_subst_with hΓ₀ W hf ES] at RI'
    exact proofErase_native_eta_subst_of_joined_guard heq hs
      (erased_lambda_eta_union_descent hs hr) hΓ₀ W ES hf RN SD
      (RI'.mono (fun H => ⟨0, .inl H⟩))
      (((RP.subst (fun H => erased_iota_primitive_subst H)).trans RP').scoped
        (fun H => .base ⟨0, .inl (.inl H)⟩)) .refl

/-- A whole first-stage singleton/Eq body path transports through an argument
whose native guard admits nested literal-lambda eta. The argument may then
compute through the entire eta union, including neutral eta and higher
singleton stages. Only its original value needs the common native carrier. -/
theorem stage_one_body_eta_argument_square
    (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (RN : ScopedTypeRecovery (ErasedLambdaEtaUnion D Recovery)
      (proofEraseCtx Γ) (proofErase Γ x) native)
    (HJ : ComputeJoin (ErasedLevelCore D) (proofErase Γ A) native)
    (RB : ScopedCompute (ErasedLevelRecoveredStage D 1) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) outB)
    (RX : ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (outB.inst outX) := by
  obtain ⟨native', RN', RC'⟩ := lambda_eta_recovery_align hs hlevels hcon hRigid hc hr hΓA.1 hx RN HJ
  have HI : Images D (A :: Γ) Γ (ProofShape.Subst.one (proofErase Γ x)) := Images.inst RN' RC'
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one x)
      (ProofShape.Subst.one (proofErase Γ x)) := erasedSubstAgreement_one hΓA hx
  have R₁ := stage_one_compute_subst heq hs hlevels hRigid hc hcon RB hΓA hb rfl rfl
    (ImageSubstitution.of_typed hΓA.1 W ES HI)
  rw [← proofErase_subst_with hΓA.1 W hb ES] at R₁
  have R₁' : ScopedCompute (ErasedLevelRecoveredStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (outB.inst (proofErase Γ x)) := by
    simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using R₁
  obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize
    (erased_level_recovered_stage_descent heq hs 1) hΓA hb rfl rfl RB
  obtain ⟨stage, RX⟩ := RX.finite_stage (Stages := ErasedEtaExpansionStage D)
    (fun {n m} hle {Δ a b} H => erased_eta_expansion_stage_mono hle H)
  have R₂ := proofErase_eta_compute_inst_argument heq hs hΓA HB.hasType.2 hx RX
  rw [proofErase_instN hΓA hx Ctx.InstN.zero HB.hasType.2, EB] at R₂
  exact (R₁'.mono (fun H => erased_expansion_into_eta_union
    ⟨1, erased_level_into_expansion_stage 1 H⟩)).trans (R₂.mono (fun H => ⟨stage, H⟩))

end LevelCoreNative
end Lean4Lean.VEnv.Strengthening
