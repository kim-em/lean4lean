import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaOriginTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionLambdaOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageZeroPiReadout

/-! # Exact stage-zero lambda computation readout

Marked payloads retain the original annotation and body computation histories
through arbitrary generated control frames. Context independence at stage zero
keeps those histories in the original scopes without increasing their stage.
Literal lambda endpoints recover the exact components, without beta residuals.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.LambdaOriginObservation
variable [Params] {D : PureObservation.Definitions}

/-- A payload records actual component representatives and computation from
the initial lambda. Its body history stays in the initial binder context. -/
def StageZeroLambdaOrigin (D : PureObservation.Definitions) (Γ : List VExpr)
    (A B : VExpr) (u : VLevel) (X Y : ProofShape) : Prop :=
  ∃ A' B' T, env.IsDefEq univs Γ A A' (.sort u) ∧
    env.HasType univs (A' :: Γ) B' T ∧
    proofErase Γ A' = X ∧ proofErase (A' :: Γ) B' = Y ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) (proofErase Γ A) X ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) B) Y

/-- An initial typed lambda supplies a payload with reflexive component histories. -/
theorem StageZeroLambdaOrigin.refl
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B T) :
    StageZeroLambdaOrigin D Γ A B u (proofErase Γ A) (proofErase (A :: Γ) B) :=
  ⟨A, B, T, hA, hB, rfl, rfl, .refl, .refl⟩

/-- Component computation of a marked lambda lowers through every temporary
prefix, then appends both histories at stage zero. Context independence puts
later body paths in the original binder context directly. -/
theorem stage_zero_lambdaOrigin_componentClosure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    LambdaOriginComponentClosure (ErasedStaticStructureEtaExpansionStage D 0) Γ (StageZeroLambdaOrigin D Γ A B u) := by
  intro Γ' n X Y outX outY hΓ' W HP RX RY
  obtain ⟨A₀, B₀, T, HA₀, hB₀, rfl, rfl, RA₀, RB₀⟩ := HP
  have hA₀ := HA₀.hasType.2
  have hΓA₀ : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA₀⟩
  have hΓA₀' : OnCtx (A₀.liftN n :: Γ') (env.IsType univs) := ⟨hΓ', u, hA₀.weakN henv W⟩
  obtain ⟨A₁, HA₁, RA₁, EA₁⟩ := proofErase_scoped_compute_certificate_descend
    (erased_static_structure_eta_expansion_stage_certificate_descent heq hs 0) hΓ hΓ' W hA₀ rfl RX
  have EΓB : proofEraseCtx (A₀.liftN n :: Γ') =
      (proofErase Γ A₀).liftN n :: proofEraseCtx Γ' := by
    rw [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA₀]
  obtain ⟨B₁, HB₁, RB₁, EB₁⟩ := proofErase_scoped_compute_certificate_descend
    (erased_static_structure_eta_expansion_stage_certificate_descent heq hs 0) hΓA₀ hΓA₀' W.succ hB₀ EΓB RY
  have HC : IsDefEqCtx env univs Γ (A₀ :: Γ) (A₁ :: Γ) := .succ .zero HA₁
  have hB₁ := HB₁.hasType.2.defeqDFC henv HC
  have EB₁' := proofErase_defeqCtx hΓA₀ HC HB₁.hasType.2
  have RPB : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (A :: Γ))
      (proofErase (A₀ :: Γ) B₀) (proofErase (A₀ :: Γ) B₁) :=
    RB₁.recontext_independent (fun H => H)
  rw [EB₁'] at RPB
  refine ⟨proofErase Γ A₁, proofErase (A₁ :: Γ) B₁,
    ⟨A₁, B₁, T, HA₀.trans HA₁, hB₁, rfl, rfl, RA₀.trans RA₁, RB₀.trans RPB⟩, EA₁.symm, ?_⟩
  rw [EB₁'] at EB₁
  exact EB₁.symm

/-- The marked observation survives all stage-zero computation while
retaining exact lower component histories in its payload. -/
theorem proofErase_stage_zero_lambda_observation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b T)
    (hn : ¬ IsProof Γ (.lam A b))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) out) :
    Obs (StageZeroLambdaOrigin D Γ A b u) 0 (fun _ _ => False) out .pi := by
  have E : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) := if_neg hn
  have H : Obs (StageZeroLambdaOrigin D Γ A b u) 0 (fun _ _ => False)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) .pi := by
    simpa only [ProofShape.liftN_zero] using
      (Obs.payload (n := 0) (S := fun _ _ => False) (StageZeroLambdaOrigin.refl hA hb))
  exact proofErase_scoped_compute_lambdaOriginObservation
    (erased_static_structure_eta_expansion_stage_descent heq hs 0)
    (erased_expansion_stage_lambdaOriginObservation 0)
    (stage_zero_lambdaOrigin_componentClosure heq hs hΓ) R hΓ (Ctx.LiftN.zero [])
    (HasType.lam hA hb) rfl E H

/-- Every expanded path from a retained typed lambda has an actual lower
lambda origin. Its annotation and body may both compute arbitrarily, including
through nested control expansions and changes of the selected binder. -/
theorem proofErase_stage_zero_lambda_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b T)
    (hn : ¬ IsProof Γ (.lam A b))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) out) :
    ∃ X y, StageZeroLambdaOrigin D Γ A b u X y ∧ ProofShape.BetaRed out (.lam X y) := by
  exact (proofErase_stage_zero_lambda_observation heq hs hΓ hA hb hn R).readout

omit [Params] in
/-- A literal lambda with a base demand is exactly its marked payload;
control lambdas can only satisfy functional demands. -/
theorem ProofShape.LambdaOriginObservation.Obs.literal_lambda_payload
    (H : Obs P 0 S (.lam X y) .pi) : P X y := by
  rcases H.lam_inv with ⟨_, A, b, HP, EX, Ey⟩ | ⟨keys, result, E, _⟩
  · simp only [ProofShape.liftN_zero] at EX Ey
    subst X y
    exact HP
  · cases E

/-- A typed lambda-to-lambda path retains exact component computations in
the original scopes, at stage zero even when the path uses control wrappers. -/
theorem proofErase_stage_zero_lambda_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b T)
    (hn : ¬ IsProof Γ (.lam A b))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) (.lam X y)) :
    StageZeroLambdaOrigin D Γ A b u X y :=
  (proofErase_stage_zero_lambda_observation heq hs hΓ hA hb hn R).literal_lambda_payload

/-- Stage-zero lambda readout preserves both component histories and exposes
a lambda by beta alone. Extracting a body comparison from arbitrary function
comparisons is separate: this theorem tracks a computation from one lambda. -/
theorem proofErase_stage_zero_lambda_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b T)
    (hn : ¬ IsProof Γ (.lam A b))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) out) :
    LambdaReadout (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase (A :: Γ) b) out := by
  obtain ⟨X, y, ⟨A', b', T', _, _, _, _, RA, RB⟩, Rβ⟩ :=
    proofErase_stage_zero_lambda_origin heq hs hΓ hA hb hn R
  exact ⟨X, y, RA, by simpa only [proofEraseCtx] using RB, Rβ⟩

/-- A common computed endpoint of two retained typed lambdas exposes one
common literal lambda. Their exact component histories remain at stage zero
in their original contexts; the common endpoint need not itself be a lambda. -/
theorem proofErase_stage_zero_lambda_join_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (ha : env.HasType univs (A :: Γ) a T)
    (hB : env.HasType univs Γ B (.sort v)) (hb : env.HasType univs (B :: Γ) b U)
    (hna : ¬ IsProof Γ (.lam A a)) (hnb : ¬ IsProof Γ (.lam B b))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) a)) out)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ B) (proofErase (B :: Γ) b)) out) :
    ∃ X y, StageZeroLambdaOrigin D Γ A a u X y ∧
      StageZeroLambdaOrigin D Γ B b v X y ∧ ProofShape.BetaRed out (.lam X y) := by
  obtain ⟨X, y, HA, Rβ⟩ := proofErase_stage_zero_lambda_origin heq hs hΓ hA ha hna RA
  exact ⟨X, y, HA, proofErase_stage_zero_lambda_components heq hs hΓ hB hb hnb
    (RB.trans (.beta Rβ)), Rβ⟩

/-- Joining function computations suffice to extract comparisons of both
original lambda components, in either mode. Bodies use the left original
binder context. This does not assume that arbitrary function comparisons
possess a common computed endpoint. Extracting bodies from general
function comparisons remains a separate unresolved obligation. -/
theorem proofErase_stage_zero_lambda_join_compares
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (ha : env.HasType univs (A :: Γ) a T)
    (hB : env.HasType univs Γ B (.sort v)) (hb : env.HasType univs (B :: Γ) b U)
    (hna : ¬ IsProof Γ (.lam A a)) (hnb : ¬ IsProof Γ (.lam B b))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) a)) out)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ B) (proofErase (B :: Γ) b)) out) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) domainMode
      (proofErase Γ A) (proofErase Γ B) ∧
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (A :: Γ)) bodyMode
      (proofErase (A :: Γ) a) (proofErase (B :: Γ) b) := by
  obtain ⟨X, y, ⟨_, _, _, _, _, _, _, RX, Ry⟩,
    ⟨_, _, _, _, _, _, _, SX, Sy⟩, _⟩ :=
    proofErase_stage_zero_lambda_join_components heq hs hΓ hA ha hB hb hna hnb RA RB
  exact ⟨.compute RX SX (.leaf .refl),
    .compute Ry (Sy.recontext_independent (fun H => H)) (.leaf .refl)⟩

end Lean4Lean.VEnv.Strengthening
