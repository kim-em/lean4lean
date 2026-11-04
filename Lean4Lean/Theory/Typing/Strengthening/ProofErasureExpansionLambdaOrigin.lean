import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaOriginTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionBackwardContext
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionCertificateDescent

/-! # Full lambda readout through controlled expansion

Marked observations retain actual lower lambda components and both computation
histories. Certificate descent handles temporary control binders; backward
context transport appends body computation at a changed payload domain.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.LambdaOriginObservation
variable [Params] {D : PureObservation.Definitions}

/-- A payload records actual component representatives and computation from
the initial lambda. Its body history stays in the initial binder context. -/
def ExpansionLambdaOrigin (D : PureObservation.Definitions) (Γ : List VExpr)
    (A B : VExpr) (u : VLevel) (X Y : ProofShape) : Prop :=
  ∃ A' B' T, env.IsDefEq univs Γ A A' (.sort u) ∧
    env.HasType univs (A' :: Γ) B' T ∧
    proofErase Γ A' = X ∧ proofErase (A' :: Γ) B' = Y ∧
    ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ A) X ∧
    ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) B) Y

/-- An initial typed lambda supplies a payload with reflexive component histories. -/
theorem ExpansionLambdaOrigin.refl
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B T) :
    ExpansionLambdaOrigin D Γ A B u (proofErase Γ A) (proofErase (A :: Γ) B) :=
  ⟨A, B, T, hA, hB, rfl, rfl, .refl, .refl⟩

/-- Component computation of a marked lambda lowers through every temporary
prefix, then appends both histories. Later body paths are pulled back to
the initial domain using its retained computation and actual equality. -/
theorem expansion_lambdaOrigin_componentClosure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    LambdaOriginComponentClosure (ErasedExpansionUnion D) Γ (ExpansionLambdaOrigin D Γ A B u) := by
  intro Γ' n X Y outX outY hΓ' W HP RX RY
  obtain ⟨A₀, B₀, T, HA₀, hB₀, rfl, rfl, RA₀, RB₀⟩ := HP
  have hA₀ := HA₀.hasType.2
  have hΓA₀ : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA₀⟩
  have hΓA₀' : OnCtx (A₀.liftN n :: Γ') (env.IsType univs) := ⟨hΓ', u, hA₀.weakN henv W⟩
  obtain ⟨A₁, HA₁, RA₁, EA₁⟩ := proofErase_scoped_compute_certificate_descend
    (erased_expansion_union_certificate_descent heq hs) hΓ hΓ' W hA₀ rfl RX
  have EΓB : proofEraseCtx (A₀.liftN n :: Γ') =
      (proofErase Γ A₀).liftN n :: proofEraseCtx Γ' := by
    rw [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA₀]
  obtain ⟨B₁, HB₁, RB₁, EB₁⟩ := proofErase_scoped_compute_certificate_descend
    (erased_expansion_union_certificate_descent heq hs) hΓA₀ hΓA₀' W.succ hB₀ EΓB RY
  have HC : IsDefEqCtx env univs Γ (A₀ :: Γ) (A₁ :: Γ) := .succ .zero HA₁
  have hB₁ := HB₁.hasType.2.defeqDFC henv HC
  have EB₁' := proofErase_defeqCtx hΓA₀ HC HB₁.hasType.2
  have RPB := proofErase_expansion_union_compute_backward_context heq hs hΓ HA₀ RA₀ hB₀ RB₁
  have EB₀ := proofErase_defeqCtx hΓA₀ (IsDefEqCtx.succ .zero HA₀.symm) hB₀
  rw [← EB₀, EB₁'] at RPB
  refine ⟨proofErase Γ A₁, proofErase (A₁ :: Γ) B₁,
    ⟨A₁, B₁, T, HA₀.trans HA₁, hB₁, rfl, rfl, RA₀.trans RA₁, RB₀.trans RPB⟩, EA₁.symm, ?_⟩
  rw [EB₁'] at EB₁
  exact EB₁.symm

/-- A lambda readout retains both computational histories in their original
scopes, together with a finite beta path from the whole computed function. -/
def ProofShape.LambdaReadout (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (A b out : ProofShape) : Prop :=
  ∃ X y, ScopedCompute Step Δ A X ∧ ScopedCompute Step (A :: Δ) b y ∧
    ProofShape.BetaRed out (.lam X y)

/-- Every expanded path from a retained typed lambda has an actual lower
lambda origin. Its annotation and body may both compute arbitrarily, including
through nested control expansions and changes of the selected binder. -/
theorem proofErase_expansion_union_lambda_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b T)
    (hn : ¬ IsProof Γ (.lam A b))
    (R : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) out) :
    ∃ X y, ExpansionLambdaOrigin D Γ A b u X y ∧ ProofShape.BetaRed out (.lam X y) := by
  have E : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) := if_neg hn
  have H : Obs (ExpansionLambdaOrigin D Γ A b u) 0 (fun _ _ => False)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) .pi := by
    simpa only [ProofShape.liftN_zero] using
      (Obs.payload (n := 0) (S := fun _ _ => False) (ExpansionLambdaOrigin.refl hA hb))
  have HO := proofErase_scoped_compute_lambdaOriginObservation
    (erased_expansion_union_descent heq hs) erased_expansion_union_lambdaOriginObservation
    (expansion_lambdaOrigin_componentClosure heq hs hΓ) R hΓ (Ctx.LiftN.zero [])
    (HasType.lam hA hb) rfl E H
  exact HO.readout

/-- Full lambda endpoint factorization up to beta, with annotation and body
computations in the original scopes. No native argument or purity is assumed. -/
theorem proofErase_expansion_union_lambda_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b T)
    (hn : ¬ IsProof Γ (.lam A b))
    (R : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) out) :
    LambdaReadout (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase (A :: Γ) b) out := by
  obtain ⟨X, y, ⟨A', b', T', _, _, _, _, RA, RB⟩, Rβ⟩ :=
    proofErase_expansion_union_lambda_origin heq hs hΓ hA hb hn R
  exact ⟨X, y, RA, by simpa only [proofEraseCtx] using RB, Rβ⟩

/-- Between literal lambda endpoints, the original component paths and
raw beta residuals from the final components meet at the same selected pair.
The body computation is indexed by the original annotation. -/
theorem proofErase_expansion_lambda_component_residuals
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b T)
    (hn : ¬ IsProof Γ (.lam A b))
    (R : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) (.lam outA outB)) :
    ∃ X y, ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ A) X ∧
      ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) y ∧
      ProofShape.BetaRed outA X ∧ ProofShape.BetaRed outB y := by
  obtain ⟨X, y, RA, RB, Rβ⟩ := proofErase_expansion_union_lambda_readout heq hs hΓ hA hb hn R
  obtain ⟨X', y', E, RX, RY⟩ := Rβ.lam_inv
  obtain ⟨rfl, rfl⟩ := ProofShape.lam.inj E
  exact ⟨_, _, RA, by simpa only [proofEraseCtx] using RB, RX, RY⟩

/-- Finite whole-function computation has a finite later bound on both
component histories, retaining the exact beta-exposed lambda. -/
theorem proofErase_expansion_stage_lambda_readout_later
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b T)
    (hn : ¬ IsProof Γ (.lam A b))
    (R : ScopedCompute (ErasedExpansionStage D stage) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) out) :
    ∃ later, stage ≤ later ∧ LambdaReadout (ErasedExpansionStage D later) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase (A :: Γ) b) out := by
  obtain ⟨X, y, RA, RB, Rβ⟩ := proofErase_expansion_union_lambda_readout heq hs hΓ hA hb hn
    (R.mono (fun H => ⟨stage, H⟩))
  obtain ⟨n, RA⟩ := RA.finite_stage (Stages := ErasedExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  obtain ⟨m, RB⟩ := RB.finite_stage (Stages := ErasedExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  refine ⟨max stage (max n m), by omega, X, y, ?_, ?_, Rβ⟩
  · exact RA.mono (fun H => erased_expansion_stage_mono (by omega) H)
  · exact RB.mono (fun H => erased_expansion_stage_mono (by omega) H)

end Lean4Lean.VEnv.Strengthening
