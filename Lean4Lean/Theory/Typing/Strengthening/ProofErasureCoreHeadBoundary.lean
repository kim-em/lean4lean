import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreConfluence
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPiExposure
import Lean4Lean.Theory.Typing.Strengthening.CanonicalEqHeadBoundary

/-! # Ordinary erased computation cannot expose a variable-major cast

Replay connects the actual stored/registered core to the existing constructor
observation model. The model's canonical-Eq cast boundary thus applies to scoped
comparisons, rather than merely to original head-model computations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
open ConstructorObservation (EtaCompute)
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

private theorem core_sound [Params] : ErasedCore.definitions.Sound env univs :=
  RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)

/-- Actual core pattern paths embed in the constructor head model. This retains
all stored definitions and registered structure equations, and reconstructs the
source typings for every concrete pattern encountered along the path. -/
theorem ErasedCore.pattern_head_compute {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {e out Γ T}, PatternCompute definitions e out →
      OnCtx Γ (env.IsType U) → env.HasType U Γ e T →
      EtaCompute (ClosedStructure.definitions (Definitions.ofEnv env U henv)) e out := by
  letI := henv.params U
  intro e out Γ T R hΓ ht
  induction R generalizing Γ T with
  | base R => exact .compute (R.of_inclusion (fun _ _ _ H => RegisteredStructure.definitions_inclusion H))
  | trans R₁ R₂ ih₁ ih₂ =>
    exact (ih₁ hΓ ht).trans (ih₂ hΓ (R₁.simAt core_sound hΓ _ ht).hasType.2)
  | pattern hp hm hc => exact concrete_pattern_compute henv hΓ hp hm (hc hΓ hm ht) ⟨_, ht⟩
  | app _ _ ihf ihx =>
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
    exact .app (ihf hΓ hf) (ihx hΓ hx)
  | lam _ _ ihA ihb =>
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    exact .lam (ihA hΓ hA) (ihb (show OnCtx (_ :: Γ) _ from ⟨hΓ, u, hA⟩) hb)
  | forallE _ _ ihA ihB =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    exact .forallE (ihA hΓ hA) (ihB (show OnCtx (_ :: Γ) _ from ⟨hΓ, u, hA⟩) hB)
  | proj _ ihm =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj (ihm hΓ hm.hasType.2)

private theorem forget_scope [Params] (R : ProofShape.ScopedCompute (fun _ => ErasedCore.Step) Δ a b) :
    ProofShape.Compute ErasedCore.Step a b := by
  induction R with
  | base R => exact .base R
  | beta R => exact .beta R
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | proj _ ih => exact .proj ih
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂

/-- A free proof major prevents a reflexive Pi cast from exposing a Pi by the
actual erased core relation, including all installed recursive definitions. -/
theorem ErasedCore.cast_no_pi {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ X u i A B A' B'}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ X (.sort u) →
      env.HasType U Γ (.bvar i) (eqApp (.succ u) (.sort u) X X) →
      env.HasType U Γ (.forallE A B) X →
      ¬ ProofShape.ScopedCompute (fun _ => Step) (proofEraseCtx Γ)
        (proofErase Γ (typeCast u X X (.bvar i) (.forallE A B))) (.forallE A' B') := by
  letI := henv.params U
  intro Γ X u i A B A' B' heq hu hΓ hX hq hpi
  intro R
  obtain ⟨HC, HN⟩ := ConstructorObservation.canonical_cast_full_boundary henv heq hu hΓ hX hq hpi
  obtain ⟨out, RR, _, EE⟩ := replay hΓ HC.hasType.1 (forget_scope R)
  obtain ⟨D, C, rfl, _, _, _⟩ := erase_forallE_inv EE
  apply HN D C
  apply ClosedSingleton.etaCompute_base heq
  apply (pattern_head_compute henv U RR hΓ HC.hasType.1).of_inclusion
  intro c ls rhs H
  rcases H with H | H
  · exact .inl (FullHead.quot_base henv _ _ _ H)
  · exact .inr H


/-- One contextual K-prefix stage repairs reflexive casts, including the free
proof-major Pi casts rejected by the ordinary core. Its endpoint guard is
reflexive at stage zero, so no paired-instantiation assumption is used. -/
theorem ErasedCore.reflexive_cast_stage_one [Params]
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X X))
    (he : env.HasType univs Γ e X) :
    ProofShape.ScopedCompute (ErasedScopedPrefixStage definitions 1) (proofEraseCtx Γ)
      (proofErase Γ (typeCast u X X q e)) (proofErase Γ e) := by
  have HC := IsDefEq.typeCast_refl henv heq hu hΓ hX hq he
  exact proofErase_scoped_prefix_full_forward heq core_sound hΓ HC.hasType.1 .refl

/-- The same stage-one cast reduction repairs both annotations of the diagonal
self-application witness. The looping body needs no normalization. -/
theorem ErasedCore.cast_loop_stage_one [Params]
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X X))
    (he : env.HasType univs Γ e X) :
    ProofShape.ScopedCompute (ErasedScopedPrefixStage definitions 1) (proofEraseCtx Γ)
      (ProofShape.selfLoop (proofErase Γ (typeCast u X X q e)))
      (ProofShape.selfLoop (proofErase Γ e)) := by
  have R := reflexive_cast_stage_one heq hu hΓ hX hq he
  exact .app (.lam R .refl) (.lam R .refl)

end Lean4Lean.VEnv.Strengthening
