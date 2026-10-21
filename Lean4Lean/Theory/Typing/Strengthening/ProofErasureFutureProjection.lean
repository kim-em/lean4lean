import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureConstructor
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointProjection
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveBetaResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnion

/-! # Future comparisons through typed projections

An ordinary primitive has an exact residual under beta and raw substitution.
This pulls raw future comparisons back across projection iota. More generally,
typed beta replay and joint projection closure preserve any future major
comparison, including proof erasure and interpreted context substitution.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private ProofShape.primitive_beta ProofShape.beta_proj_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveBetaResidual
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- An ordinary primitive before a future comparison preserves the complete
future certificate. This requires neither typing nor a primitive confluence
law: its exact beta residual and raw substitution law suffice. -/
theorem BetaStableFamily.primitive_prefix
    (hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (HP : Primitive D a a')
    (H : BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ a' b) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ a b := by
  constructor
  · intro p q RP RQ
    obtain ⟨shared, RB, HS⟩ := ProofShape.primitive_beta HP RP
    exact .compute (hprim HS) .refl (H.1 RB RQ)
  · intro Δ' τ p q W RP RQ
    obtain ⟨shared, RB, HS⟩ := ProofShape.primitive_beta (HP.subst (σ := τ)) RP
    exact .compute (hprim HS) .refl (H.2 W RB RQ)

/-- Projection iota consumes the retained field's future comparison directly.
The constructor and major need not possess a computational join. -/
theorem BetaStableFamily.project_constructor
    (hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (hi : env.projections family info)
    (hp : ps.length = info.nparams) (hf : fields.length = info.numFields)
    (hj : i < fields.length)
    (H : BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ
      fields[i] (.proj family i m)) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ
      (.proj family i (ProofShape.mkApps (.const info.ctorName ls) (ps ++ fields)))
      (.proj family i m) := by
  apply BetaStableFamily.primitive_prefix hprim ?_ H
  apply Primitive.projIota hi (by simp [hp, hf])
  rw [← hp, List.getElem?_append_right (by omega)]
  simp [hj]

private theorem projection_beta
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (ht : env.HasType univs Γ (.proj s i a) T)
    (H : BetaStableFamily (fun Δ => JointCompare Step Δ mode)
      (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b))
    (RP : ProofShape.BetaRed (proofErase Γ (.proj s i a)) p)
    (RQ : ProofShape.BetaRed (proofErase Γ (.proj s i b)) q) :
    JointCompare Step (proofEraseCtx Γ) true p q := by
  have HAB := (proofErase_joint_compare_reflect hstep hΓ ha hb H.base).1
    ⟨_, (ha.isType henv hΓ).choose_spec⟩
  have HP := SimAt.proj henv.orderedStrong hΓ (fun _ ht => HAB.of_l henv hΓ ht) T ht
  by_cases hp : IsProof Γ (.proj s i a)
  · have E := (proofErase_eq_proof.2 hp).trans
      (proofErase_eq_proof.2 ((isProof_congr hΓ HP).1 hp)).symm
    exact (proofErase_beta_join_family hΓ ht HP.hasType.2
      (E ▸ ProofShape.BetaRed.refl) .refl).1 RP RQ
  have hq := mt (isProof_congr hΓ HP).2 hp
  rw [show proofErase Γ (.proj s i a) = .proj s i (proofErase Γ a) from if_neg hp] at RP
  rw [show proofErase Γ (.proj s i b) = .proj s i (proofErase Γ b) from if_neg hq] at RQ
  obtain ⟨pa, rfl, RA⟩ := ProofShape.beta_proj_inv RP
  obtain ⟨qb, rfl, RB⟩ := ProofShape.beta_proj_inv RQ
  obtain ⟨a', PA, EA⟩ := proofErase_beta_replay hΓ ha RA
  obtain ⟨b', PB, EB⟩ := proofErase_beta_replay hΓ hb RB
  have HA := beta_eq hΓ ha PA
  have HB := beta_eq hΓ hb PB
  have HPA := SimAt.proj henv.orderedStrong hΓ (fun _ ht => HA.toU.of_l henv hΓ ht) T ht
  have HPB := SimAt.proj henv.orderedStrong hΓ
    (fun _ ht => HB.toU.of_l henv hΓ ht) T HP.hasType.2
  have hp' := mt (isProof_congr hΓ HPA).2 hp
  have hq' := mt (isProof_congr hΓ HPB).2 hq
  have HC := proofErase_joint_project_typed hstep hprim hΓ HA.hasType.2 HB.hasType.2
    HPA.hasType.2 HPB.hasType.2 (by simpa only [EA, EB] using H.1 RA RB)
  simpa only [show proofErase Γ (.proj s i a') = .proj s i (proofErase Γ a') from if_neg hp',
    show proofErase Γ (.proj s i b') = .proj s i (proofErase Γ b') from if_neg hq', EA, EB] using HC

/-- Every typed future joint comparison is closed under projection, in either
input mode. Beta replay types the residual majors, and the ordinary joint
projection theorem handles their comparisons. Interpreted substitutions retain
the input certificate. No general primitive substitution or endpoint transport
law is assumed, and the output may be projected again.
The selected field type may depend on the original major. -/
theorem proofErase_future_project
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (ht : env.HasType univs Γ (.proj s i a) T)
    (H : BetaStableFamily (fun Δ => JointCompare Step Δ mode)
      (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b)) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ)
      (proofErase Γ (.proj s i a)) (proofErase Γ (.proj s i b)) := by
  refine ⟨fun RP RQ => projection_beta hstep hprim hΓ ha hb ht H RP RQ, ?_⟩
  intro Δ' τ p q W RP RQ
  have HAB := (proofErase_joint_compare_reflect hstep hΓ ha hb H.base).1
    ⟨_, (ha.isType henv hΓ).choose_spec⟩
  have HP := SimAt.proj henv.orderedStrong hΓ (fun _ ht => HAB.of_l henv hΓ ht) T ht
  have HC := H.subst W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  rw [← proofErase_subst_with hΓ₀ WS ht ES] at RP
  rw [← proofErase_subst_with hΓ₀ WS HP.hasType.2 ES] at RQ
  rw [← proofErase_subst_with hΓ₀ WS ha ES, ← proofErase_subst_with hΓ₀ WS hb ES,
    ← EΓ₀] at HC
  rw [← EΓ₀]
  exact projection_beta hstep hprim hΓ₀ (ha.subst henv WS) (hb.subst henv WS)
    (ht.subst henv WS) HC RP RQ

/-- The concrete joint union is closed under typed future projection, without
any unresolved substitution, carrier conversion or beta transport premise. -/
theorem proofErase_future_union_project
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (ht : env.HasType univs Γ (.proj s i a) T)
    (H : BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ mode)
      (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b)) :
    BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true) (proofEraseCtx Γ)
      (proofErase Γ (.proj s i a)) (proofErase Γ (.proj s i b)) :=
  proofErase_future_project (erased_joint_union_descent heq hs)
    (fun HP => .base ⟨0, .inl (.inl HP)⟩) hΓ ha hb ht H

end Lean4Lean.VEnv.Strengthening
