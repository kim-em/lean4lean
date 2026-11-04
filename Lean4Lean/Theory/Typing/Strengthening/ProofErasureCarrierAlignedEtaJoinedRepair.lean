import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedExpansionPiJoin

/-! # Repairing eta annotations from joined native types

Exact native recovery of an assigned Pi is unnecessary for a single eta
repair. A beta/universe-joined native output exposes a native Pi; its domain
join gives a common reduct of the two eta expansions. This accepts captured
assigned annotations without attempting to reproduce them from the short term.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A native output joined to the assigned Pi gives a descending eta guard
whose target joins the assigned eta expansion using only beta and universe
conversion. No native certificate at the exact assigned Pi is required. -/
theorem proofErase_native_eta_joined_annotation
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (RN : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) native)
    (HJ : BetaLevelJoin native
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B))) :
    ∃ expanded common,
      NativeEtaExpansion Step (proofEraseCtx Γ) (proofErase Γ f) expanded ∧
      ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) expanded common ∧
      ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ)
        (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) common := by
  obtain ⟨X, Y, RT, HX, _⟩ := HJ.pi_exposure
  have RP := RN.convert (ScopedCompute.beta RT)
  have W : Ctx.LiftN 0 0 Γ Γ := .zero []
  obtain ⟨D', C, hfD, ED, _⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ hΓ W hf
    (by simpa only [ProofShape.liftN_zero] using RP)
  simp only [ProofShape.liftN_zero] at ED
  obtain ⟨⟨_, HAD⟩, _, _⟩ := (hf.uniqU henv hΓ hfD).forallE_inv henv hΓ
  have hD : env.HasType univs Γ D' (.sort u) := hA.defeqU_l henv hΓ HAD.toU
  have SD : DomainSort (proofEraseCtx Γ) X u := ED ▸ DomainSort.of_typed hΓ hD
  have hn : ¬ IsProof Γ f := fun hp => RN.ne_proof (proofErase_eq_proof.2 hp)
  have EE := proofErase_nativeEtaExpansion hΓ hA hf hn
  have Hη : BetaLevelJoin
      (.lam X (.app ((proofErase Γ f).liftN 1) (etaArgument u)))
      (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) := by
    rw [EE]
    exact HX.lam .refl
  obtain ⟨common, RL, RR⟩ := proofErase_carrier_aligned_raw_join_realize hΓ
    (IsDefEq.eta hf).hasType.1 Hη
  exact ⟨_, common, NativeEtaExpansion.intro RP SD, RL, RR⟩

/-- One additional eta stage repairs an assigned annotation from joined
native evidence. The common reduct need not preserve the assigned annotation,
and the right residual uses no recovered guards. -/
theorem proofErase_eta_stage_joined_native_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (RN : ScopedTypeRecovery (ErasedEtaExpansionStage D k) (proofEraseCtx Γ)
      (proofErase Γ f) native)
    (HJ : BetaLevelJoin native
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B))) :
    ∃ common, ScopedCompute (ErasedEtaExpansionStage D (k + 1)) (proofEraseCtx Γ)
        (proofErase Γ f) common ∧
      ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ)
        (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) common := by
  obtain ⟨expanded, common, RE, RL, RR⟩ := proofErase_native_eta_joined_annotation
    (erased_eta_expansion_stage_descent heq hs k) hΓ hA hf RN HJ
  have RE' : ErasedEtaExpansionStage D (k + 1) (proofEraseCtx Γ) (proofErase Γ f) expanded :=
    .inr (.inr (.inr (.inr RE)))
  refine ⟨common, (ScopedCompute.base RE').trans (RL.mono ?_), RR⟩
  intro Δ a b H
  exact erased_expansion_into_eta_stage (k + 1)
    (erased_level_into_expansion_stage (k + 1) (erased_level_primitive_into_stage H (k + 1)))

/-- The union admits the same annotation repair from an arbitrary finite
native certificate. It still assumes an actual raw join to the assigned Pi;
universal joined-native coverage is not asserted. -/
theorem proofErase_eta_union_joined_native_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (RN : ScopedTypeRecovery (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) native)
    (HJ : BetaLevelJoin native
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B))) :
    ∃ common, ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ f) common ∧
      ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ)
        (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) common := by
  obtain ⟨k, RN⟩ := RN.finite_stage (Stages := ErasedEtaExpansionStage D)
    (fun {n m} hle {Δ a b} H => erased_eta_expansion_stage_mono hle H)
  obtain ⟨common, RL, RR⟩ := proofErase_eta_stage_joined_native_square heq hs hΓ hA hf RN HJ
  exact ⟨common, RL.mono (fun H => ⟨k + 1, H⟩), RR⟩

end Lean4Lean.VEnv.Strengthening
