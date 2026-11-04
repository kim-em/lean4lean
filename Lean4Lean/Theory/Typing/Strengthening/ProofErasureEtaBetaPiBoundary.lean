import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpandedNativeJoinBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaLambdaEtaInstances

/-! # Head beta can force eta outside the core-join invariant

An identity wrapper stores a Pi whose domain is eta-converted from the literal
lambda argument's domain. Both endpoints recover native Pis. Nevertheless eta
at the wrapper and beta of the wrapper cannot be joined in the level core.
One eta step inside the surviving lambda annotation repairs the same peak.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private scoped_normal_fixed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
open private raw_no_join context_pure from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedJoinedNativeBoundary
open private context native assigned nativeRaw assignedRaw context_wf native_typed types_equal erasures normal_forms source_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
namespace EtaBetaPiBoundary
open EtaRecoveryJoinBoundary

private def valueRaw : ProofShape := .lam nativeRaw (.sort .zero)
private def typeRaw : ProofShape := .forallE assignedRaw (.sort (.succ .zero))
private def sourceRaw : ProofShape := .app (.lam typeRaw (.bvar 0)) valueRaw
private def longRaw : ProofShape := .lam assignedRaw (.app (sourceRaw.liftN 1) (.bvar 0))
private def finalRaw : ProofShape := .lam assignedRaw (.sort .zero)

private theorem source_beta : BetaRed sourceRaw valueRaw := by
  simpa only [sourceRaw, ProofShape.inst, Nat.lt_irrefl, ↓reduceIte, ProofShape.liftN_zero] using
    (BetaRed.beta (A := typeRaw) (b := .bvar 0) (a := valueRaw))

private theorem long_beta : BetaRed longRaw finalRaw := by
  apply ProofShape.BetaRed.lam .refl
  apply (ProofShape.BetaRed.app (source_beta.liftN (n := 1)) .refl).trans
  simpa only [valueRaw, ProofShape.liftN, ProofShape.inst] using
    (BetaRed.beta (A := nativeRaw.liftN 1) (b := .sort .zero) (a := .bvar 0))

private theorem normal_no_join : ¬ BetaLevelJoin valueRaw finalRaw := by
  rintro ⟨a, b, RA, RB, V⟩
  have HN (x) (hx : NormalSyntax (fun _ _ => False) x) :
      NormalSyntax (fun _ _ => False) (.lam x (.sort .zero)) :=
    ⟨fun _ H => H.elim, hx, fun _ H => H.elim, trivial⟩
  have E₁ := scoped_normal_fixed (ScopedCompute.beta (Step := fun _ _ _ => False) (Δ := []) RA)
    (fun Δ => HN _ (normal_forms (Step := fun _ _ _ => False) (fun H => H.elim) Δ).1)
  have E₂ := scoped_normal_fixed (ScopedCompute.beta (Step := fun _ _ _ => False) (Δ := []) RB)
    (fun Δ => HN _ (normal_forms (Step := fun _ _ _ => False) (fun H => H.elim) Δ).2)
  rw [E₁, E₂] at V
  cases V with
  | lam HD _ => exact raw_no_join (.variant HD)

private theorem source_long_no_join : ¬ BetaLevelJoin sourceRaw longRaw := by
  intro H
  exact normal_no_join ((BetaLevelJoin.beta source_beta).symm.trans (H.trans (.beta long_beta)))

variable [Params]
private theorem core_no_join (D : Definitions) (HΓ : PureContext Δ) :
    ¬ ComputeJoin (ErasedLevelCore D) sourceRaw longRaw := by
  rintro ⟨shared, RA, RB⟩
  apply source_long_no_join
  exact proofErase_expanded_pure_common_join HΓ (by trivial) (by trivial)
    (RA.scoped (fun H => .base (erased_level_core_expansion_into_union (.inl H))))
    (RB.scoped (fun H => .base (erased_level_core_expansion_into_union (.inl H))))

private theorem domain_eta_path (D : Definitions) (hΓ : OnCtx Γ (env.IsType univs)) :
    ScopedCompute (ErasedEtaExpansionStage D 1) (proofEraseCtx (context Γ)) nativeRaw assignedRaw := by
  have RN := native_eta_expansion_recovery (D := D) hΓ
  have hC := context_wf hΓ
  have hn := not_proof_at_positive_type hC native_typed source_typed
  rw [show proofErase (context Γ) (.bvar 0) = .bvar 0 from if_neg hn] at RN
  have R := RN.bvar_compute
  rw [proofEraseCtx_oracle, erasedTypeOracle_valid hC
    (Lookup.zero (ty := VExpr.app (.bvar 0) (.bvar 1)))] at R
  change ScopedCompute _ _ (proofErase (context Γ) native) (proofErase (context Γ) assigned) at R
  rw [(erasures hΓ).1, (erasures hΓ).2] at R
  exact R

/-- Native Pi availability at both sides of one typed head-beta step does not
make native eta core-joinable with the original source. The beta target is a
literal lambda. The very same peak closes at eta stage one by computing inside
its domain annotation, so this is not a confluence or strengthening counterexample.
It applies to every definition collection without extra environment declarations. -/
theorem typed_pi_beta_core_failure_and_eta_repair (D : Definitions) :
    ∃ Γ e f T A b expanded nativePi,
      OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ e T ∧ env.HasType univs Γ f T ∧
      env.IsDefEq univs Γ e f T ∧ proofErase Γ f = .lam A b ∧
      BetaRed (proofErase Γ e) (proofErase Γ f) ∧
      ScopedTypeRecovery (ErasedEtaExpansionStage D 0) (proofEraseCtx Γ) (proofErase Γ e) (proofErase Γ T) ∧
      ScopedTypeRecovery (ErasedEtaExpansionStage D 0) (proofEraseCtx Γ) (proofErase Γ f) (.forallE A nativePi) ∧
      NativeEtaExpansion (ErasedEtaExpansionStage D 0) (proofEraseCtx Γ) (proofErase Γ e) expanded ∧
      ¬ ComputeJoin (ErasedLevelCore D) (proofErase Γ e) expanded ∧
      ∃ shared, ScopedCompute (ErasedEtaExpansionStage D 1) (proofEraseCtx Γ) (proofErase Γ f) shared ∧
        BetaRed expanded shared := by
  let Γ₀ := context []
  have hC : OnCtx Γ₀ (env.IsType univs) := context_wf trivial
  have hCA : OnCtx (native :: Γ₀) (env.IsType univs) := ⟨hC, _, native_typed⟩
  have hCB : OnCtx (assigned :: Γ₀) (env.IsType univs) := ⟨hC, _, types_equal.hasType.1⟩
  let f : VExpr := .lam native (.sort .zero)
  let T : VExpr := .forallE assigned (.sort (.succ .zero))
  have hf : env.HasType univs Γ₀ f T :=
    (IsDefEq.forallEDF types_equal.symm (HasType.sort (by trivial))).defeq
      (HasType.lam native_typed (HasType.sort (by trivial)))
  have hn := not_isProof_function_to_sort hC hf
  have hT : env.HasType univs Γ₀ T
      (.sort (.imax (.succ .zero) (.succ (.succ .zero)))) :=
    HasType.forallE types_equal.hasType.1 (HasType.sort (by trivial))
  obtain ⟨EN, EA⟩ := erasures (Γ := []) (by trivial)
  have Ef : proofErase Γ₀ f = valueRaw := by
    change proofErase Γ₀ (.lam native (.sort .zero)) = _
    rw [show proofErase Γ₀ (.lam native (.sort .zero)) = .lam _ _ from if_neg hn, EN,
      show proofErase (native :: Γ₀) (.sort .zero) = .sort .zero from
        if_neg (not_isProof_of_sort hCA (HasType.sort (by trivial)))]
    rfl
  have ET : proofErase Γ₀ T = typeRaw := by
    change proofErase Γ₀ (.forallE assigned (.sort (.succ .zero))) = _
    rw [show proofErase Γ₀ (.forallE assigned (.sort (.succ .zero))) = .forallE _ _ from
      if_neg (not_isProof_of_sort hC hT), EA,
      show proofErase (assigned :: Γ₀) (.sort (.succ .zero)) = .sort (.succ .zero) from
        if_neg (not_isProof_of_sort hCB (HasType.sort (by trivial)))]
    rfl
  have EE : proofErase Γ₀ (.app (.lam T (.bvar 0)) f) = sourceRaw := by
    rw [proofErase_nativeIdentityExpansion hC hf hn, ET, Ef]
    rfl
  have RN := proofErase_identity_wrapper_native (Step := ErasedEtaExpansionStage D 0) hC hf hn
  have SD : DomainSort (proofEraseCtx Γ₀) assignedRaw (.succ .zero) := by
    rw [← EA]
    exact .of_typed hC types_equal.hasType.1
  have Earg : etaArgument (.succ .zero) = .bvar 0 := by
    unfold etaArgument
    split
    · rename_i H
      have := VLevel.equiv_def.1 H []
      simp [VLevel.eval] at this
    · rfl
  have RE : NativeEtaExpansion (ErasedEtaExpansionStage D 0) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (.app (.lam T (.bvar 0)) f)) longRaw := by
    have RN' := RN
    rw [ET] at RN'
    simpa only [EE, Earg, longRaw] using NativeEtaExpansion.intro RN' SD
  refine ⟨Γ₀, .app (.lam T (.bvar 0)) f, f, T, nativeRaw, .sort .zero, longRaw,
    .sort (.succ .zero), hC, (nativeIdentityExpansion_equal hf).hasType.1, hf,
    nativeIdentityExpansion_equal hf, Ef, ?_, RN, ?_, RE, ?_, ?_⟩
  · rw [EE, Ef]; exact source_beta
  · rw [Ef]; exact .lam (.sort (by trivial))
  · rw [EE]
    exact core_no_join D (context_pure (Γ := []) (by intro a ha; cases ha))
  · refine ⟨finalRaw, ?_, long_beta⟩
    rw [Ef]
    exact .lam (domain_eta_path D (Γ := []) (by trivial)) .refl

end EtaBetaPiBoundary
end Lean4Lean.VEnv.Strengthening
