import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIdentityEtaCriticalPeak
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointChecking
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin

/-! # Compared control functions need eta in their native-output joins

The same-function native coherence theorem cannot be extended to inferred
function comparison while retaining a level-core or stage-zero join conclusion.
Two constant callers accept the same literal sort, and their selected native
Pis compare, but their result types require eta to join. The first eta stage
repairs the example. This leaves comparison of complete outputs, rather than
stage-zero common reduction, as a possible target for different functions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives

private theorem constant_sort_caller_erase
    (hΓ : OnCtx Γ (env.IsType univs)) (hb : env.HasType univs Γ b B)
    (hn : ¬ IsProof Γ b) :
    proofErase Γ (.lam (.sort (.succ .zero)) b.lift) =
      .lam (.sort (.succ .zero)) ((proofErase Γ b).liftN 1) ∧
    proofErase Γ (.app (.lam (.sort (.succ .zero)) b.lift) (.sort .zero)) =
      .app (.lam (.sort (.succ .zero)) ((proofErase Γ b).liftN 1)) (.sort .zero) := by
  have hA : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    .sort (by trivial)
  have hΓA : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hp : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hb' := hb.weakN henv (Ctx.LiftN.one (A := .sort (.succ .zero)))
  have hf := HasType.lam hA hb'
  have HE : env.IsDefEq univs Γ
      (.app (.lam (.sort (.succ .zero)) b.lift) (.sort .zero)) b B := by
    simpa only [VExpr.inst_lift] using IsDefEq.beta hb' hp
  have hnapp := mt (isProof_congr hΓ HE).1 hn
  have hnf := not_isProof_fn hΓ hf hp hnapp
  have EF : proofErase Γ (.lam (.sort (.succ .zero)) b.lift) =
      .lam (.sort (.succ .zero)) ((proofErase Γ b).liftN 1) := by
    rw [show proofErase Γ (.lam (.sort (.succ .zero)) b.lift) = .lam _ _ from if_neg hnf,
      proofErase_liftN hΓ hΓA Ctx.LiftN.one hb,
      show proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) from
        if_neg (not_isProof_of_sort hΓ hA)]
  refine ⟨EF, ?_⟩
  rw [show proofErase Γ (.app (.lam (.sort (.succ .zero)) b.lift) (.sort .zero)) = .app _ _ from
    if_neg hnapp, EF,
    show proofErase Γ (.sort .zero) = .sort .zero from if_neg (not_isProof_of_sort hΓ hp)]

namespace EtaRecoveryJoinBoundary
open private context native assigned nativeRaw assignedRaw context_wf native_typed types_equal erasures normal_forms
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
open private raw_no_join context_pure
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedJoinedNativeBoundary
open private domain_eta_path
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureIdentityEtaCriticalPeak
open private ProofShape.beta_forallE_parts
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin

omit [Params] in
private theorem beta_level_pi_domains (H : BetaLevelJoin (.forallE A b) (.forallE B c)) :
    BetaLevelJoin A B := by
  obtain ⟨left, right, RL, RR, V⟩ := H
  obtain ⟨X, x, rfl, RX, _⟩ := ProofShape.beta_forallE_parts RL
  obtain ⟨Y, y, rfl, RY, _⟩ := ProofShape.beta_forallE_parts RR
  have HXY : StructuralVariant X Y := by
    cases V with
    | refl => exact .refl
    | forallE HA _ => exact HA
  exact ⟨X, Y, RX, RY, HXY⟩

private theorem domains_compare {Step : List ProofShape → ProofShape → ProofShape → Prop} :
    ComputedJointCompare Step Δ false nativeRaw assignedRaw :=
  .symm (.app (.leaf .refl) (.leaf (.etaL (.boundVar (f := ProofShape.bvar 2)))))

private theorem lifted_domains_compare {Step : List ProofShape → ProofShape → ProofShape → Prop} :
    ComputedJointCompare Step Δ false (nativeRaw.liftN 1) (assignedRaw.liftN 1) := by
  exact .symm (.app (.leaf .refl) (.leaf (.etaL (.boundVar (f := ProofShape.bvar 3)))))

/-- Two inferred-compared functions of the same terminal control type, applied
to the same literal sort, recover types with no common reduct even in the entire
non-eta expansion union. Their selected native Pis and complete outputs also
compare at stage zero. An explicit stage-one path joins the outputs. Thus the
fixed-function core-join theorem cannot simply replace function identity by
inferred comparison; neither output comparison nor strengthening is refuted.
The witness also provides purity, beta-normality and typed representatives of
both outputs, for transporting this example through later conversion tails.
No assumptions on the definitions or additional environment declarations are
needed, so the construction also applies in environments with canonical Eq. -/
theorem compared_control_outputs_need_eta_join (D : Definitions) :
    ∃ Γ f g T X Y outL outR, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ f (.forallE (.sort (.succ .zero)) T) ∧
      env.HasType univs Γ g (.forallE (.sort (.succ .zero)) T) ∧
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0)
        (proofEraseCtx Γ) false (proofErase Γ f) (proofErase Γ g) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ f) (.forallE (.sort (.succ .zero)) X) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ g) (.forallE (.sort (.succ .zero)) Y) ∧
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
        (.forallE (.sort (.succ .zero)) X) (.forallE (.sort (.succ .zero)) Y) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ (.app f (.sort .zero))) outL ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ (.app g (.sort .zero))) outR ∧
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0)
        (proofEraseCtx Γ) false outL outR ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ) outL outR ∧
      ¬ ComputeJoin (ErasedLevelCore D) outL outR ∧
      (¬ ∃ out, ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) outL out ∧
        ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) outR out) ∧
      PureContext (proofEraseCtx Γ) ∧ PureLambda outL ∧ PureLambda outR ∧
      NormalSyntax (fun _ _ => False) outL ∧ NormalSyntax (fun _ _ => False) outR ∧
      ∃ P Q v w, env.HasType univs Γ P (.sort v) ∧ env.HasType univs Γ Q (.sort w) ∧
        proofErase Γ P = outL ∧ proofErase Γ Q = outR := by
  let Γ := context []
  have hΓ : OnCtx Γ (env.IsType univs) := context_wf trivial
  have hΓN : OnCtx (native :: Γ) (env.IsType univs) := ⟨hΓ, _, native_typed⟩
  have hΓA : OnCtx (assigned :: Γ) (env.IsType univs) := ⟨hΓ, _, types_equal.hasType.1⟩
  let b : VExpr := .lam native (.sort .zero)
  let c : VExpr := .lam assigned (.sort .zero)
  let B : VExpr := .forallE assigned (.sort (.succ .zero))
  have hb : env.HasType univs Γ b B :=
    (IsDefEq.forallEDF types_equal.symm (HasType.sort (by trivial))).defeq
      (HasType.lam native_typed (HasType.sort (by trivial)))
  have hc : env.HasType univs Γ c B := .lam types_equal.hasType.1 (.sort (by trivial))
  have hnb := not_isProof_function_to_sort hΓ hb
  have hnc := not_isProof_function_to_sort hΓ hc
  obtain ⟨EN, EA⟩ := erasures (Γ := []) (by trivial)
  have Eb : proofErase Γ b = .lam nativeRaw (.sort .zero) := by
    rw [show proofErase Γ b = .lam _ _ from if_neg hnb, EN,
      show proofErase (native :: Γ) (.sort .zero) = .sort .zero from
        if_neg (not_isProof_of_sort hΓN (HasType.sort (by trivial)))]
  have Ec : proofErase Γ c = .lam assignedRaw (.sort .zero) := by
    rw [show proofErase Γ c = .lam _ _ from if_neg hnc, EA,
      show proofErase (assigned :: Γ) (.sort .zero) = .sort .zero from
        if_neg (not_isProof_of_sort hΓA (HasType.sort (by trivial)))]
  obtain ⟨Ef, Efp⟩ := constant_sort_caller_erase hΓ hb hnb
  obtain ⟨Eg, Egp⟩ := constant_sort_caller_erase hΓ hc hnc
  rw [Eb] at Ef Efp
  rw [Ec] at Eg Egp
  let P := ProofShape.forallE nativeRaw (.sort (.succ .zero))
  let Q := ProofShape.forallE assignedRaw (.sort (.succ .zero))
  have hPure := context_pure (Γ := []) (by intro a ha; cases ha)
  have HNP : NormalSyntax (fun _ _ => False) P :=
    ⟨fun _ H => H.elim, (normal_forms (Step := fun _ _ _ => False) (fun H => H.elim) []).1,
      fun _ H => H.elim, trivial⟩
  have HNQ : NormalSyntax (fun _ _ => False) Q :=
    ⟨fun _ H => H.elim, (normal_forms (Step := fun _ _ _ => False) (fun H => H.elim) []).2,
      fun _ H => H.elim, trivial⟩
  have pi_erase {A} (hA : env.HasType univs Γ A (.sort (.succ .zero))) :
      proofErase Γ (.forallE A (.sort (.succ .zero))) =
        .forallE (proofErase Γ A) (.sort (.succ .zero)) := by
    have hPi := HasType.forallE hA (HasType.sort (l := .succ .zero) (by trivial))
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
    rw [show proofErase Γ (.forallE A (.sort (.succ .zero))) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hPi),
      show proofErase (A :: Γ) (.sort (.succ .zero)) = .sort (.succ .zero) from
        if_neg (not_isProof_of_sort hΓA (HasType.sort (by trivial)))]
  have hTyped : ∃ P₀ Q₀ v w, env.HasType univs Γ P₀ (.sort v) ∧
      env.HasType univs Γ Q₀ (.sort w) ∧ proofErase Γ P₀ = P ∧ proofErase Γ Q₀ = Q := by
    refine ⟨.forallE native (.sort (.succ .zero)), .forallE assigned (.sort (.succ .zero)), _, _,
      .forallE native_typed (.sort (by trivial)),
      .forallE types_equal.hasType.1 (.sort (by trivial)), ?_, ?_⟩
    · rw [pi_erase native_typed, EN]
    · rw [pi_erase types_equal.hasType.1, EA]
  have Hno : ¬ ∃ out, ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) P out ∧
      ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) Q out := by
    rintro ⟨out, RL, RR⟩
    exact raw_no_join (beta_level_pi_domains (proofErase_expanded_pure_common_join
      (context_pure (Γ := []) (by intro a ha; cases ha)) (by trivial) (by trivial) RL RR))
  refine ⟨Γ, .lam (.sort (.succ .zero)) b.lift, .lam (.sort (.succ .zero)) c.lift,
    B.lift, P.liftN 1, Q.liftN 1, P, Q, hΓ,
    .lam (.sort (by trivial)) (hb.weakN henv Ctx.LiftN.one),
    .lam (.sort (by trivial)) (hc.weakN henv Ctx.LiftN.one), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    Hno, hPure, by trivial, by trivial, HNP, HNQ, hTyped⟩
  · rw [Ef, Eg]
    exact .lam (.leaf .refl) (.lam lifted_domains_compare (.leaf .refl))
  · rw [Ef]; exact .lam (.lam (.sort (by trivial)))
  · rw [Eg]; exact .lam (.lam (.sort (by trivial)))
  · exact .forallE (.leaf .refl) (.forallE lifted_domains_compare (.leaf .refl))
  · rw [Efp]
    exact .app (.lam (.lam (.sort (by trivial))))
  · rw [Egp]
    exact .app (.lam (.lam (.sort (by trivial))))
  · exact .forallE domains_compare (.leaf .refl)
  · have R := domain_eta_path D
    rw [EN, EA] at R
    exact .forallE R .refl
  · rintro ⟨out, RL, RR⟩
    exact Hno ⟨out, RL.scoped (fun H => .base ⟨0, .inl H⟩),
      RR.scoped (fun H => .base ⟨0, .inl H⟩)⟩

end EtaRecoveryJoinBoundary
end Lean4Lean.VEnv.Strengthening
