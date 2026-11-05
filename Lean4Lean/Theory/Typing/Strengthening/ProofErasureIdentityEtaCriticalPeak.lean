import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreBetaSquare
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureEtaStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaLambdaEtaCoreJoin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpandedNativeJoinBoundary

/-! # A single identity-beta/native-eta peak tests arbitrary type conversion

An identity wrapper recovers its assigned function type without recovering its
argument. Its beta branch exposes the argument's written lambda domain; its eta
branch retains the assigned domain. Joining these branches in the level core
is exactly joining those domains. A concrete eta-converted-domain example needs
eta in the residual join even though the original native guard is at stage zero.
The concrete core obstruction and its eta repair already appear in
`ProofErasureEtaBetaPiBoundary`. Here the arbitrary-conversion construction is
general, and the concrete nonjoinability extends to the entire non-eta union.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Every ordinary type equation occurs as the domain comparison of one
typed identity-beta/native-eta peak. The eta guard uses stage zero. Its long
branch beta-reduces to the same constant body under the other domain, and
level-core joining of the peak is equivalent to level-core joining of A and B.
No confluence, canonical-Eq, native coverage or normalization premise is used. -/
theorem identity_eta_type_conversion_peak
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u)) :
    ∃ source T etaOut,
      source = .app (.lam (.forallE B (.sort (.succ .zero))) (.bvar 0)) (.lam A (.sort .zero)) ∧
      env.HasType univs Γ source T ∧
      BetaRed (proofErase Γ source) (.lam (proofErase Γ A) (.sort .zero)) ∧
      NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D 0)
        (proofEraseCtx Γ) (proofErase Γ source) etaOut ∧
      BetaRed etaOut (.lam (proofErase Γ B) (.sort .zero)) ∧
      (ComputeJoin (ErasedLevelCore D) (.lam (proofErase Γ A) (.sort .zero)) etaOut ↔
        ComputeJoin (ErasedLevelCore D) (proofErase Γ A) (proofErase Γ B)) := by
  let Q : VExpr := .forallE B (.sort (.succ .zero))
  let f : VExpr := .lam A (.sort .zero)
  let source : VExpr := .app (.lam Q (.bvar 0)) f
  have hA := HAB.hasType.1
  have hB := HAB.hasType.2
  have hb : env.HasType univs (A :: Γ) (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hf : env.HasType univs Γ f Q :=
    (IsDefEq.forallEDF HAB (HasType.sort (l := .succ .zero) (by trivial))).defeq (HasType.lam hA hb)
  have hn : ¬ IsProof Γ f := not_isProof_function_to_sort hΓ hf
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, hB⟩
  have Ef : proofErase Γ f = .lam (proofErase Γ A) (.sort .zero) := by
    rw [show proofErase Γ f = .lam (proofErase Γ A) (proofErase (A :: Γ) (.sort .zero)) from if_neg hn]
    exact congrArg (ProofShape.lam (proofErase Γ A)) (if_neg (not_isProof_of_sort hΓA hb))
  have hQ : env.HasType univs Γ Q (.sort (.imax u (.succ (.succ .zero)))) :=
    .forallE hB (.sort (by trivial))
  have EQ : proofErase Γ Q = .forallE (proofErase Γ B) (.sort (.succ .zero)) := by
    rw [show proofErase Γ Q = .forallE (proofErase Γ B) (proofErase (B :: Γ) (.sort (.succ .zero))) from
      if_neg (not_isProof_of_sort hΓ hQ)]
    exact congrArg (ProofShape.forallE (proofErase Γ B))
      (if_neg (not_isProof_of_sort hΓB (HasType.sort (by trivial))))
  have RB : BetaRed (proofErase Γ source) (.lam (proofErase Γ A) (.sort .zero)) := by
    simpa only [Ef] using proofErase_identity_wrapper_beta hΓ hf hn
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (proofErase Γ source) (.forallE (proofErase Γ B) (.sort (.succ .zero))) := by
    simpa only [EQ] using proofErase_identity_wrapper_native (Step := ErasedStaticStructureEtaExpansionStage D 0) hΓ hf hn
  let etaOut := ProofShape.lam (proofErase Γ B)
    (.app ((proofErase Γ source).liftN 1) (etaArgument u))
  have RE : NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (proofErase Γ source) etaOut := .intro RN (.of_typed hΓ hB)
  have Rbeta : BetaRed etaOut (.lam (proofErase Γ B) (.sort .zero)) := by
    apply (BetaRed.lam .refl (.app RB.liftN .refl)).trans
    have R := proofErase_eta_lambda_beta hΓ hA hb (proofErase Γ B)
    simpa only [show proofErase (A :: Γ) (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hΓA hb)] using R
  refine ⟨source, Q, etaOut, rfl, (nativeIdentityExpansion_equal hf).hasType.1, RB, RE, Rbeta, ?_⟩
  constructor
  · rintro ⟨shared, RL, RR⟩
    obtain ⟨X, x, rfl, RX, _⟩ := RL.level_core_lam_inv
    obtain ⟨Y, y, E, RY, _⟩ := RR.level_core_lam_inv
    cases E
    exact ⟨X, RX, RY⟩
  · rintro ⟨shared, RA, RB⟩
    exact ⟨.lam shared (.sort .zero), .lam RA .refl,
      (Compute.beta Rbeta).trans (.lam RB .refl)⟩

/-- A proposed core-residual invariant for beta/eta overlaps. The next
theorems show that this invariant is false, already for an identity beta step
and an eta expansion whose native guard uses stage zero. It is not the open
full-union confluence claim, which permits eta in the residual paths. -/
def BetaEtaCoreForkJoin (D : Definitions) : Prop :=
  ∀ {Γ e T left right}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
    BetaRed (proofErase Γ e) left →
    NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (proofErase Γ e) right → ComputeJoin (ErasedLevelCore D) left right

/-- Even the identity instances of the proposed beta/eta core invariant
would make the ordinary level core complete for all type conversion. This
consequence does not require soundness or confluence of that core. -/
theorem BetaEtaCoreForkJoin.type_conversion
    (H : BetaEtaCoreForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u)) :
    ComputeJoin (ErasedLevelCore D) (proofErase Γ A) (proofErase Γ B) := by
  obtain ⟨source, T, out, _, ht, RB, RE, _, HE⟩ := identity_eta_type_conversion_peak (D := D) hΓ HAB
  exact HE.1 (H hΓ ht RB RE)

namespace EtaRecoveryJoinBoundary
open private context native assigned nativeRaw assignedRaw context_wf types_equal erasures
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
open private raw_no_join context_pure
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedJoinedNativeBoundary

private theorem domain_eta_path (D : Definitions) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx (context []))
      (proofErase (context []) native) (proofErase (context []) assigned) := by
  have hΓ : OnCtx ([] : List VExpr) (env.IsType univs) := trivial
  have RN := native_eta_expansion_recovery (D := D) hΓ
  have hn : ¬ IsProof (context []) (.bvar 0) := fun hp => RN.ne_proof (proofErase_eq_proof.2 hp)
  rw [show proofErase (context []) (.bvar 0) = .bvar 0 from if_neg hn] at RN
  have R := RN.bvar_compute
  have EO : contextOracle (proofEraseCtx (context [])) 0 = proofErase (context []) native := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid (context_wf hΓ)
      (Lookup.zero (ty := VExpr.app (.bvar 0) (.bvar 1)))]
    rfl
  rw [EO] at R
  exact R.mono (erased_eta_into_static_structure_eta_stage 1)

private theorem domains_not_core_join (D : Definitions) :
    ¬ ComputeJoin (ErasedLevelCore D) (proofErase (context []) native)
      (proofErase (context []) assigned) := by
  obtain ⟨EN, EA⟩ := erasures (Γ := []) trivial
  rw [EN, EA]
  rintro ⟨shared, RN, RA⟩
  have HΓ := context_pure (Γ := []) (by intro a ha; cases ha)
  exact raw_no_join (proofErase_expanded_pure_common_join HΓ
    (show PureLambda nativeRaw from by trivial) (show PureLambda assignedRaw from by trivial)
    (RN.scoped (fun H => .base ⟨0, .inl H⟩)) (RA.scoped (fun H => .base ⟨0, .inl H⟩)))

omit [Params] in
private theorem beta_level_lam_domains (H : BetaLevelJoin (.lam A b) (.lam B c)) :
    BetaLevelJoin A B := by
  obtain ⟨left, right, RL, RR, V⟩ := H
  obtain ⟨X, x, rfl, RX, _⟩ := RL.lam_inv
  obtain ⟨Y, y, rfl, RY, _⟩ := RR.lam_inv
  have HXY : StructuralVariant X Y := by
    cases V with
    | refl => exact .refl
    | lam HA _ => exact HA
  exact ⟨X, Y, RX, RY, HXY⟩

/-- A concrete typed identity-beta/native-eta peak has no level-core join,
nor a join at any depth of the entire non-eta singleton/expansion union,
but has an explicit join at the first eta stage. The domains are the familiar
neutral types F f and F (fun x => f x). This works over every well-formed
environment, hence also with canonical Eq, and every definition collection.
It refutes only core residuals, not full-union confluence or strengthening. -/
theorem identity_beta_eta_needs_eta_residual (D : Definitions) :
    ∃ Γ source T left right shared, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ source T ∧
      BetaRed (proofErase Γ source) left ∧
      NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D 0)
        (proofEraseCtx Γ) (proofErase Γ source) right ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ) left shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ) right shared ∧
      ¬ ComputeJoin (ErasedLevelCore D) left right ∧
      ¬ ∃ out, ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) left out ∧
        ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) right out := by
  have hΓ := context_wf (Γ := []) trivial
  obtain ⟨source, T, out, ES, ht, RB, RE, RC, HE⟩ :=
    identity_eta_type_conversion_peak (D := D) hΓ (types_equal (Γ := [])).symm
  refine ⟨context [], source, T, _, out, .lam (proofErase (context []) assigned) (.sort .zero),
    hΓ, ht, RB, RE, .lam (domain_eta_path D) .refl, .beta RC,
    (fun H => domains_not_core_join D (HE.1 H)), ?_⟩
  have HΓ := context_pure (Γ := []) (by intro a ha; cases ha)
  have HS : PureLambda (proofErase (context []) source) := by
    classical
    rw [ES]
    have pure_if {p : Prop} [Decidable p] {a b : ProofShape}
        (ha : PureLambda a) (hb : PureLambda b) : PureLambda (if p then a else b) := by
      split <;> assumption
    simp only [native, assigned, proofErase]
    repeat' first | apply pure_if | constructor | trivial
  have HR : PureLambda out := by
    cases RE with
    | intro RN _ =>
      have HP := RN.pure_context (fun H => erased_expansion_stage_pure_root 0 H) HΓ HS
      exact ⟨HP.1, HS.liftN, by unfold etaArgument; split <;> trivial⟩
  obtain ⟨EN, EA⟩ := erasures (Γ := []) trivial
  have HL : PureLambda (.lam (proofErase (context []) native) (.sort .zero)) := by
    rw [EN]; trivial
  rintro ⟨shared, RL, RR⟩
  have H := beta_level_lam_domains
    ((proofErase_expanded_pure_common_join HΓ HL HR RL RR).trans (.beta RC))
  rw [EN, EA] at H
  exact raw_no_join H

end EtaRecoveryJoinBoundary

/-- The proposed core-residual invariant fails even though both branches of
the counterexample do join with eta available at the first stage. Increasing
only the depth of the original native guard cannot repair this invariant. -/
theorem not_beta_eta_core_fork_join (D : Definitions) : ¬ BetaEtaCoreForkJoin D := by
  intro H
  obtain ⟨Γ, source, T, left, right, shared, hΓ, ht, RB, RE, _, _, Hno, _⟩ :=
    EtaRecoveryJoinBoundary.identity_beta_eta_needs_eta_residual D
  exact Hno (H hΓ ht RB RE)

end Lean4Lean.VEnv.Strengthening
