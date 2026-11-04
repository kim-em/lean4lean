import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaJoinedRecoveryBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaNativeExample
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreGuardPrimitives

/-! # Full non-eta computation does not give universal common native coverage

On pure source and context erasures, every native output stays pure. Thus even
common reducts using the entire controlled expansion union imply beta/universe
joins. The eta-assigned neutral example refutes universal common native coverage
for that whole union, not just for the raw beta/universe join presentation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Common expanded reducts of pure endpoints imply a raw beta/universe join.
The endpoints may compute through arbitrarily many singleton stages. -/
theorem proofErase_expanded_pure_common_join
    (HΔ : PureContext Δ) (HA : PureLambda a) (HB : PureLambda b)
    (RA : ScopedCompute (ErasedExpansionUnion D) Δ a shared)
    (RB : ScopedCompute (ErasedExpansionUnion D) Δ b shared) : BetaLevelJoin a b :=
  (erased_expansion_union_pure_join RA HΔ HA).trans
    (erased_expansion_union_pure_join RB HΔ HB).symm

/-- A typed retained value can have no native output sharing a common reduct
with its assigned type in the entire non-eta expansion union. Every singleton
stage and both controlled beta expansions are allowed on both join branches.
This holds for any declaration collection and needs no extra declarations. -/
theorem expansion_common_native_failure (D : Definitions) :
    ∃ Γ p A, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ p A ∧ ¬ IsProof Γ p ∧
      PureContext (proofEraseCtx Γ) ∧ PureLambda (proofErase Γ p) ∧ PureLambda (proofErase Γ A) ∧
      ∀ native shared, ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ p) native →
        ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ A) shared →
        ¬ ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) native shared := by
  obtain ⟨Γ, p, A, hΓ, hp, hn, HΓ, HP, HA, _, Hno⟩ :=
    EtaRecoveryJoinBoundary.expansion_joined_native_failure_empty D
  refine ⟨Γ, p, A, hΓ, hp, hn, HΓ, HP, HA, ?_⟩
  intro native shared RN RA RT
  have HN : PureLambda native := RN.pure_context
    (fun ⟨stage, H⟩ => erased_expansion_stage_pure_root stage H) HΓ HP
  exact Hno native RN (proofErase_expanded_pure_common_join HΓ HN HA RT RA)

/-- In particular, level-core common-native coverage cannot be universal even
if native recovery itself is allowed every non-eta expanded singleton stage. -/
theorem level_core_common_native_failure (D : Definitions) :
    ∃ Γ p A, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ p A ∧ ¬ IsProof Γ p ∧
      ∀ native, ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ p) native →
        ¬ ComputeJoin (ErasedLevelCore D) (proofErase Γ A) native := by
  obtain ⟨Γ, p, A, hΓ, hp, hn, _, _, _, Hno⟩ := expansion_common_native_failure D
  refine ⟨Γ, p, A, hΓ, hp, hn, ?_⟩
  rintro native RN ⟨shared, RA, RT⟩
  exact Hno native shared RN
    (RA.scoped (fun H => .base (erased_level_core_expansion_into_union (.inl H))))
    (RT.scoped (fun H => .base (erased_level_core_expansion_into_union (.inl H))))

/-- A fully typed single substitution need not satisfy the new level-native
image invariant. Hence those transport theorems are conditional tools, not a
coverage proof; increasing non-eta singleton depth cannot remove this example. -/
theorem level_core_joined_images_not_universal (D : Definitions) :
    ∃ Γ p A, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ p A ∧
      OnCtx (A :: Γ) (env.IsType univs) ∧
      Ctx.SubstEq env univs Γ (VExpr.Subst.one p) (VExpr.Subst.one p) (A :: Γ) ∧
      ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one p) (ProofShape.Subst.one (proofErase Γ p)) ∧
      ¬ LevelCoreNative.Images D (A :: Γ) Γ (ProofShape.Subst.one (proofErase Γ p)) := by
  obtain ⟨Γ, p, A, hΓ, hp, hn, Hno⟩ := level_core_common_native_failure D
  obtain ⟨u, hA⟩ := hp.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W : Ctx.SubstEq env univs Γ (VExpr.Subst.one p) (VExpr.Subst.one p) (A :: Γ) :=
    Ctx.InstN.zero.substEq hΓA hp
  refine ⟨Γ, p, A, hΓ, hp, hΓA, W, erasedSubstAgreement_one hΓA hp, ?_⟩
  intro HI
  have hv : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have hvn : ¬ IsProof (A :: Γ) (.bvar 0) := fun H => hn ((isProof_subst hΓ W hv).2 H)
  obtain ⟨native, RN, RC⟩ := HI Lookup.zero hvn
  have RN' : ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ p) native :=
    RN.mono (fun H => erased_level_core_expansion_into_union (.inl H))
  have RC' : Compute (ErasedLevelCore D) (proofErase Γ A) native := by
    have H := RC.mono (Step' := ErasedLevelCore D) (fun H => Or.inl H)
    simpa only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id] using H
  exact Hno native RN' (.of_compute RC')

/-- One typed beta contraction can lose native recovery joined to the assigned
type even by arbitrary full-expanded common reducts. This is stronger than
loss of literal recovery or of beta/universe joins. It excludes eta expansion. -/
theorem identity_beta_loses_expanded_common_native (D : Definitions) :
    ∃ Γ p A, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ p A ∧ ¬ IsProof Γ p ∧
      env.IsDefEq univs Γ (.app (.lam A (.bvar 0)) p) p A ∧
      ProofShape.BetaRed (proofErase Γ (.app (.lam A (.bvar 0)) p)) (proofErase Γ p) ∧
      ScopedTypeRecovery (ErasedExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam A (.bvar 0)) p)) (proofErase Γ A) ∧
      ∀ native shared, ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ p) native →
        ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ A) shared →
        ¬ ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) native shared := by
  obtain ⟨Γ, p, A, hΓ, hp, hn, _, _, _, Hno⟩ := expansion_common_native_failure D
  exact ⟨Γ, p, A, hΓ, hp, hn, nativeIdentityExpansion_equal hp,
    proofErase_identity_wrapper_beta hΓ hp hn, proofErase_identity_wrapper_native hΓ hp hn, Hno⟩

namespace EtaRecoveryJoinBoundary
open private context assigned context_wf source_typed native_typed types_equal erasures
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
open private context_pure from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedJoinedNativeBoundary
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary

/-- One eta layer strictly repairs the same common-native coverage obstruction:
all non-eta stages fail even with full-expanded common reducts, while eta stage
one recovers the exact assigned type. This is a comparison of certificate
languages, not a counterexample to declarative strengthening. -/
theorem eta_strict_common_native_repair (D : Definitions) :
    ∃ Γ p A, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ p A ∧ ¬ IsProof Γ p ∧
      (∀ native shared, ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ p) native →
        ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ A) shared →
        ¬ ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) native shared) ∧
      ScopedTypeRecovery (ErasedEtaExpansionStage D 1) (proofEraseCtx Γ)
        (proofErase Γ p) (proofErase Γ A) := by
  have hΓ : OnCtx ([] : List VExpr) (env.IsType univs) := trivial
  have HPure : PureContext (proofEraseCtx ([] : List VExpr)) := by intro a ha; cases ha
  have hC := context_wf hΓ
  have hn := not_proof_at_positive_type hC native_typed source_typed
  have HΓ := context_pure HPure
  have HP : PureLambda (proofErase (context []) (.bvar 0)) := by
    rw [show proofErase (context []) (.bvar 0) = .bvar 0 from if_neg hn]
    trivial
  have HA : PureLambda (proofErase (context []) assigned) := by rw [(erasures hΓ).2]; trivial
  refine ⟨context [], .bvar 0, assigned, hC, types_equal.symm.defeq source_typed, hn, ?_,
    native_eta_expansion_recovery hΓ⟩
  intro native shared RN RA RT
  have HN : PureLambda native := RN.pure_context
    (fun ⟨stage, H⟩ => erased_expansion_stage_pure_root stage H) HΓ HP
  exact (native_eta_expansion_strict_repair hΓ HPure).1 native RN
    (proofErase_expanded_pure_common_join HΓ HN HA RT RA)

end EtaRecoveryJoinBoundary

end Lean4Lean.VEnv.Strengthening
