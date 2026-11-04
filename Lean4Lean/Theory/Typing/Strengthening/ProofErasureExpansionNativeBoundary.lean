import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionNativeExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIdentityRecoveryCover
import Lean4Lean.Theory.Typing.Strengthening.RecursiveDomainLoop
import Lean4Lean.Theory.Typing.Strengthening.RecursiveTypeInhabitants

/-! # Exact native coverage still fails with controlled expansions

A retained lambda can have a constant-headed recursive assigned type. Every
native output of a lambda retains a Pi observation, whereas that assigned type
has none. Even the full expanded union therefore fails exact assigned coverage
and exact native preservation under beta. The canonical extension also has a
proved proposition front, so this is not a strengthening counterexample.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private ctx_wf fn_typed domain_typed diagonal_at_domain diagonal_not_proof
  from Lean4Lean.Theory.Typing.Strengthening.RecursiveDomainLoop
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Expanded native recovery of a raw lambda never selects a constant- or
projection-headed carrier, even at unbounded finite guard depth. -/
theorem expansion_union_native_lambda_not_primitiveHead
    (R : ScopedTypeRecovery (ErasedExpansionUnion D) Δ (.lam A b) out) :
    ¬ PrimitiveHead out :=
  (R.lambda_headObservation erased_expansion_union_headObservation
    (S := fun _ _ => False)).not_primitiveHead

namespace RecursiveDomain
/-- The actual recursive family application retains its constant head under
proof erasure; its typing in a type universe rules out proof collapse. -/
theorem erased_domain_primitiveHead
    (hc : env.constants c = some (declaration c).toVConstant) :
    PrimitiveHead (proofErase loopCtx (domainL c)) := by
  have hn := not_isProof_of_sort ctx_wf (domain_typed hc)
  have hnf := not_isProof_fn ctx_wf (family_typed hc univs loopCtx) fn_typed hn
  rw [show proofErase loopCtx (domainL c) =
      .app (proofErase loopCtx (.const c [])) (proofErase loopCtx fn) from if_neg hn,
    show proofErase loopCtx (.const c []) = .const c [] from if_neg hnf]
  trivial

/-- Exact assigned native coverage fails for the typed diagonal at its recursive
carrier, independently of which definitions the expanded union admits. -/
theorem expansion_native_exact_failure
    (hc : env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, env.IsDefEq univs Γ (.const c []) (familyValue c) familyType) :
    env.HasType univs loopCtx (diagonal (domainL c)) (domainL c) ∧
      ¬ IsProof loopCtx (diagonal (domainL c)) ∧
      ¬ ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx loopCtx)
        (proofErase loopCtx (diagonal (domainL c))) (proofErase loopCtx (domainL c)) := by
  refine ⟨diagonal_at_domain hc hδ, diagonal_not_proof hc hδ, ?_⟩
  intro R
  have EE : proofErase loopCtx (diagonal (domainL c)) =
      .lam (proofErase loopCtx (domainL c)) (proofErase (domainL c :: loopCtx) selfBody) :=
    if_neg (diagonal_not_proof hc hδ)
  exact expansion_union_native_lambda_not_primitiveHead (EE ▸ R) (erased_domain_primitiveHead hc)

/-- A typed identity cover has exact native recovery already at stage zero,
but its beta reduct has no exact assigned recovery even in the full union.
Thus transporting exact native evidence by beta cannot repair general coverage. -/
theorem expansion_native_beta_failure
    (hc : env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, env.IsDefEq univs Γ (.const c []) (familyValue c) familyType) :
    let x := diagonal (domainL c)
    let y := VExpr.app (.lam (domainL c) (.bvar 0)) x
    env.HasType univs loopCtx y (domainL c) ∧
      env.HasType univs loopCtx x (domainL c) ∧
      ProofShape.BetaRed (proofErase loopCtx y) (proofErase loopCtx x) ∧
      ScopedTypeRecovery (ErasedExpansionStage D 0) (proofEraseCtx loopCtx)
        (proofErase loopCtx y) (proofErase loopCtx (domainL c)) ∧
      ¬ ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx loopCtx)
        (proofErase loopCtx x) (proofErase loopCtx (domainL c)) := by
  obtain ⟨hx, hn, hno⟩ := expansion_native_exact_failure (D := D) hc hδ
  obtain ⟨hy, HE, RB, RN⟩ := proofErase_identity_recovery_cover
    (Step := ErasedExpansionStage D 0) ctx_wf hx
  exact ⟨hy, hx, RB, RN (fun hp => hn ((isProof_congr ctx_wf HE).1 hp)), hno⟩

omit [Params] in
/-- The checked recursive extension preserves canonical Eq and satisfies the
proposition front, while a typed beta step destroys exact native recovery from
stage zero to the full union. The obstruction is to the proposed interface. -/
theorem canonical_expansion_native_failure
    (hbase : base.WF) (heq : base.HasCanonicalEq) (hfresh : base.constants c = none) :
    letI := (extended_wf hbase hfresh).params 0
    (extended base c).HasCanonicalEq ∧ PropositionFront ∧
      ∀ D, ∃ Γ x y A,
        OnCtx Γ ((extended base c).IsType 0) ∧
        (extended base c).HasType 0 Γ y A ∧
        (extended base c).HasType 0 Γ x A ∧
        ProofShape.BetaRed (proofErase Γ y) (proofErase Γ x) ∧
        ScopedTypeRecovery (ErasedExpansionStage D 0) (proofEraseCtx Γ)
          (proofErase Γ y) (proofErase Γ A) ∧
        ¬ ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ x) (proofErase Γ A) := by
  letI := (extended_wf hbase hfresh).params 0
  refine ⟨extended_canonicalEq heq hfresh, canonical_recursiveDomain_front hbase heq hfresh, ?_⟩
  intro D
  refine ⟨loopCtx, diagonal (domainL c),
    .app (.lam (domainL c) (.bvar 0)) (diagonal (domainL c)), domainL c, ctx_wf, ?_⟩
  apply expansion_native_beta_failure (D := D) (c := c)
  · change (extended base c).constants c = some (declaration c).toVConstant
    simp [extended, stub, VEnv.addDefEq]
  · exact fun Γ => equation 0 Γ
end RecursiveDomain
end Lean4Lean.VEnv.Strengthening
