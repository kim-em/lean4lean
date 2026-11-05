import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationJoin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedSubstitution

/-! # Computation chains independent of erased representatives

An erased value may be represented by terms at different written assignments.
Nonproof erasure reflection aligns their terms; proof erasures can be represented
by the actual source proof. Thus a chain can be replayed without comparing the
assignments of arbitrary proofs or assuming computation-chain completeness.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Replay a typed chain from any typed representative of its source erasure.
The output keeps the target erasure and the new source's actual assignment.
Neither canonical Eq nor fork joining is required for this change of witness. -/
theorem TypedComputationEq.representative
    (hΓ : OnCtx Γ (env.IsType univs)) (H : TypedComputationEq D Γ a b A)
    (ha' : env.HasType univs Γ a' A') (E : proofErase Γ a' = proofErase Γ a) :
    ∃ b', TypedComputationEq D Γ a' b' A' ∧ proofErase Γ b' = proofErase Γ b := by
  by_cases hp : IsProof Γ a'
  · have hpa : IsProof Γ a := proofErase_eq_proof.mp (E.symm.trans (proofErase_eq_proof.mpr hp))
    obtain ⟨P, haP, hP⟩ := hpa
    have hpb : IsProof Γ b := ⟨P, (H.defeq.toU.of_l henv hΓ haP).hasType.2, hP⟩
    exact ⟨a', .refl ha', (proofErase_eq_proof.mpr hp).trans (proofErase_eq_proof.mpr hpb).symm⟩
  · obtain ⟨_, HN⟩ := (proofErase_reflect hΓ ha' H.defeq.hasType.1 E).2 hp
    have HE := (HN.defeq hΓ).of_l henv hΓ ha'
    have HC := TypedComputationEq.of_erasure_eq (D := D) HE E
    exact ⟨b, HC.trans (H.at_source_type hΓ HE.hasType.2), rfl⟩

/-- An erased chain has actual typed representatives in the indicated context.
This does not assert that arbitrary ordinary equalities are computational. -/
def ErasedValueChain (D : PureObservation.Definitions) (Γ : List VExpr)
    (a b : ProofShape) : Prop :=
  ∃ x y A, TypedComputationEq D Γ x y A ∧ proofErase Γ x = a ∧ proofErase Γ y = b

/-- A typed representative supplies reflexivity for its erasure. -/
theorem ErasedValueChain.refl (H : env.HasType univs Γ x A) :
    ErasedValueChain D Γ (proofErase Γ x) (proofErase Γ x) := ⟨x, x, A, .refl H, rfl, rfl⟩

/-- Reverse an erased chain using its actual witnesses. -/
theorem ErasedValueChain.symm (H : ErasedValueChain D Γ a b) : ErasedValueChain D Γ b a := by
  obtain ⟨x, y, A, H, rfl, rfl⟩ := H
  exact ⟨y, x, A, H.symm, rfl, rfl⟩

/-- Reify an erased chain at any actual source assignment. The arbitrary proof
case retains the source proof instead of equating distinct proof propositions. -/
theorem ErasedValueChain.replay (hΓ : OnCtx Γ (env.IsType univs))
    (H : ErasedValueChain D Γ a b) (hx : env.HasType univs Γ x A)
    (Ex : proofErase Γ x = a) :
    ∃ y, TypedComputationEq D Γ x y A ∧ proofErase Γ y = b := by
  obtain ⟨x', y', A', H, Ex', Ey'⟩ := H
  obtain ⟨y, HC, Ey⟩ := H.representative hΓ hx (Ex.trans Ex'.symm)
  exact ⟨y, HC, Ey.trans Ey'⟩

/-- Erased chains compose even when their middle representatives differ. -/
theorem ErasedValueChain.trans (hΓ : OnCtx Γ (env.IsType univs))
    (H : ErasedValueChain D Γ a b) (H' : ErasedValueChain D Γ b c) :
    ErasedValueChain D Γ a c := by
  obtain ⟨x, y, A, H, Ex, Ey⟩ := H
  obtain ⟨z, HZ, Ez⟩ := H'.replay hΓ H.defeq.hasType.2 Ey
  exact ⟨x, z, A, H.trans HZ, Ex, Ez⟩

/-- Typed forward computation supplies an erased value chain to its raw output. -/
theorem ErasedValueChain.of_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) out) : ErasedValueChain D Γ (proofErase Γ x) out := by
  obtain ⟨y, H, Ey⟩ := TypedComputationEq.realize_compute heq hs hΓ hx R
  exact ⟨x, y, A, H, rfl, Ey⟩

end Lean4Lean.VEnv.Strengthening
