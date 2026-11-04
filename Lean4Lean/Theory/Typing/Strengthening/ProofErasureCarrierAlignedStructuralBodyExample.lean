import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedStructuralBodies
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredPrimitiveRenaming
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredUnion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNormalSyntax

/-! # Dependent body variants with no body or image join

Both bodies retain the substituted variable as the codomain of a Pi. Different
but equivalent universe annotations prevent a literal body-beta join. The
argument images are also distinct normal universe expressions. The structural
paired-beta theorem compares the instantiated bodies nonetheless.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params]

private def zeroAlias : VLevel := .max .zero .zero
private def levelAlias : VLevel := .max (.succ .zero) .zero
private def body (u : VLevel) : VExpr := .forallE (.sort u) (.bvar 1)

private theorem body_type (hu : u.WF univs) :
    env.HasType univs [.sort (.succ .zero)] (body u) (.sort (.imax (.succ u) (.succ .zero))) := by
  exact .forallE (.sort hu) (.bvar (.succ .zero))

private theorem body_erasure (hu : u.WF univs) :
    proofErase [.sort (.succ .zero)] (body u) = .forallE (.sort u) (.bvar 1) := by
  have hΓ : OnCtx [.sort (.succ .zero)] (env.IsType univs) := ⟨trivial, _, HasType.sort (by trivial)⟩
  have hdom : env.HasType univs [.sort (.succ .zero)] (.sort u) (.sort (.succ u)) := .sort hu
  have hΓD : OnCtx [.sort u, .sort (.succ .zero)] (env.IsType univs) := ⟨hΓ, _, hdom⟩
  have hv : env.HasType univs [.sort u, .sort (.succ .zero)] (.bvar 1) (.sort (.succ .zero)) :=
    .bvar (.succ .zero)
  rw [show proofErase [.sort (.succ .zero)] (body u) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ (body_type hu)),
    show proofErase [.sort (.succ .zero)] (.sort u) = .sort u from
      if_neg (not_isProof_of_sort hΓ hdom),
    show proofErase [.sort u, .sort (.succ .zero)] (.bvar 1) = .bvar 1 from
      if_neg (not_isProof_of_sort hΓD hv)]

/-- Actual typed dependent bodies and images can both fail to join, while the
structural-variant paired-beta theorem still supplies their inferred comparison.
The codomains retain the respective argument images after instantiation. -/
theorem carrier_aligned_structural_bodies_without_joins
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∃ A x y b c B C, OnCtx [A] (env.IsType univs) ∧
      env.HasType univs [] x A ∧ env.HasType univs [] y A ∧
      env.HasType univs [A] b B ∧ env.HasType univs [A] c C ∧
      StructuralVariant (proofErase [A] b) (proofErase [A] c) ∧
      (¬ ∃ out, ProofShape.BetaRed (proofErase [A] b) out ∧ ProofShape.BetaRed (proofErase [A] c) out) ∧
      (¬ ∃ out, ScopedCompute (ErasedCarrierRecoveredUnion D) [] (proofErase [] x) out ∧
        ScopedCompute (ErasedCarrierRecoveredUnion D) [] (proofErase [] y) out) ∧
      CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) [] false
        (proofErase [] (b.inst x)) (proofErase [] (c.inst y)) := by
  have hΓ : OnCtx [.sort (.succ .zero)] (env.IsType univs) := ⟨trivial, _, HasType.sort (by trivial)⟩
  have hx : env.HasType univs [] (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hz : zeroAlias ≈ .zero := by simp [zeroAlias, VLevel.equiv_def, VLevel.eval]
  have hl : levelAlias ≈ .succ .zero := by simp [levelAlias, VLevel.equiv_def, VLevel.eval]
  have hy : env.HasType univs [] (.sort zeroAlias) (.sort (.succ .zero)) :=
    (IsDefEq.sortDF (by trivial) (by trivial) (VLevel.succ_congr hz)).defeq (.sort (by trivial))
  have Ex : proofErase [] (.sort .zero) = .sort .zero := if_neg (not_isProof_of_sort (Γ := []) trivial hx)
  have Ey : proofErase [] (.sort zeroAlias) = .sort zeroAlias := if_neg (not_isProof_of_sort (Γ := []) trivial hy)
  have hb := body_type (u := levelAlias) (by trivial)
  have hc := body_type (u := .succ .zero) (by trivial)
  have Eb := body_erasure (u := levelAlias) (by trivial)
  have Ec := body_erasure (u := .succ .zero) (by trivial)
  have V : StructuralVariant (proofErase [.sort (.succ .zero)] (body levelAlias))
      (proofErase [.sort (.succ .zero)] (body (.succ .zero))) := by
    rw [Eb, Ec]; exact .forallE (.sort hl) .refl
  have H : CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) [] false
      (proofErase [] (.sort .zero)) (proofErase [] (.sort zeroAlias)) := by
    rw [Ex, Ey]; exact .computed (.leaf (.sort hz.symm))
  refine ⟨_, _, _, _, _, _, _, hΓ, hx, hy, hb, hc, V, ?_, ?_, ?_⟩
  · rw [Eb, Ec]
    rintro ⟨out, RB, RC⟩
    have EB := RB.fixed_of_normal (Step := fun _ _ => False)
      ⟨(fun _ H => H.elim), ⟨(fun _ H => H.elim), trivial⟩, ⟨(fun _ H => H.elim), trivial⟩⟩
    have EC := RC.fixed_of_normal (Step := fun _ _ => False)
      ⟨(fun _ H => H.elim), ⟨(fun _ H => H.elim), trivial⟩, ⟨(fun _ H => H.elim), trivial⟩⟩
    have E := EB.symm.trans EC
    cases E
  · rw [Ex, Ey]
    rintro ⟨out, RX, RY⟩
    have EX := scoped_normal_fixed RX (fun _ => ⟨fun _ H => erased_carrier_recovered_union_head H, trivial⟩)
    have EY := scoped_normal_fixed RY (fun _ => ⟨fun _ H => erased_carrier_recovered_union_head H, trivial⟩)
    have E := EX.symm.trans EY
    cases E
  · exact proofErase_carrier_aligned_variant_body_beta (erased_carrier_recovered_union_rename heq hs)
      hΓ hΓ hb hc hx hy .refl .refl V H

end Lean4Lean.VEnv.Strengthening
