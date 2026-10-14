import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedStructureProjection
import Lean4Lean.Theory.Typing.ProjectionIndexBound

/-! # Typed support for projecting scoped comparisons -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- An inferred major certificate projects at any already typed occurrence.
Common major types align the resulting projections and their proof classification. -/
theorem proofErase_scoped_project_inferred (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (ht : env.HasType univs Γ (.proj s i a) T)
    (H : ProofShape.ScopedCompare Step (proofEraseCtx Γ) false (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ (.proj s i a)) (proofErase Γ (.proj s i b)) := by
  have HAB := (proofErase_scoped_compare_reflect hstep hΓ ha hb H).1
    ⟨_, (ha.isType henv hΓ).choose_spec⟩
  have HP := SimAt.proj henv.orderedStrong hΓ (fun _ ht => HAB.of_l henv hΓ ht) T ht
  by_cases hp : IsProof Γ (.proj s i a)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HP).1 hp)]
    exact .refl
  · have hp' := mt (isProof_congr hΓ HP).2 hp
    rw [show proofErase Γ (.proj s i a) = .proj s i (proofErase Γ a) from if_neg hp,
      show proofErase Γ (.proj s i b) = .proj s i (proofErase Γ b) from if_neg hp']
    exact .proj H

/-- Computation of a typed major projects with exact erasures, including
whole-proof collapse at the dependent field type. -/
theorem proofErase_scoped_compute_project (hΓ : OnCtx Γ (env.IsType univs))
    (H : env.IsDefEq univs Γ a b A) (ht : env.HasType univs Γ (.proj s i a) T)
    (R : ProofShape.ScopedCompute Step Δ (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompute Step Δ (proofErase Γ (.proj s i a)) (proofErase Γ (.proj s i b)) := by
  have HP := SimAt.proj henv.orderedStrong hΓ
    (fun _ ht => (show env.IsDefEqU univs Γ a b from ⟨_, H⟩).of_l henv hΓ ht) T ht
  by_cases hp : IsProof Γ (.proj s i a)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HP).1 hp)]
    exact .refl
  · have hp' := mt (isProof_congr hΓ HP).2 hp
    rw [show proofErase Γ (.proj s i a) = .proj s i (proofErase Γ a) from if_neg hp,
      show proofErase Γ (.proj s i b) = .proj s i (proofErase Γ b) from if_neg hp']
    exact .proj R

/-- A typed projection's major cannot have an erased lambda head: its rigid
family type cannot also be the lambda's natural Pi type. -/
theorem proofErase_projection_not_lam (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.proj s i a) T)
    (E : proofErase Γ a = .lam D body) : False := by
  obtain ⟨A, b, rfl, _, _, _⟩ := erase_lam_inv E
  obtain ⟨_, _, _, _, _, _, _, hi, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
  obtain ⟨⟨_, hA⟩, _, hb⟩ := hm.hasType.2.lam_inv henv hΓ
  obtain ⟨_, hfamily⟩ := hm.hasType.2.isType henv hΓ
  exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi) hfamily
    (hm.hasType.2.uniqU henv hΓ (HasType.lam hA hb))

/-- Projection typing identifies an exposed unindexed constructor's registered
family and proves the selected index is in its erased field list. -/
theorem proofErase_projection_constructor_family (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.proj s i a) T)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams) (hf : fields.length = info.numFields)
    (Ea : proofErase Γ a = ProofShape.mkApps (.const info.ctorName ls) (ps ++ fields)) :
    s = family ∧ i < fields.length := by
  obtain ⟨args, rfl, Hargs⟩ := proofErase_const_spine_inv Ea
  have hlen := congrArg List.length Hargs
  simp only [List.length_append, List.length_map, hp, hf] at hlen
  obtain ⟨_, _, _, _, _, _, _, hi', _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
  have hnat := structure_constructor_family hΓ hi hx hlen.symm hm.hasType.2
  obtain ⟨_, hfamily⟩ := hnat.isType henv hΓ
  have E := (henv.headInversion.rigid_rigid hΓ (henv.projectionRigid hi)
    (henv.projectionRigid hi') ((hnat.uniqU henv hΓ hm.hasType.2).typeChain henv hΓ hfamily)).1
  subst s
  exact ⟨rfl, by simpa only [hf] using ht.proj_index_lt henv hΓ hi⟩

end Lean4Lean.VEnv.Strengthening
