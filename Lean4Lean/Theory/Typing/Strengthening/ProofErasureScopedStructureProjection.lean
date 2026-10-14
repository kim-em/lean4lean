import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedStructureCoverage

/-! # Selecting a recursively compared structure field

Projection consumes a structure guard by ordinary field selection and its
smaller recursive field certificate. No inferred-mode structure eta is added.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- The ordinary erased primitives are available at every contextual stage. -/
theorem erased_scoped_prefix_stage_core : ∀ stage {Δ a b},
    ErasedIotaPrimitive D a b → ErasedScopedPrefixStage D stage Δ a b := by
  intro stage
  induction stage with
  | zero => exact id
  | succ stage ih => exact fun H => .inl (ih H)

/-- Projecting a recursive structure comparison selects its corresponding
smaller field guard. Typed replay excludes a hidden result when the original
projection is a non-proof; proof results collapse on both sides. -/
theorem proofErase_scoped_structure_project
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, ProofShape.Primitive D a b → ProofShape.ScopedCompute Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (ht : env.HasType univs Γ (.proj family i a) T)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams) (hf : fields.length = info.numFields)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (Ea : proofErase Γ a = ProofShape.mkApps (.const info.ctorName ls) (ps ++ fields))
    (H : ∀ j (h : j < fields.length), fields[j] ≠ .proof →
      ProofShape.ScopedCompare Step (proofEraseCtx Γ) true fields[j]
        (.proj family j (proofErase Γ b)))
    (hidx : i < fields.length) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.proj family i a)) (proofErase Γ (.proj family i b)) := by
  have HM : ProofShape.ScopedCompare Step (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b) := by
    rw [Ea]
    exact .structFields hi hx hp hf hadm H
  have HAB := (proofErase_scoped_compare_reflect hstep hΓ ha hb HM).1
    ⟨_, (ha.isType henv hΓ).choose_spec⟩
  have HP := SimAt.proj henv.orderedStrong hΓ (fun _ ht => HAB.of_l henv hΓ ht) T ht
  by_cases hproof : IsProof Γ (.proj family i a)
  · rw [proofErase_eq_proof.2 hproof, proofErase_eq_proof.2 ((isProof_congr hΓ HP).1 hproof)]
    exact .refl
  have hproof' := mt (isProof_congr hΓ HP).2 hproof
  have Eleft : proofErase Γ (.proj family i a) =
      .proj family i (ProofShape.mkApps (.const info.ctorName ls) (ps ++ fields)) := by
    rw [show proofErase Γ (.proj family i a) = .proj family i (proofErase Γ a) from if_neg hproof, Ea]
  have R : ProofShape.ScopedCompute Step (proofEraseCtx Γ)
      (proofErase Γ (.proj family i a)) fields[i] := by
    rw [Eleft]
    apply hprim
    apply ProofShape.Primitive.projIota hi (by simp [hp, hf])
    rw [← hp, List.getElem?_append_right (by omega)]
    simp [hidx]
  have hn : fields[i] ≠ .proof := by
    intro E
    have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨out, HE, EE⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ W ht rfl
      (by simpa only [ProofShape.liftN_zero] using R)
    simp only [ProofShape.liftN_zero] at EE
    exact hproof ((isProof_congr hΓ HE).2 (proofErase_eq_proof.1 (EE.trans E)))
  rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hproof']
  exact .compute R .refl (H i hidx hn)

/-- Recursive structure guards can be projected in every finite contextual
prefix stage without increasing its bound. -/
theorem proofErase_scoped_prefix_structure_project
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (ht : env.HasType univs Γ (.proj family i a) T)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams) (hf : fields.length = info.numFields)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (Ea : proofErase Γ a = ProofShape.mkApps (.const info.ctorName ls) (ps ++ fields))
    (H : ∀ j (h : j < fields.length), fields[j] ≠ .proof →
      ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ) true fields[j]
        (.proj family j (proofErase Γ b)))
    (hidx : i < fields.length) :
    ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ) true
      (proofErase Γ (.proj family i a)) (proofErase Γ (.proj family i b)) :=
  proofErase_scoped_structure_project (erased_scoped_prefix_stage_descent heq hs stage)
    (fun H => .base (erased_scoped_prefix_stage_core stage (.inl (.inl H))))
    hΓ ha hb ht hi hx hp hf hadm Ea H hidx

end Lean4Lean.VEnv.Strengthening
