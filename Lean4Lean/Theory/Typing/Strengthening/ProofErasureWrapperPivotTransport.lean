import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCutPivotHistory
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureWrapperNativeOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCutHistoryPrimitiveSquare

/-! # Native transfer through literal wrappers after their arguments evolve

An identity frame retains ordinary typing at its annotation, rather than native
recovery of its current argument. A constant frame transfers the inner native
outputs. Both laws allow the paired pivot to be arbitrary raw syntax.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : PureObservation.Definitions}

/-- Ordinary source and type witnesses for one raw wrapper argument. This
certificate deliberately does not assert native recovery at the stored type. -/
def WrapperTypeWitness (Γ : List VExpr) (e A : ProofShape) : Prop :=
  ∃ e₀ A₀, env.HasType univs Γ e₀ A₀ ∧ proofErase Γ e₀ = e ∧ proofErase Γ A₀ = A

/-- Computation of the argument preserves its old ordinary type witness. -/
theorem WrapperTypeWitness.compute_term
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : WrapperTypeWitness Γ e A)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) e e') :
    WrapperTypeWitness Γ e' A := by
  obtain ⟨e₀, A₀, ht, Ee, EA⟩ := H
  obtain ⟨e₁, HE, E₁⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ ht rfl Ee R
  exact ⟨e₁, A₀, HE.hasType.2, E₁, EA⟩

/-- Sound computation preserves retention of an ordinarily typed source. -/
theorem WrapperTypeWitness.not_proof_after
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : WrapperTypeWitness Γ e A) (hn : e ≠ .proof)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) e e') :
    e' ≠ .proof := by
  obtain ⟨e₀, A₀, ht, Ee, _⟩ := H
  obtain ⟨e₁, HE, E₁⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ ht rfl Ee R
  intro E
  have hp := (isProof_congr hΓ HE).2 (proofErase_eq_proof.1 (E₁.trans E))
  exact hn (Ee.symm.trans (proofErase_eq_proof.2 hp))

/-- Computing the stored annotation changes ordinary typing by conversion. -/
theorem WrapperTypeWitness.compute_type
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : WrapperTypeWitness Γ e A)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) A A') :
    WrapperTypeWitness Γ e A' := by
  obtain ⟨e₀, A₀, ht, Ee, EA⟩ := H
  obtain ⟨_, hA⟩ := ht.isType henv hΓ
  obtain ⟨A₁, HE, E₁⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hA rfl EA R
  exact ⟨e₀, A₁, HE.defeq ht, Ee, E₁⟩

/-- A native guard at frame creation supplies the ordinary annotation witness
that later survives even after exact recovery of its argument has disappeared. -/
theorem WrapperTypeWitness.of_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : WrapperTypeWitness Γ e T)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) e A) :
    WrapperTypeWitness Γ e A := by
  obtain ⟨e₀, T₀, ht, rfl, _⟩ := H
  obtain ⟨A₀, hA, EA⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ ht RN
  exact ⟨e₀, A₀, hA, rfl, EA⟩

/-- Retained identity syntax has its stored type even without an argument
native certificate. -/
theorem WrapperTypeWitness.identity
    (hΓ : OnCtx Γ (env.IsType univs)) (H : WrapperTypeWitness Γ e A) (hn : e ≠ .proof) :
    WrapperTypeWitness Γ (.app (.lam A (.bvar 0)) e) A := by
  obtain ⟨e₀, A₀, ht, rfl, rfl⟩ := H
  have hne : ¬ IsProof Γ e₀ := fun hp => hn (proofErase_eq_proof.2 hp)
  exact ⟨_, A₀, (nativeIdentityExpansion_equal ht).hasType.1,
    proofErase_nativeIdentityExpansion hΓ ht hne, rfl⟩

/-- The generated unused wrapper retains the payload's ordinary type. -/
theorem WrapperTypeWitness.constant
    (hΓ : OnCtx Γ (env.IsType univs)) (H : WrapperTypeWitness Γ e A) (hn : e ≠ .proof) :
    WrapperTypeWitness Γ (constantExpansion e) A := by
  obtain ⟨e₀, A₀, ht, rfl, rfl⟩ := H
  have hne : ¬ IsProof Γ e₀ := fun hp => hn (proofErase_eq_proof.2 hp)
  exact ⟨_, A₀, (constantExpansion_equal ht).hasType.1,
    proofErase_constantExpansion hΓ ht hne, rfl⟩

/-- A raw identity function supplies its written annotation for every raw
argument. The argument need not recover that annotation. -/
theorem raw_identity_native (A e : ProofShape) :
    ScopedTypeRecovery Step Δ (.app (.lam A (.bvar 0)) e) A := by
  have R : ScopedTypeRecovery Step Δ (.app (.lam A (.bvar 0)) e) ((A.liftN 1).inst e) :=
    .app (.lam (.bvar (i := 0)))
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
    ProofShape.lift_subst_cons, ProofShape.subst_id] using R

/-- Identity frames with the same ordinary annotation have the same native
outputs, independently of their arguments. Only the source argument is typed. -/
theorem native_output_transfer_identity
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : WrapperTypeWitness Γ e A) (hn : e ≠ .proof)
    (pivot : ProofShape) :
    NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.lam A (.bvar 0)) e) (.app (.lam A (.bvar 0)) pivot) := by
  obtain ⟨e₀, A₀, ht, rfl, rfl⟩ := H
  have hne : ¬ IsProof Γ e₀ := fun hp => hn (proofErase_eq_proof.2 hp)
  intro out RN
  rw [← proofErase_nativeIdentityExpansion hΓ ht hne] at RN
  exact (raw_identity_native _ pivot).convert (static_structure_identity_native_origin heq hs hΓ ht RN)

/-- Native output transfer lifts through the generated constant frame. The
pivot argument can be raw: weakening its certificate uses only the typed scope. -/
theorem NativeOutputTransfer.constant
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HT : WrapperTypeWitness Γ e A) (hn : e ≠ .proof)
    (H : NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) e pivot) :
    NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (constantExpansion e) (constantExpansion pivot) := by
  obtain ⟨e₀, A₀, ht, rfl, _⟩ := HT
  have hne : ¬ IsProof Γ e₀ := fun hp => hn (proofErase_eq_proof.2 hp)
  intro out RN
  have RP := H out ((static_structure_constant_expansion_native_iff heq hs hΓ ht hne).1 RN)
  have hS : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := .sort (by trivial)
  have hΓS : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) := ⟨hΓ, _, hS⟩
  have hrename : ∀ {Δ Δ' a b τ}, ErasedStaticStructureEtaExpansionUnion D Δ a b →
      ContextRenaming Δ Δ' τ → ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst τ) (b.subst τ) := by
    intro Δ Δ' a b τ ⟨n, H⟩ W
    exact ⟨n, erased_static_structure_eta_expansion_stage_rename heq hs n H W⟩
  have RL := RP.rename hrename (ContextRenaming.of_liftN hΓ hΓS Ctx.LiftN.one)
  have ES : proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) :=
    if_neg (not_isProof_of_sort hΓ hS)
  simp only [subst_bvar_liftN, proofEraseCtx, ES] at RL
  simpa only [constantExpansion, ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
    ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id] using
    (ScopedTypeRecovery.app (a := .sort .zero) (ScopedTypeRecovery.lam RL))

/-- Compatible computation under the generated constant wrapper uses a typed
unused binder, without typing either endpoint of the raw payload path. -/
theorem static_structure_constant_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) e e') :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (constantExpansion e) (constantExpansion e') := by
  have hS : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := .sort (by trivial)
  have ES : proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) :=
    if_neg (not_isProof_of_sort hΓ hS)
  have SD : DomainSort (proofEraseCtx Γ) (.sort (.succ .zero)) (.succ (.succ .zero)) :=
    ⟨Γ, _, hΓ, rfl, hS, ES⟩
  exact .app (.lam .refl (static_structure_compute_under_domain heq hs SD R)) .refl

end Lean4Lean.VEnv.Strengthening
