import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureSortRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCommonNativeBinder

/-! # Returning computed universe binders to their original demand

The sort readout theorem reverses every computation starting at a literal
universe using only beta and level conversion. This supplies stage-zero exact
images for forward context transport, even when the domain path has arbitrary
guard depth. Common type arguments likewise recover their exact universe.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Every computed universe returns to the original literal universe at
stage zero: beta removes expansion frames and level conversion restores the
chosen universe expression. This is a special reversal theorem, not confluence. -/
theorem static_structure_computed_sort_returns
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.sort u) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) out (.sort u) := by
  obtain ⟨v, HE, _, RB⟩ := proofErase_static_structure_union_sort_readout heq hs hΓ hu R
  exact (ScopedCompute.beta RB).trans (.base (.inl (.inr (.sort HE.symm hu))))

/-- A computed universe binder supplies exact stage-zero identity images in
the forward direction. Its arbitrary-depth domain computation is discharged
by sort readout, with no native coverage or type-fork premise. -/
theorem static_structure_native_computed_sort_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAC : env.IsDefEq univs Γ (.sort u) C (.sort v))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.sort u) (proofErase Γ C)) :
    StaticStructureEtaNativeSubstitution.ImageSubstitution D 0
      (proofEraseCtx (.sort u :: Γ)) (proofEraseCtx (C :: Γ)) ProofShape.Subst.id := by
  have hU := HAC.hasType.1
  have RC := static_structure_computed_sort_returns heq hs hΓ (hU.sort_inv henv.ordered) R
  have E : proofErase Γ (.sort u) = .sort u := if_neg (not_isProof_of_sort hΓ hU)
  rw [← E] at RC
  intro Γ' hΓ' EΓ'
  exact static_structure_native_backward_context heq hs hΓ HAC.symm RC hΓ' EΓ'

/-- Forward computation transport across a computed universe binder keeps
both the exact output and the original stage. -/
theorem proofErase_static_structure_compute_sort_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAC : env.IsDefEq univs Γ (.sort u) C (.sort v))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.sort u) (proofErase Γ C))
    (ht : env.HasType univs (.sort u :: Γ) e T)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx (.sort u :: Γ))
      (proofErase (.sort u :: Γ) e) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx (C :: Γ))
      (proofErase (C :: Γ) e) out := by
  have hΓA : OnCtx (.sort u :: Γ) (env.IsType univs) := ⟨hΓ, v, HAC.hasType.1⟩
  have R' := StaticStructureEtaNativeSubstitution.compute heq hs R hΓA ht rfl rfl
    (static_structure_native_computed_sort_context heq hs hΓ HAC RA)
  simp only [Nat.add_zero, ProofShape.subst_id] at R'
  simpa only [proofErase_defeqCtx hΓA (IsDefEqCtx.succ .zero HAC) ht] using R'

/-- Native recovery also transports forward across a computed universe
binder with the exact selected output and no increase in guard depth. -/
theorem proofErase_static_structure_recovery_sort_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAC : env.IsDefEq univs Γ (.sort u) C (.sort v))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.sort u) (proofErase Γ C))
    (ht : env.HasType univs (.sort u :: Γ) e T)
    (R : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx (.sort u :: Γ))
      (proofErase (.sort u :: Γ) e) out) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx (C :: Γ))
      (proofErase (C :: Γ) e) out := by
  have hΓA : OnCtx (.sort u :: Γ) (env.IsType univs) := ⟨hΓ, v, HAC.hasType.1⟩
  have R' := StaticStructureEtaNativeSubstitution.recovery heq hs R hΓA ht rfl rfl
    (static_structure_native_computed_sort_context heq hs hΓ HAC RA)
  simp only [Nat.add_zero, ProofShape.subst_id] at R'
  simpa only [proofErase_defeqCtx hΓA (IsDefEqCtx.succ .zero HAC) ht] using R'

/-- Common-native evidence for a type argument meets its assigned universe
exactly. This discharges the image premise of arbitrary native substitution,
not just one application result. It makes no assertion for data arguments. -/
theorem CommonNativeArgument.exact_sort
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x (.sort u))
    (H : CommonNativeArgument D Γ x (.sort u)) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ (.sort u)) := by
  obtain ⟨shared, RN, RC⟩ := H (not_isProof_of_sort hΓ hx)
  obtain ⟨_, hU⟩ := hx.isType henv hΓ
  have E : proofErase Γ (.sort u) = .sort u := if_neg (not_isProof_of_sort hΓ hU)
  rw [E] at RC ⊢
  exact static_structure_exact_sort_of_common heq hs hΓ hx RN RC

/-- Beta at a commonly recovered type argument preserves every selected
native result exactly. The general common-native instantiation obligation is
not assumed: sort readout supplies the exact image for this branch. -/
theorem static_structure_common_type_beta_native_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (hb : env.HasType univs (.sort u :: Γ) b B) (hx : env.HasType univs Γ x (.sort u))
    (HX : CommonNativeArgument D Γ x (.sort u))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam (.sort u) b) x)) out) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) out :=
  static_structure_root_beta_native_recovery heq hs hΓ (HasType.sort hu) hb hx
    (fun _ => HX.exact_sort heq hs hΓ hx) RN

end Lean4Lean.VEnv.Strengthening
