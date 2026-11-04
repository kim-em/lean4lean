import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSequentialSubstitution

/-! # Replacing a protected type head after family instantiation

A family is first substituted in a context where its domain can be neutral.
The ambient type variable is then replaced by an arbitrary typed type. Both
recursive checking and first-layer computation survive; the specialized family
needs no fresh structural-path or native-recovery certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Single instantiation by a finite structural path is a certified sequence. -/
theorem SequentialSubstitution.inst_structural
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p T)
    (HR : StructuralFamilyRecovery D cut Γ p (proofErase Γ T) n) :
    SequentialSubstitution (StructuralImageSubstitution D)
      (proofEraseCtx (T :: Γ)) (proofEraseCtx Γ) (ProofShape.Subst.one (proofErase Γ p)) := by
  obtain ⟨u, hT⟩ := hp.isType henv hΓ
  have hΓT : OnCtx (T :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := T)).substEq hΓT hp
  exact .single (StructuralImageSubstitution.of_typed hΓ W
    (erasedSubstAgreement_one hΓT hp) (StructuralOrRecoveringImages.inst HR))

/-- Instantiate a finite-path image, then replace the ambient type variable.
The second step is not required to preserve any head protected by the first. -/
theorem SequentialSubstitution.inst_type_after
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort u))
    (hp : env.HasType univs (.sort u :: Γ) p T)
    (HR : StructuralFamilyRecovery D cut (.sort u :: Γ) p
      (proofErase (.sort u :: Γ) T) n) :
    SequentialSubstitution (StructuralImageSubstitution D)
      (proofEraseCtx (T :: .sort u :: Γ)) (proofEraseCtx Γ)
      ((ProofShape.Subst.one (proofErase (.sort u :: Γ) p)).comp
        (ProofShape.Subst.one (proofErase Γ C))) := by
  have hΓu : OnCtx (.sort u :: Γ) (env.IsType univs) :=
    ⟨hΓ, u.succ, HasType.sort (hC.sort_r henv hΓ)⟩
  have HC : StructuralFamilyRecovery D 0 Γ C (proofErase Γ (.sort u)) 0 := by
    rw [show proofErase Γ (.sort u) = .sort u from
      if_neg (not_isProof_of_sort hΓ (HasType.sort (hC.sort_r henv hΓ)))]
    exact .type hC
  exact .comp (inst_structural hΓu hp HR) (inst_structural hΓ hC HC)

/-- Every recursive comparison can first instantiate its family binder and then
its ambient type binder, with no recovery premise on the specialized image. -/
theorem proofErase_computed_joint_zero_compare_inst_type_after
    (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort u))
    (hp : env.HasType univs (.sort u :: Γ) p T)
    (HR : StructuralFamilyRecovery D cut (.sort u :: Γ) p
      (proofErase (.sort u :: Γ) T) n)
    (ha : env.HasType univs (T :: .sort u :: Γ) a A)
    (hb : env.HasType univs (T :: .sort u :: Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0)
      (proofEraseCtx (T :: .sort u :: Γ)) mode
      (proofErase (T :: .sort u :: Γ) a) (proofErase (T :: .sort u :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ ((a.inst p).inst C)) (proofErase Γ ((b.inst p).inst C)) := by
  have hΓu : OnCtx (.sort u :: Γ) (env.IsType univs) :=
    ⟨hΓ, u.succ, HasType.sort (hC.sort_r henv hΓ)⟩
  obtain ⟨v, hT⟩ := hp.isType henv hΓu
  have hΓT : OnCtx (T :: .sort u :: Γ) (env.IsType univs) := ⟨hΓu, v, hT⟩
  have W₁ := (Ctx.InstN.zero (Γ₀ := .sort u :: Γ) (e₀ := p) (A₀ := T)).substEq hΓT hp
  have W₂ := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := C) (A₀ := .sort u)).substEq hΓu hC
  simp only [VExpr.Subst.liftN] at W₁ W₂
  have E₁ : ErasedSubstAgreement (T :: .sort u :: Γ) (.sort u :: Γ)
      (VExpr.Subst.one p) (ProofShape.Subst.one (proofErase (.sort u :: Γ) p)) :=
    erasedSubstAgreement_one hΓT hp
  have E₂ : ErasedSubstAgreement (.sort u :: Γ) Γ
      (VExpr.Subst.one C) (ProofShape.Subst.one (proofErase Γ C)) :=
    erasedSubstAgreement_one hΓu hC
  have HH := (ComputedZeroGuardSubstitution.structural hs).sequential.check H
    hΓT ha hb rfl rfl rfl (SequentialSubstitution.inst_type_after hΓ hC hp HR)
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN,
    proofErase_subst_with hΓ W₂ (ha.subst henv.orderedStrong W₁ hΓu) E₂,
    proofErase_subst_with hΓ W₂ (hb.subst henv.orderedStrong W₁ hΓu) E₂,
    proofErase_subst_with hΓu W₁ ha E₁, proofErase_subst_with hΓu W₁ hb E₁,
    ProofShape.subst_subst] using HH

/-- A first-layer computation retains its exact twice-instantiated output after
replacing a previously protected ambient type variable by an arbitrary type. -/
theorem proofErase_computed_joint_one_compute_inst_type_after
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort u))
    (hp : env.HasType univs (.sort u :: Γ) p T)
    (HR : StructuralFamilyRecovery D cut (.sort u :: Γ) p
      (proofErase (.sort u :: Γ) T) n)
    (ht : env.HasType univs (T :: .sort u :: Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D 1)
      (proofEraseCtx (T :: .sort u :: Γ)) (proofErase (T :: .sort u :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ ((e.inst p).inst C))
      ((out.inst (proofErase (.sort u :: Γ) p)).inst (proofErase Γ C)) := by
  have hΓu : OnCtx (.sort u :: Γ) (env.IsType univs) :=
    ⟨hΓ, u.succ, HasType.sort (hC.sort_r henv hΓ)⟩
  obtain ⟨v, hT⟩ := hp.isType henv hΓu
  have hΓT : OnCtx (T :: .sort u :: Γ) (env.IsType univs) := ⟨hΓu, v, hT⟩
  have W₁ := (Ctx.InstN.zero (Γ₀ := .sort u :: Γ) (e₀ := p) (A₀ := T)).substEq hΓT hp
  have W₂ := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := C) (A₀ := .sort u)).substEq hΓu hC
  simp only [VExpr.Subst.liftN] at W₁ W₂
  have E₁ : ErasedSubstAgreement (T :: .sort u :: Γ) (.sort u :: Γ)
      (VExpr.Subst.one p) (ProofShape.Subst.one (proofErase (.sort u :: Γ) p)) :=
    erasedSubstAgreement_one hΓT hp
  have E₂ : ErasedSubstAgreement (.sort u :: Γ) Γ
      (VExpr.Subst.one C) (ProofShape.Subst.one (proofErase Γ C)) :=
    erasedSubstAgreement_one hΓu hC
  have HH := proofErase_computed_joint_one_compute_subst_sequential heq hs
    (SequentialSubstitution.inst_type_after hΓ hC hp HR) hΓT ht rfl rfl R
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst,
    ProofShape.Subst.liftN,
    proofErase_subst_with hΓ W₂ (ht.subst henv.orderedStrong W₁ hΓu) E₂,
    proofErase_subst_with hΓu W₁ ht E₁, ProofShape.subst_subst] using HH

private theorem type_variable_family_path
    (hΓ : OnCtx (.sort u :: Γ) (env.IsType univs))
    (hp : env.HasType univs (.sort u :: Γ) p (.forallE (.bvar 0) (.sort v))) :
    StructuralFamilyRecovery D 0 (.sort u :: Γ) p
      (proofErase (.sort u :: Γ) (.forallE (.bvar 0) (.sort v))) 0 := by
  have hx : env.HasType univs (.sort u :: Γ) (.bvar 0) (.sort u) := .bvar .zero
  have HC : AnchoredCarrier 0 (proofErase (.sort u :: Γ) (.bvar 0)) := by
    rw [show proofErase (.sort u :: Γ) (.bvar 0) = .bvar 0 from
      if_neg (not_isProof_of_sort hΓ hx)]
    exact ⟨0, [], Nat.le_refl 0, rfl⟩
  exact (AnchoredFamilyRecovery.of_family hΓ hp HC).structural

/-- A family over an abstract type can be specialized to any actual type in a
recursive body comparison. Neither lambda exposure nor image recovery is a
premise, before or after specialization. The original body certificate must
still exist in the abstract context. -/
theorem proofErase_computed_joint_zero_compare_inst_abstractFamily
    (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort u))
    (hp : env.HasType univs (.sort u :: Γ) p (.forallE (.bvar 0) (.sort v)))
    (ha : env.HasType univs (.forallE (.bvar 0) (.sort v) :: .sort u :: Γ) a A)
    (hb : env.HasType univs (.forallE (.bvar 0) (.sort v) :: .sort u :: Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0)
      (proofEraseCtx (.forallE (.bvar 0) (.sort v) :: .sort u :: Γ)) mode
      (proofErase (.forallE (.bvar 0) (.sort v) :: .sort u :: Γ) a)
      (proofErase (.forallE (.bvar 0) (.sort v) :: .sort u :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ ((a.inst p).inst C)) (proofErase Γ ((b.inst p).inst C)) := by
  have hΓu : OnCtx (.sort u :: Γ) (env.IsType univs) :=
    ⟨hΓ, u.succ, HasType.sort (hC.sort_r henv hΓ)⟩
  exact proofErase_computed_joint_zero_compare_inst_type_after hs hΓ hC hp
    (type_variable_family_path hΓu hp) ha hb H

/-- Abstract type-family specialization also transports every first-layer
computation, preserving its exact twice-instantiated result. -/
theorem proofErase_computed_joint_one_compute_inst_abstractFamily
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort u))
    (hp : env.HasType univs (.sort u :: Γ) p (.forallE (.bvar 0) (.sort v)))
    (ht : env.HasType univs (.forallE (.bvar 0) (.sort v) :: .sort u :: Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D 1)
      (proofEraseCtx (.forallE (.bvar 0) (.sort v) :: .sort u :: Γ))
      (proofErase (.forallE (.bvar 0) (.sort v) :: .sort u :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ ((e.inst p).inst C))
      ((out.inst (proofErase (.sort u :: Γ) p)).inst (proofErase Γ C)) := by
  have hΓu : OnCtx (.sort u :: Γ) (env.IsType univs) :=
    ⟨hΓ, u.succ, HasType.sort (hC.sort_r henv hΓ)⟩
  exact proofErase_computed_joint_one_compute_inst_type_after heq hs hΓ hC hp
    (type_variable_family_path hΓu hp) ht R

omit [Params] in
/-- Replacing the abstract type by a sort is explicitly outside global neutral
head preservation. The sequential transport theorems do not require this
condition on the later substitution. -/
theorem sort_inst_does_not_preserve_carrier_heads (v : VLevel) :
    ¬ PreservesCarrierHeads 0 0 (ProofShape.Subst.one (.sort v)) := by
  intro H
  obtain ⟨j, _, E⟩ := H 0 (Nat.le_refl 0)
  cases E

end Lean4Lean.VEnv.Strengthening
