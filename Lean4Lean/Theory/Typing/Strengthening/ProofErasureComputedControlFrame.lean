import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageZeroSortExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageZeroTerminalTransport

/-! # Contract control frames after computation of their binder annotation

The comparison's binder need not remain a literal universe. Its forward
history from the original universe supplies exact native typing of the fixed
sort argument at the changed annotation. This retains dependent body checks
at every finite stage. At stage zero, terminal-image transport removes the forward-history premise
entirely. Extracting the body check from arbitrary computed function comparison
remains open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- A forward computation of a universe annotation supplies exact native
images for substitution of its original sort inhabitant. The annotation may
contain arbitrary intermediate control frames. Ordinary equality interprets
the substitution; the forward history supplies its additional native evidence. -/
theorem computed_universe_control_images
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (HC : env.IsDefEq univs Γ (.sort (.succ u)) C (.sort v))
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.sort (.succ u)) (proofErase Γ C)) :
    StaticStructureEtaNativeSubstitution.ImageSubstitution D 0
      (proofEraseCtx (C :: Γ)) (proofEraseCtx Γ)
      (ProofShape.Subst.one (.sort u)) := by
  have hP : env.HasType univs Γ (.sort u) C := HC.defeq (.sort hu)
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, v, HC.hasType.2⟩
  have EP : proofErase Γ (.sort u) = .sort u :=
    if_neg (not_isProof_of_sort hΓ (HasType.sort hu))
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.sort u)) (proofErase Γ C) := by
    rw [EP]
    exact .convert (.sort hu) RC
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := VExpr.sort u) (A₀ := C)).substEq hΓC hP
  rw [← EP]
  intro Γ' hΓ' EΓ'
  exact NativeImageTransport.ImageSubstitution.of_typed hΓ W
    (erasedSubstAgreement_one hΓC hP) (NativeImageTransport.Images.inst RN) hΓ' EΓ'

/-- Both compared control arguments return to the fixed sort, and the body
comparison survives contraction at its original finite stage. Bodies may
have a dependent common type under the computed annotation. Their comparison
is an explicit premise, not extracted from an arbitrary function comparison.
The displayed lambda domains are discarded by beta. -/
theorem computed_universe_control_frame_pair
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (HC : env.IsDefEq univs Γ (.sort (.succ u)) C (.sort v))
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.sort (.succ u)) (proofErase Γ C))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (hx : env.HasType univs Γ x (.sort w)) (hy : env.HasType univs Γ y (.sort z))
    (HB : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx (C :: Γ)) mode
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b))
    (HX : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) xMode
      (.sort u) (proofErase Γ x))
    (HY : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) yMode
      (.sort u) (proofErase Γ y)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx Γ)
      (.app (.lam K (proofErase (C :: Γ) a)) (proofErase Γ x))
      (proofErase Γ (a.inst (.sort u))) ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx Γ)
      (.app (.lam L (proofErase (C :: Γ) b)) (proofErase Γ y))
      (proofErase Γ (b.inst (.sort u))) ∧
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst (.sort u))) (proofErase Γ (b.inst (.sort u))) := by
  have hP : env.HasType univs Γ (.sort u) C := HC.defeq (.sort hu)
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, v, HC.hasType.2⟩
  have EP : proofErase Γ (.sort u) = .sort u :=
    if_neg (not_isProof_of_sort hΓ (HasType.sort hu))
  have H := StaticStructureEtaNativeSubstitution.check heq hs (k := 0) HB hΓC ha hb rfl rfl rfl
    (computed_universe_control_images hΓ hu HC RC)
  have EA := proofErase_instN hΓC hP Ctx.InstN.zero ha
  have EB := proofErase_instN hΓC hP Ctx.InstN.zero hb
  rw [EP] at EA EB
  have RX := (stage_zero_compared_sort_returns heq hs hΓ hu hx HX).mono
    (fun H => erased_static_structure_eta_expansion_stage_mono (Nat.zero_le n) H)
  have RY := (stage_zero_compared_sort_returns heq hs hΓ hu hy HY).mono
    (fun H => erased_static_structure_eta_expansion_stage_mono (Nat.zero_le n) H)
  refine ⟨(ScopedCompute.app .refl RX).trans (.beta ?_),
    (ScopedCompute.app .refl RY).trans (.beta ?_), ?_⟩
  · rw [EA]; exact .beta
  · rw [EB]; exact .beta
  · rw [EA, EB]
    simpa only [Nat.add_zero, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H

/-- Both compared control arguments return to the fixed sort, and the body
comparison survives contraction at stage zero without a forward annotation path.
Bodies may have a dependent common type under a universe-convertible annotation.
Their comparison
is an explicit premise, not extracted from an arbitrary function comparison.
The displayed lambda domains are discarded by beta. -/
theorem stage_zero_converted_control_frame_pair
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (HC : env.IsDefEq univs Γ (.sort (.succ u)) C (.sort v))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (hx : env.HasType univs Γ x (.sort w)) (hy : env.HasType univs Γ y (.sort z))
    (HB : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ)) mode
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b))
    (HX : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) xMode
      (.sort u) (proofErase Γ x))
    (HY : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) yMode
      (.sort u) (proofErase Γ y)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.app (.lam K (proofErase (C :: Γ) a)) (proofErase Γ x))
      (proofErase Γ (a.inst (.sort u))) ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.app (.lam L (proofErase (C :: Γ) b)) (proofErase Γ y))
      (proofErase Γ (b.inst (.sort u))) ∧
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst (.sort u))) (proofErase Γ (b.inst (.sort u))) := by
  have hP : env.HasType univs Γ (.sort u) C := HC.defeq (.sort hu)
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, v, HC.hasType.2⟩
  have EP : proofErase Γ (.sort u) = .sort u :=
    if_neg (not_isProof_of_sort hΓ (HasType.sort hu))
  have H := stage_zero_compare_inst_terminal heq hs hΓ hP (.type (HasType.sort hu)) ha hb HB
  have EA := proofErase_instN hΓC hP Ctx.InstN.zero ha
  have EB := proofErase_instN hΓC hP Ctx.InstN.zero hb
  rw [EP] at EA EB
  have RX := stage_zero_compared_sort_returns heq hs hΓ hu hx HX
  have RY := stage_zero_compared_sort_returns heq hs hΓ hu hy HY
  refine ⟨(ScopedCompute.app .refl RX).trans (.beta ?_),
    (ScopedCompute.app .refl RY).trans (.beta ?_), ?_⟩
  · rw [EA]; exact .beta
  · rw [EB]; exact .beta
  · exact H

end Lean4Lean.VEnv.Strengthening
