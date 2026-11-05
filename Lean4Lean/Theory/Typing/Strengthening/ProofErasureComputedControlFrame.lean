import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageZeroSortExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageZeroTerminalTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalLambdaTrace

/-! # Contract control frames after computation of their binder annotation

The comparison's binder need not remain a literal universe. Its forward
history from the original universe supplies exact native typing of the fixed
sort argument at the changed annotation. This retains dependent body checks
at every finite stage. At stage zero, terminal-image transport removes the forward-history premise
entirely. Inferred function comparison at stage zero now supplies the body
check by the pending-control trace theorem.
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

/-- Function computations with a common endpoint supply the body comparison
needed to contract both universe control frames. The common endpoint can
contain wrappers, and no body comparison is assumed. This covers computation
joins; the full inferred case is supplied by the final theorem below. -/
theorem stage_zero_control_frame_pair_of_function_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (HC : env.IsDefEq univs Γ (.sort (.succ u)) C (.sort v))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (hx : env.HasType univs Γ x (.sort w)) (hy : env.HasType univs Γ y (.sort z))
    (hna : ¬ IsProof Γ (.lam C a)) (hnb : ¬ IsProof Γ (.lam C b))
    (RFA : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ C) (proofErase (C :: Γ) a)) out)
    (RFB : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ C) (proofErase (C :: Γ) b)) out)
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
  have HB := (proofErase_stage_zero_lambda_join_compares heq hs hΓ HC.hasType.2 ha
    HC.hasType.2 hb hna hnb RFA RFB (domainMode := false) (bodyMode := mode)).2
  exact stage_zero_converted_control_frame_pair heq hs hΓ hu HC ha hb hx hy HB HX HY

/-- Independently computed function domains and bodies need not meet. A body
comparison under the left computed domain pulls back to the original binder
and supplies the check for paired control-frame contraction. All computation
prefixes may use generated wrappers. The final theorem below removes this
structural-boundary restriction for inferred function comparisons. -/
theorem stage_zero_control_frame_pair_of_computed_bodies
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (HC : env.IsDefEq univs Γ (.sort (.succ u)) C (.sort v))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (hx : env.HasType univs Γ x (.sort w)) (hy : env.HasType univs Γ y (.sort z))
    (hna : ¬ IsProof Γ (.lam C a)) (hnb : ¬ IsProof Γ (.lam C b))
    (RFA : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ C) (proofErase (C :: Γ) a)) (.lam X a'))
    (RFB : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ C) (proofErase (C :: Γ) b)) (.lam Y b'))
    (Hbody : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0)
      (X :: proofEraseCtx Γ) mode a' b')
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
  have HB := stage_zero_computed_lambda_body_compare heq hs hΓ HC.hasType.2 ha hb hna hnb RFA RFB Hbody
  exact stage_zero_converted_control_frame_pair heq hs hΓ hu HC ha hb hx hy HB HX HY

/-- Arbitrary inferred comparison of the two original control functions now
supplies their body comparison. Both paired control frames contract and retain
a comparison in either mode, without a body-check or computation-join premise. -/
theorem stage_zero_control_frame_pair_of_inferred_functions
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (HC : env.IsDefEq univs Γ (.sort (.succ u)) C (.sort v))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (hx : env.HasType univs Γ x (.sort w)) (hy : env.HasType univs Γ y (.sort z))
    (hna : ¬ IsProof Γ (.lam C a)) (hnb : ¬ IsProof Γ (.lam C b))
    (HF : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
      (.lam (proofErase Γ C) (proofErase (C :: Γ) a))
      (.lam (proofErase Γ C) (proofErase (C :: Γ) b)))
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
  have HB₀ := stage_zero_inferred_lambda_body_compare heq hs hΓ HC.hasType.2 ha hb hna hnb HF
  have HB : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx (C :: Γ)) mode (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) := by
    cases mode with
    | false => exact HB₀
    | true => exact HB₀.common
  exact stage_zero_converted_control_frame_pair heq hs hΓ hu HC ha hb hx hy HB HX HY

/-- Common actual Pi typing suffices for control functions with independent
written annotations. Inferred function comparison supplies the reference-body
check, and compared sort arguments let both original raw applications contract.
No equality or computation between the written domains is a separate premise. -/
theorem stage_zero_control_frame_pair_at_common_pi
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (HC : env.IsDefEq univs Γ (.sort (.succ u)) C (.sort v))
    (hf : env.HasType univs Γ (.lam A a) (.forallE C T))
    (hg : env.HasType univs Γ (.lam B b) (.forallE C T))
    (hna : ¬ IsProof Γ (.lam A a)) (hnb : ¬ IsProof Γ (.lam B b))
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C)
    (HF : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A a)) (proofErase Γ (.lam B b)))
    (HX : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) xMode
      (.sort u) (proofErase Γ x))
    (HY : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) yMode
      (.sort u) (proofErase Γ y)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.app (proofErase Γ (.lam A a)) (proofErase Γ x)) (proofErase Γ (a.inst (.sort u))) ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.app (proofErase Γ (.lam B b)) (proofErase Γ y)) (proofErase Γ (b.inst (.sort u))) ∧
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst (.sort u))) (proofErase Γ (b.inst (.sort u))) := by
  have HT : TerminalDomain Γ C := TerminalDomain.sort.convert hΓ HC
  obtain ⟨HCA, ha⟩ := lambda_body_at_reference_pi hΓ HC.hasType.2 hf
  obtain ⟨HCB, hb⟩ := lambda_body_at_reference_pi hΓ HC.hasType.2 hg
  have HB₀ := stage_zero_terminal_lambda_bodies_at_pi heq hs hΓ HC.hasType.2 HT hf hg hna hnb HF
  have HB : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx (C :: Γ)) mode (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) := by
    cases mode with
    | false => exact HB₀
    | true => exact HB₀.common
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, v, HC.hasType.2⟩
  have EA := proofErase_defeqCtx hΓC (IsDefEqCtx.succ .zero HCA) ha
  have EB := proofErase_defeqCtx hΓC (IsDefEqCtx.succ .zero HCB) hb
  have R := stage_zero_converted_control_frame_pair (K := proofErase Γ A) (L := proofErase Γ B)
    heq hs hΓ hu HC ha hb (HC.symm.defeq hx) (HC.symm.defeq hy) HB HX HY
  simpa only [EA, EB, show proofErase Γ (.lam A a) = .lam _ _ from if_neg hna,
    show proofErase Γ (.lam B b) = .lam _ _ from if_neg hnb] using R

end Lean4Lean.VEnv.Strengthening
