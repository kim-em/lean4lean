import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedControlFrame
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedCarrierTypeChecking

/-! # Contract paired control applications for all three application rules

A selected native or computed function domain supplies an actual carrier typing
for its argument. At universe-valued control arguments, carrier checking then
reduces to ordinary comparison. A retained history from the fixed sort feeds
that comparison into exact sort return and paired contraction.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : PureObservation.Definitions}

/-- Native or computed domain selection for a universe-domain function turns
its carrier argument guard into ordinary common checking at the same stage.
The selected raw domain need not be a literal sort. -/
theorem stage_zero_control_carrier_arguments_checked
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HC : env.IsDefEq univs Γ (.sort w) C (.sort v))
    (hf : env.HasType univs Γ f (.forallE C T))
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C)
    (HR : (∃ Y, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (proofErase Γ f) (.forallE X Y)) ∨
      (∃ body, ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0)
        (proofEraseCtx Γ) (proofErase Γ f) (.lam X body)))
    (HX : ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) X (proofErase Γ x) (proofErase Γ y)) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) true
      (proofErase Γ x) (proofErase Γ y) := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
    erased_static_structure_eta_expansion_stage_descent heq hs 0
  have Hselected : ∃ A, env.HasType univs Γ x A ∧ proofErase Γ A = X := by
    rcases HR with ⟨Y, RN⟩ | ⟨body, RF⟩
    · obtain ⟨P, hfP, EP⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf RN
      obtain ⟨A, B, rfl, _, EA, _⟩ := erase_forallE_inv EP
      exact ⟨A, argument_at_displayed_domain hΓ hf hfP hx, EA⟩
    · obtain ⟨f', HF, Ef⟩ := proofErase_scoped_compute_realize hstep hΓ hf rfl rfl RF
      obtain ⟨A, b, rfl, _, EA, _⟩ := erase_lam_inv Ef
      obtain ⟨⟨u, hA⟩, B, hb⟩ := HF.hasType.2.lam_inv henv hΓ
      exact ⟨A, argument_at_displayed_domain hΓ HF.hasType.2 (HasType.lam hA hb) hx, EA⟩
  obtain ⟨A, hxA, EA⟩ := Hselected
  exact proofErase_computed_carrier_types_checked hstep hΓ (HC.symm.defeq hx) (HC.symm.defeq hy)
    (.inl hxA) (by simpa only [EA] using HX)

/-- All three structural application premises suffice for paired contraction
when the left control argument retains its forward history from the fixed
sort. The original functions may have independent written annotations; no
separate body check, annotation join or right argument history is needed.
Outer comparison computation still requires retention of this left history. -/
theorem stage_zero_control_application_pair
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (HC : env.IsDefEq univs Γ (.sort (.succ u)) C (.sort v))
    (hf : env.HasType univs Γ (.lam A a) (.forallE C T))
    (hg : env.HasType univs Γ (.lam B b) (.forallE C T))
    (hna : ¬ IsProof Γ (.lam A a)) (hnb : ¬ IsProof Γ (.lam B b))
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.sort u) (proofErase Γ x))
    (HF : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A a)) (proofErase Γ (.lam B b)))
    (Harg : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) true
        (proofErase Γ x) (proofErase Γ y) ∨
      (∃ X Y, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ (.lam A a)) (.forallE X Y) ∧
        ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D 0)
          (proofEraseCtx Γ) X (proofErase Γ x) (proofErase Γ y)) ∨
      (∃ X body, ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ (.lam A a)) (.lam X body) ∧
        ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D 0)
          (proofEraseCtx Γ) X (proofErase Γ x) (proofErase Γ y))) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.app (proofErase Γ (.lam A a)) (proofErase Γ x)) (proofErase Γ (a.inst (.sort u))) ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.app (proofErase Γ (.lam B b)) (proofErase Γ y)) (proofErase Γ (b.inst (.sort u))) ∧
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst (.sort u))) (proofErase Γ (b.inst (.sort u))) := by
  have Hxy : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) true
      (proofErase Γ x) (proofErase Γ y) := by
    rcases Harg with H | ⟨X, Y, RN, H⟩ | ⟨X, body, RF, H⟩
    · exact H
    · exact stage_zero_control_carrier_arguments_checked heq hs hΓ HC hf hx hy (.inl ⟨Y, RN⟩) H
    · exact stage_zero_control_carrier_arguments_checked heq hs hΓ HC hf hx hy (.inr ⟨body, RF⟩) H
  exact stage_zero_control_frame_pair_at_common_pi heq hs hΓ hu HC hf hg hna hnb hx hy HF
    (.compute RX .refl (.leaf (.refl (mode := true)))) (.compute RX .refl Hxy)

end Lean4Lean.VEnv.Strengthening
