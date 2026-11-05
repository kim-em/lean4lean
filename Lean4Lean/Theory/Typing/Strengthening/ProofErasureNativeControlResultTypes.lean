import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalNativePiComparison
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageZeroSortExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointImageComputation

/-! # Native result-type comparisons for paired universe control arguments

The selected codomains need not have the same annotation or universe. Whole-Pi
comparison supplies their check at the fixed sort; each original argument's
return computation passes through its selected codomain. Functions may have
arbitrary heads, with no lambda exposure premise.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : PureObservation.Definitions}

/-- Computation of an actual application argument passes through the exact
codomain selected by native Pi recovery. Typed replay and uniqueness align the
argument with the selected domain; no new recovery of the argument is needed. -/
theorem stage_zero_native_result_argument_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE C T)) (hx : env.HasType univs Γ x C)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE X Y))
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ x) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (Y.inst (proofErase Γ x)) (Y.inst out) := by
  obtain ⟨P, hfP, EP⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_stage_descent heq hs 0) hΓ hf RF
  obtain ⟨A, B, rfl, _, _, EB⟩ := erase_forallE_inv EP
  obtain ⟨⟨u, hA⟩, _, hB⟩ := (hfP.isType henv hΓ).forallE_inv henv
  have hxA := argument_at_displayed_domain hΓ hf hfP hx
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have WS := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hxA
  have H := proofErase_compute_subst_images_of_renaming
    (erased_static_structure_eta_expansion_stage_rename heq hs 0)
    hΓ WS hB (erasedSubstAgreement_one hΓA hxA)
    (τ := ProofShape.Subst.one out) (fun i => by
      cases i with
      | zero => exact RX
      | succ i => exact .refl)
  simpa only [EB, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H

/-- For paired arguments checked against a fixed universe, comparison of native
Pi outputs compares their exact instantiated result types. The two arguments
and both selected domains may differ; no result-type check, function-head
exposure or computation between written annotations is assumed. This concerns
the selected result types before any independent final native conversion tails. -/
theorem stage_zero_native_control_result_types_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (HC : env.IsDefEq univs Γ (.sort (.succ u)) C (.sort v))
    (hf : env.HasType univs Γ f (.forallE C T))
    (hg : env.HasType univs Γ g (.forallE C T))
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE X Y))
    (RG : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ g) (.forallE Z W))
    (HT : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode
      (.forallE X Y) (.forallE Z W))
    (HX : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) xMode
      (.sort u) (proofErase Γ x))
    (HY : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) yMode
      (.sort u) (proofErase Γ y)) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
      (Y.inst (proofErase Γ x)) (W.inst (proofErase Γ y)) := by
  have hp : env.HasType univs Γ (.sort u) C := HC.defeq (.sort hu)
  have EP : proofErase Γ (.sort u) = .sort u := if_neg (not_isProof_of_sort hΓ (HasType.sort hu))
  have HTerm : TerminalDomain Γ C := TerminalDomain.sort.convert hΓ HC
  have HI := stage_zero_terminal_native_application_types_compare heq hs hΓ HC.hasType.2 HTerm
    hf hg hp RF RG HT
  rw [EP] at HI
  have RX := stage_zero_compared_sort_returns heq hs hΓ hu (HC.symm.defeq hx) HX
  have RY := stage_zero_compared_sort_returns heq hs hΓ hu (HC.symm.defeq hy) HY
  exact .compute (stage_zero_native_result_argument_compute heq hs hΓ hf hx RF RX)
    (stage_zero_native_result_argument_compute heq hs hΓ hg hy RG RY) HI

end Lean4Lean.VEnv.Strengthening
