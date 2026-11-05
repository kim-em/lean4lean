import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeHeadSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeFreshTypeBoundary

/-! # Native substitution can expose an uncertifiable new cut

Substitution preserves certificates of existing head reductions. It need not
certify newly exposed beta redexes: a native function image may recover a Pi
whose domain has computed away from the lambda's written annotation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- A computed domain supplies exact native recovery for the identity function
at the correspondingly computed Pi. Its written annotation is still the old
domain. A retained inhabitant makes the identity's bound variable retained. -/
theorem native_identity_function_computed_domain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x A) (hn : ¬ IsProof Γ x)
    (HAC : env.IsDefEq univs Γ A C (.sort u))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ C)) :
    env.HasType univs Γ (.lam A (.bvar 0)) (.forallE C C.lift) ∧
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A (.bvar 0))) (proofErase Γ (.forallE C C.lift)) := by
  have hA := HAC.hasType.1
  have hC := HAC.hasType.2
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, u, hC⟩
  have hv : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have hf := HasType.lam hA hv
  have HE := IsDefEq.forallEDF HAC (HAC.weakN henv Ctx.LiftN.one)
  have hfC : env.HasType univs Γ (.lam A (.bvar 0)) (.forallE C C.lift) := HE.defeq hf
  have hnv : ¬ IsProof (A :: Γ) (.bvar 0) := by
    intro hp
    have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
    have H := (isProof_subst hΓ W hv).2 hp
    simpa [VExpr.subst, VExpr.Subst.one, VExpr.Subst.liftN, VExpr.Subst.cons] using hn H
  have hnf : ¬ IsProof Γ (.lam A (.bvar 0)) := by
    apply not_isProof_fn hΓ hf hx
    intro hp
    have H := isProof_congr hΓ (nativeIdentityExpansion_equal hx)
    exact hn (H.1 hp)
  have EF : proofErase Γ (.lam A (.bvar 0)) = .lam (proofErase Γ A) (.bvar 0) := by
    rw [show proofErase Γ (.lam A (.bvar 0)) = .lam _ _ from if_neg hnf,
      show proofErase (A :: Γ) (.bvar 0) = .bvar 0 from if_neg hnv]
  have hPi := HasType.forallE hC (hC.weakN henv Ctx.LiftN.one)
  have EP : proofErase Γ (.forallE C C.lift) =
      .forallE (proofErase Γ C) ((proofErase Γ C).liftN 1) := by
    rw [show proofErase Γ (.forallE C C.lift) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hPi)]
    rw [proofErase_liftN hΓ hΓC Ctx.LiftN.one hC]
  have hrename : ∀ {Δ Δ' a b τ}, ErasedStaticStructureEtaExpansionUnion D Δ a b →
      ContextRenaming Δ Δ' τ →
      ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst τ) (b.subst τ) := by
    intro Δ Δ' a b τ ⟨n, H⟩ W
    exact ⟨n, erased_static_structure_eta_expansion_stage_rename heq hs n H W⟩
  have RL := RA.rename hrename (ContextRenaming.of_liftN hΓ hΓA Ctx.LiftN.one)
  simp only [subst_bvar_liftN, proofEraseCtx] at RL
  refine ⟨hfC, ?_⟩
  rw [EF, EP]
  exact (ScopedTypeRecovery.lam (ScopedTypeRecovery.bvar (i := 0))).convert (.forallE RA RL)

/-- Even an exact native function image can expose a new identity beta cut
outside NativeHeadBeta. The argument itself has exact native recovery at the
function's selected domain. The obstruction is the distinct written domain,
not an untyped image or a failure of native substitution for existing cuts.
The environment hypothesis is the same positive empty structure used by the
existing exact-recovery boundary; this is not a strengthening counterexample. -/
theorem native_substitution_created_cut_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ A C x, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ x A ∧ env.HasType univs Γ x C ∧
      env.HasType univs Γ (.lam A (.bvar 0)) (.forallE C C.lift) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ x) (proofErase Γ C) ∧
      Ctx.SubstEq env univs Γ (VExpr.Subst.one (.lam A (.bvar 0)))
        (VExpr.Subst.one (.lam A (.bvar 0))) (.forallE C C.lift :: Γ) ∧
      NativeImageTransport.Images (ErasedStaticStructureEtaExpansionUnion D)
        (.forallE C C.lift :: Γ) Γ (ProofShape.Subst.one (proofErase Γ (.lam A (.bvar 0)))) ∧
      (VExpr.app (.bvar 0) x.lift).inst (.lam A (.bvar 0)) = .app (.lam A (.bvar 0)) x ∧
      ¬ NativeHeadBeta D Γ (.app (.lam A (.bvar 0)) x) x := by
  obtain ⟨Γ, x, A, hΓ, ht, hn, Hno, Hcommon⟩ := descending_native_exact_coverage_failure
    (erased_static_structure_eta_expansion_union_descent heq hs) hi hp hx hz hS
  obtain ⟨shared, RN, RA⟩ := Hcommon D
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) shared := RN.mono (fun H => ⟨1, erased_unit_into_static_structure_eta_stage 1 H⟩)
  have RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) shared := RA.mono (fun H => ⟨1, erased_unit_into_static_structure_eta_stage 1 H⟩)
  obtain ⟨v, hA⟩ := ht.isType henv hΓ
  obtain ⟨C, HAC, EC⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hA rfl rfl RA
  rw [← EC] at RN RA
  obtain ⟨hf, RF⟩ := native_identity_function_computed_domain heq hs hΓ ht hn HAC RA
  obtain ⟨w, hG⟩ := hf.isType henv hΓ
  have hΓG : OnCtx (.forallE C C.lift :: Γ) (env.IsType univs) := ⟨hΓ, w, hG⟩
  refine ⟨Γ, A, C, x, hΓ, ht, HAC.defeq ht, hf, RN,
    (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := .lam A (.bvar 0)) (A₀ := .forallE C C.lift)).substEq hΓG hf, NativeImageTransport.Images.inst RF, ?_, ?_⟩
  · simp only [VExpr.inst, VExpr.instVar, Nat.lt_irrefl, ↓reduceIte,
      VExpr.liftN_zero, VExpr.inst_lift]
  · intro H
    exact Hno (H.recovery heq hs hΓ (nativeIdentityExpansion_equal ht).hasType.1
      ((proofErase_identity_wrapper_native (Step := ErasedStaticStructureEtaExpansionStage D 0) hΓ ht hn).mono (fun H => ⟨0, H⟩)))

end Lean4Lean.VEnv.Strengthening
