import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedGuardedSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureUnitPrefixExample

/-! # Retaining substituted parameters beneath guarded domain computation

The source lambda annotation computes through a structure-singleton stage to
Prop, while its body returns the substituted parameter. The two image terms may
have no computation join. Both source typing and the full scoped certificate
are constructed explicitly before paired instantiation is applied.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- An actual guarded type computation can change the written lambda domain
while the body retains the substituted parameter. Image comparison is inferred;
no recovery or join is required for either image. -/
theorem carrier_aligned_guarded_parameter_bodies
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HE : env.IsDefEq univs Γ e (.sort .zero) (.sort (.succ .zero)))
    (R : ScopedCompute (ErasedStructureSingletonUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (proofErase Γ (.sort .zero)))
    (HX : CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) false
      (proofErase Γ x) (proofErase Γ y)) :
    ∃ T, env.HasType univs (A :: Γ) (.lam e.lift (.bvar 1)) T ∧
      env.HasType univs (A :: Γ) (.lam (.sort .zero) (.bvar 1)) T ∧
      ScopedCompare (ErasedStructureSingletonUnion D) (proofEraseCtx (A :: Γ)) false
        (proofErase (A :: Γ) (.lam e.lift (.bvar 1)))
        (proofErase (A :: Γ) (.lam (.sort .zero) (.bvar 1))) ∧
      CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) false
        (proofErase Γ (.lam e x.lift)) (proofErase Γ (.lam (.sort .zero) y.lift)) := by
  have HE' : env.IsDefEq univs (A :: Γ) e.lift (.sort .zero) (.sort (.succ .zero)) := HE.weak henv
  have hb : env.HasType univs (e.lift :: A :: Γ) (.bvar 1) A.lift.lift := .bvar (.succ .zero)
  have hc : env.HasType univs (.sort .zero :: A :: Γ) (.bvar 1) A.lift.lift := .bvar (.succ .zero)
  have HL := IsDefEq.lamDF HE' hb
  have hctx := IsDefEqCtx.succ .zero HE'.symm
  have Ebody := proofErase_defeqCtx (Γ₁ := .sort .zero :: A :: Γ) ⟨hΓA, _, HE'.hasType.2⟩ hctx hc
  have R' := R.subst (erased_structure_singleton_union_subst heq hs)
    (ContextRenaming.of_liftN hΓA.1 hΓA Ctx.LiftN.one).interpretation
  simp only [subst_bvar_liftN] at R'
  rw [← proofErase_liftN hΓA.1 hΓA Ctx.LiftN.one HE.hasType.1,
    ← proofErase_liftN hΓA.1 hΓA Ctx.LiftN.one HE.hasType.2] at R'
  have HC : ScopedCompare (ErasedStructureSingletonUnion D) (proofEraseCtx (A :: Γ)) false
      (proofErase (A :: Γ) (.lam e.lift (.bvar 1)))
      (proofErase (A :: Γ) (.lam (.sort .zero) (.bvar 1))) := by
    by_cases hp : IsProof (A :: Γ) (.lam e.lift (.bvar 1))
    · rw [proofErase_eq_proof.2 hp,
        proofErase_eq_proof.2 (isProof_of_common_type hΓA HL.hasType.1 HL.hasType.2 hp)]
      exact .leaf .refl
    · have hn : ¬ IsProof (A :: Γ) (.lam (.sort .zero) (.bvar 1)) :=
        fun hp' => hp (isProof_of_common_type hΓA HL.hasType.2 HL.hasType.1 hp')
      rw [show proofErase (A :: Γ) (.lam e.lift (.bvar 1)) = .lam _ _ from if_neg hp,
        show proofErase (A :: Γ) (.lam (.sort .zero) (.bvar 1)) = .lam _ _ from if_neg hn, Ebody]
      exact .lam (.compute R' .refl (.leaf .refl)) (.leaf .refl)
  refine ⟨_, HL.hasType.1, HL.hasType.2, HC, ?_⟩
  have H := proofErase_carrier_aligned_guarded_paired_inst heq hs hΓA hx hy HL.hasType.1 HL.hasType.2 HX HC
  simpa [VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.inst_liftN] using H

/-- A canonical-Eq prefix at a positive fieldless structure supplies a concrete
stage-one annotation computation. Every inferred-related pair of typed images
can be retained beneath that annotation and its Prop reduct. The example asserts
actual guarded coverage, not exclusion from all alternative core computations. -/
theorem carrier_aligned_guarded_unit_parameter_example
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ∃ Γ e, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ e (.sort (.succ .zero)) ∧
      env.IsDefEq univs Γ e (.sort .zero) (.sort (.succ .zero)) ∧
      ScopedCompute (ErasedStructureSingletonStage D 1) (proofEraseCtx Γ)
        (proofErase Γ e) (.sort .zero) ∧
      ∀ {A x y}, OnCtx (A :: Γ) (env.IsType univs) →
        env.HasType univs Γ x A → env.HasType univs Γ y A →
        CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) false
          (proofErase Γ x) (proofErase Γ y) →
        CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) false
          (proofErase Γ (.lam e x.lift)) (proofErase Γ (.lam (.sort .zero) y.lift)) := by
  obtain ⟨Γ, e, hΓ, he, HE, R, _⟩ := unit_neutral_sort_exposure (D := D) heq hi hp hx hf hS
  have R := R.mono (erased_unit_singleton_into_structure 1)
  refine ⟨Γ, e, hΓ, he, HE, R, ?_⟩
  intro A x y hΓA hx hy HX
  have RP : proofErase Γ (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓ HE.hasType.2)
  obtain ⟨_, _, _, _, H⟩ := carrier_aligned_guarded_parameter_bodies heq hs hΓA hx hy HE
    (by rw [RP]; exact R.mono (fun H => ⟨1, H⟩)) HX
  exact H

end Lean4Lean.VEnv.Strengthening
