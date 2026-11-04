import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructurePiOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaLambdaResidual

/-! # Full native eta on literal lambdas has an annotation residual

A native guard recovered from a literal lambda preserves a forward history
from its written annotation. Exact Pi component extraction supplies this path
even when the guard uses arbitrary earlier structure and function eta stages.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Every selected native Pi domain of a literal lambda is a computation
of its written annotation in the full static structure/function-eta union.
This is exact at the selected domain; no beta cleanup or assigned-type coverage
is assumed. A caller's declared argument domain need not have this property. -/
theorem static_structure_lambda_native_domain_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (R : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) (.forallE X Y)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) X := by
  obtain ⟨C, RC, RP⟩ := R.lam_compute
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨C', hbC, EC⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA hb
    (by simpa only [proofEraseCtx] using RC)
  obtain ⟨v, hC⟩ := hbC.isType henv hΓA
  rw [← EC] at RP
  obtain ⟨_, _, _, _, _, _, RA, _⟩ :=
    proofErase_static_structure_union_pi_components heq hs hΓ hA hC RP
  exact RA

/-- A native eta step on an actual lambda meets a computation changing only
its displayed domain. The eta branch beta-reduces to that exact same lambda;
its original body is retained, even for a proposition-valued domain. -/
theorem static_structure_lambda_eta_component_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hn : ¬ IsProof Γ (.lam A b))
    (R : NativeEtaExpansion (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) out) :
    ∃ sharedA, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) sharedA ∧
      ProofShape.BetaRed out (.lam sharedA (proofErase (A :: Γ) b)) := by
  cases R with
  | @intro X Y v RN SD =>
    have RA := static_structure_lambda_native_domain_origin heq hs hΓ hA hb RN
    have hf := HasType.lam hA hb
    have Ef : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) := if_neg hn
    obtain ⟨D', C', hfD, ED, _⟩ := proofErase_scoped_recovered_pi_descend
      (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hΓ
      (show Ctx.LiftN 0 0 Γ Γ from .zero []) hf
      (by simpa only [ProofShape.liftN_zero, Ef] using RN)
    simp only [ProofShape.liftN_zero] at ED
    obtain ⟨_, hPi⟩ := hfD.isType henv hΓ
    obtain ⟨⟨_, hD⟩, _⟩ := hPi.forallE_inv henv
    have SD' : DomainSort (proofEraseCtx Γ) ((proofErase Γ D').liftN 0) v := by
      simpa only [ProofShape.liftN_zero, ED] using SD
    have hDv := SD'.descend hΓ hΓ (Ctx.LiftN.zero []) hD
    obtain ⟨⟨_, HAD⟩, _⟩ := (hf.uniqU henv hΓ hfD).forallE_inv henv hΓ
    have hAv := hDv.defeqU_l henv hΓ HAD.toU.symm
    exact ⟨X, RA, proofErase_eta_lambda_beta hΓ hAv hb X⟩

/-- The whole literal-lambda/native-eta peak has a common reduct. The short
branch computes only the annotation; the long branch uses only beta. -/
theorem static_structure_lambda_eta_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hn : ¬ IsProof Γ (.lam A b))
    (R : NativeEtaExpansion (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) shared ∧ ProofShape.BetaRed out shared := by
  have E : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) := if_neg hn
  rw [E] at R ⊢
  obtain ⟨sharedA, RA, RB⟩ := static_structure_lambda_eta_component_residual heq hs hΓ hA hb hn R
  exact ⟨_, .lam RA .refl, RB⟩

end Lean4Lean.VEnv.Strengthening
