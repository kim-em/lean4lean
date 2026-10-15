import Lean4Lean.Theory.Typing.Strengthening.ProofErasureApplicationStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierApplicationExample
import Lean4Lean.Theory.Typing.Strengthening.EqRecResultBoundary

/-! # Recovered neutral applications now guard actual Eq computation

The endpoints f x and f y are propositions for distinct unit variables x and y.
They have no old structure-carrier guard at any stage. Recursive recovered
checking certifies them at stage zero and exposes a Pi payload at stage one.
No all-path computational separation from the older stages is asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- The old neutral-application root embeds in the enlarged recursive language
at the same initial stage. It remains usable in both checking modes. -/
theorem recovered_neutral_application_check
    (H : ProofShape.RecoveredCarrierApplication (fun _ _ => False)
      (ErasedStructureSingletonStage D 0) Δ a b) :
    ProofShape.ApplicationCompare (ErasedApplicationStage D 0) Δ mode a b := by
  have H' : ProofShape.ScopedRecoveredCarrierApplication (ErasedApplicationStage D 0)
      (ErasedApplicationStage D 0) Δ a b := H.scoped (fun H => H.elim)
  exact H'.application

/-- Recovered application comparisons are available recursively beneath both
Pi annotations, with the codomain's actual binder context retained. -/
theorem recovered_application_pi_check
    (HA : ProofShape.ScopedRecoveredCarrierApplication Step Step Δ A A')
    (HB : ProofShape.ScopedRecoveredCarrierApplication Step Step (A :: Δ) B B') :
    ProofShape.ApplicationCompare Step Δ mode (.forallE A B) (.forallE A' B') :=
  .forallE HA.application HB.application

/-- A canonical-Eq recursor over the propositions f x and f y computes to a
Pi at the new stage one. Their explicit universe carrier has no old guard at
any structure-singleton stage, even though those stages are all retained in
the enlarged family. The result concerns the guard and new computation, not
absence of every alternative old computation. -/
theorem neutral_application_pi_exposure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family levels) (.sort (.succ u))) :
    ∃ Γ e, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ e (.sort (.succ (.succ .zero))) ∧
      env.IsDefEq univs Γ e (.forallE (.sort (.succ .zero)) (.sort (.succ .zero)))
        (.sort (.succ (.succ .zero))) ∧
      ProofShape.ScopedCompute (ErasedApplicationStage D 1) (proofEraseCtx Γ)
        (proofErase Γ e) (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) ∧
      ProofShape.ApplicationCompare (ErasedApplicationStage D 0) (proofEraseCtx Γ) true
        (proofErase Γ (.app (.bvar 2) (.bvar 0))) (proofErase Γ (.app (.bvar 2) (.bvar 1))) ∧
      ∀ stage, ¬ ProofShape.StructureCarrierGuard (ErasedStructureSingletonStage D stage)
        (proofEraseCtx Γ) (proofErase Γ (.sort .zero))
        (proofErase Γ (.app (.bvar 2) (.bvar 0))) (proofErase Γ (.app (.bvar 2) (.bvar 1))) := by
  obtain ⟨Γ, hΓ, hP, hQ, Hroot, HN⟩ := recovered_neutral_application_context (D := D) hi hp hx hf hS
  let P := VExpr.app (.bvar 2) (.bvar 0)
  let Q := VExpr.app (.bvar 2) (.bvar 1)
  have HC : ProofShape.ApplicationCompare (ErasedApplicationStage D 0) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q) := recovered_neutral_application_check Hroot
  have HPQ : env.IsDefEq univs Γ P Q (.sort .zero) :=
    ((proofErase_application_compare_reflect (erased_application_stage_descent heq hs 0)
      hΓ hP hQ HC).1 ⟨_, HasType.sort (by trivial)⟩).of_l henv hΓ hP
  let q := eqReflApp (.succ .zero) (.sort .zero) P
  have hprop : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q) :=
    (IsDefEq.eqApp_r heq (by trivial) hprop hP HPQ).defeq
      (HasType.eqReflApp heq (by trivial) hprop hP)
  let F := VExpr.forallE (.sort (.succ .zero)) (.sort (.succ .zero))
  let X := VExpr.sort (.succ (.succ .zero))
  have hF : env.HasType univs Γ F X :=
    (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq
      (HasType.forallE (HasType.sort (by trivial)) (HasType.sort (by trivial)))
  let M := constantEqMotive (.succ .zero) (.sort .zero) P X
  let e := eqRecApp (.succ (.succ (.succ .zero))) (.succ .zero) (.sort .zero) P M F Q q
  have he : env.HasType univs Γ e X := constant_eqRec_typed henv heq (by trivial) (by trivial)
    hΓ hprop hP (HasType.sort (by trivial)) hF hQ hq
  have HE : env.IsDefEq univs Γ e F X := eqRecApp_simAt henv heq hΓ ⟨_, HPQ⟩ _ he
  have R := proofErase_application_full_forward heq hs hΓ he HC
  have EF : proofErase Γ F = .forallE (.sort (.succ .zero)) (.sort (.succ .zero)) := by
    rw [show proofErase Γ F = .forallE (proofErase Γ (.sort (.succ .zero)))
      (proofErase (.sort (.succ .zero) :: Γ) (.sort (.succ .zero))) from
        if_neg (not_isProof_of_sort hΓ hF)]
    have hΓT : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) :=
      ⟨hΓ, _, HasType.sort (by trivial)⟩
    rw [show proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) from
      if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial))),
      show proofErase (.sort (.succ .zero) :: Γ) (.sort (.succ .zero)) = .sort (.succ .zero) from
      if_neg (not_isProof_of_sort hΓT (HasType.sort (by trivial)))]
  rw [EF] at R
  exact ⟨Γ, e, hΓ, he, HE, R, HC, HN⟩

end Lean4Lean.VEnv.Strengthening
