import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConvertedAnchoredInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructuralDomainBoundary

/-! # Body substitution by converting the structural eta example's selected type

The exact lambda from StructuralDomainBoundary has no anchored path at its
assigned type. A recursive neutral binder conversion reaches its written type,
where its literal type-valued body supplies a finite anchored path.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private context native assigned nativeRaw assignedRaw context_wf native_typed
  types_equal erasures
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
variable [Params]

private theorem erase_pi_sort
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hv : v.WF univs) :
    proofErase Γ (.forallE A (.sort v)) = .forallE (proofErase Γ A) (.sort v) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  rw [show proofErase Γ (.forallE A (.sort v)) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hA (HasType.sort hv))),
    show proofErase (A :: Γ) (.sort v) = .sort v from
      if_neg (not_isProof_of_sort hΓA (HasType.sort hv))]

private theorem image_conversion (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ u, env.IsDefEq univs (context Γ)
      (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero)))
      (.forallE (.forallE native (.sort .zero)) (.sort (.succ .zero))) (.sort u) ∧
    NeutralTypeChange 0
      (proofErase (context Γ) (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero))))
      (proofErase (context Γ) (.forallE (.forallE native (.sort .zero)) (.sort (.succ .zero)))) ∧
    env.HasType univs (context Γ) (.lam (.forallE native (.sort .zero)) (.sort .zero))
      (.forallE (.forallE native (.sort .zero)) (.sort (.succ .zero))) ∧
    AnchoredFamilyRecovery D 0 (context Γ) (.lam (.forallE native (.sort .zero)) (.sort .zero))
      (proofErase (context Γ) (.forallE (.forallE native (.sort .zero)) (.sort (.succ .zero)))) 1 := by
  have hC := context_wf hΓ
  have hX := HasType.forallE (Γ := context Γ) native_typed (HasType.sort (l := .zero) (by trivial))
  have hY := HasType.forallE (Γ := context Γ) types_equal.hasType.1 (HasType.sort (l := .zero) (by trivial))
  have Hdom := IsDefEq.forallEDF (Γ := context Γ) types_equal (HasType.sort (l := .zero) (by trivial))
  have HTU := IsDefEq.forallEDF Hdom (HasType.sort (l := .succ .zero) (by trivial))
  have hp := HasType.lam hX (HasType.sort (l := .zero) (by trivial))
  have HR : AnchoredFamilyRecovery D 0 (context Γ)
      (.lam (.forallE native (.sort .zero)) (.sort .zero))
      (proofErase (context Γ) (.forallE (.forallE native (.sort .zero)) (.sort (.succ .zero)))) 1 := by
    rw [erase_pi_sort hC hX (by trivial)]
    exact .lam (.type (HasType.sort (by trivial)))
  have HT : NeutralTypeChange 0
      (proofErase (context Γ) (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero))))
      (proofErase (context Γ) (.forallE (.forallE native (.sort .zero)) (.sort (.succ .zero)))) := by
    rw [erase_pi_sort hC hY (by trivial), erase_pi_sort hC hX (by trivial),
      erase_pi_sort hC types_equal.hasType.1 (by trivial), erase_pi_sort hC native_typed (by trivial),
      (erasures hΓ).1, (erasures hΓ).2]
    exact .forallE (.forallE (.neutral (k := 0) (i := 1) (j := 1)
      (args := [.lam (.sort .zero) (.app (.bvar 3) (.bvar 0))]) (args' := [.bvar 2])
      (by omega) (by omega)) .refl) .refl
  exact ⟨_, HTU, HT, hp, HR⟩

/-- The Pi-wrapped eta lambda transports every common-typed stage-zero body
comparison, including all nested carriers and computed-domain applications.
Its assigned-type recovery/exposure failures remain valid. This proves shared
argument instantiation for this example, not unrestricted endpoint beta stability. -/
theorem proofErase_computed_joint_structural_eta_lambda_inst
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs
      (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero)) :: context Γ) a A)
    (hb : env.HasType univs
      (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero)) :: context Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0)
      (proofEraseCtx (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero)) :: context Γ)) mode
      (proofErase (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero)) :: context Γ) a)
      (proofErase (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero)) :: context Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (context Γ)) mode
      (proofErase (context Γ) (a.inst (.lam (.forallE native (.sort .zero)) (.sort .zero))))
      (proofErase (context Γ) (b.inst (.lam (.forallE native (.sort .zero)) (.sort .zero)))) := by
  obtain ⟨_, HTU, HT, hp, HR⟩ := image_conversion (D := D) hΓ
  exact proofErase_computed_joint_zero_compare_inst_converted_anchored hs (context_wf hΓ) HTU HT hp HR ha hb H

/-- The same structural eta image instantiates first-layer computations,
including generated singleton and Eq prefixes with recursive guards. -/
theorem proofErase_computed_joint_converted_structural_eta_compute_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs
      (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero)) :: context Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D 1)
      (proofEraseCtx (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero)) :: context Γ))
      (proofErase (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero)) :: context Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (context Γ))
      (proofErase (context Γ) (e.inst (.lam (.forallE native (.sort .zero)) (.sort .zero))))
      (out.inst (proofErase (context Γ) (.lam (.forallE native (.sort .zero)) (.sort .zero)))) := by
  obtain ⟨_, HTU, HT, hp, HR⟩ := image_conversion (D := D) hΓ
  exact proofErase_computed_joint_one_compute_inst_converted_anchored
    heq hs (context_wf hΓ) HTU HT hp HR he R

end Lean4Lean.VEnv.Strengthening
