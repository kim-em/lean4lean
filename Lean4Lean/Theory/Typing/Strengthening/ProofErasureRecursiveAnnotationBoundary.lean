import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveAnnotationChecking
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveFamilyCastBoundary

/-! # Nonjoining lambda annotations with inferred future checking

The nonjoining endpoint types from the cast example are now written lambda
domains. Their recursive comparison gives inferred checking, while every
putative computation join of the lambdas would join the domains as well.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

omit [Params] in
private theorem lam_domain_path
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ (.lam A b) out) :
    ∃ A' b', out = .lam A' b' ∧ ScopedCompute Step Δ A A' := by
  generalize E : ProofShape.lam A b = source at R
  induction R generalizing A b with
  | base H => exact (E ▸ hhead H).elim
  | beta H =>
    cases E
    obtain ⟨A', b', HE, HA, _⟩ := H.lam_inv
    exact ⟨A', b', HE, .beta HA⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨A₁, b₁, rfl, RA⟩ := ih₁ E
    obtain ⟨A₂, b₂, HE, RB⟩ := ih₂ rfl
    exact ⟨A₂, b₂, HE, RA.trans RB⟩
  | lam RA _ => cases E; exact ⟨_, _, rfl, RA⟩
  | app | proj | forallE => cases E

/-- Actual same-body lambdas have a common Pi type and inferred future
comparison, although neither their written domains nor the lambdas have a
computation join in the full joint union. Thus the inferred result is not
obtained by finding a stronger endpoint computation join. -/
theorem recursive_annotation_inferred_without_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' A C u,
      OnCtx Γ' (env.IsType univs) ∧
      env.HasType univs Γ' A (.sort u) ∧ env.HasType univs Γ' C (.sort u) ∧
      env.HasType univs Γ' (.lam A (.sort .zero)) (.forallE A (.sort (.succ .zero))) ∧
      env.HasType univs Γ' (.lam C (.sort .zero)) (.forallE A (.sort (.succ .zero))) ∧
      BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ false) (proofEraseCtx Γ')
        (proofErase Γ' (.lam A (.sort .zero))) (proofErase Γ' (.lam C (.sort .zero))) ∧
      (¬ ∃ shared, ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' A) shared ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' C) shared) ∧
      ¬ ∃ shared,
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' (.lam A (.sort .zero))) shared ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' (.lam C (.sort .zero))) shared := by
  obtain ⟨Γ', u, A, C, _, _, hΓ', _, hA, hC, _, _, _, HA, _, Hno⟩ :=
    recursive_family_cast_nonjoining_endpoints (D := D) heq hEq hΓ
  have hb : env.HasType univs (A :: Γ') (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hleft := HasType.lam hA hb
  obtain ⟨hright, H⟩ := recursive_lambda_annotation_future heq hs hregistry hΓ' hA hC hb HA
  refine ⟨Γ', A, C, u, hΓ', hA, hC, hleft, hright, H, Hno, ?_⟩
  rintro ⟨out, RL, RR⟩
  rw [show proofErase Γ' (.lam A (.sort .zero)) = .lam _ _ from
    if_neg (not_isProof_function_to_sort hΓ' hleft)] at RL
  rw [show proofErase Γ' (.lam C (.sort .zero)) = .lam _ _ from
    if_neg (not_isProof_function_to_sort hΓ' hright)] at RR
  obtain ⟨A', b, rfl, RA⟩ := lam_domain_path erased_joint_union_head RL
  obtain ⟨C', c, E, RC⟩ := lam_domain_path erased_joint_union_head RR
  cases E
  exact Hno ⟨A', RA, RC⟩

omit [Params] in
/-- The separation holds in every actual well-formed canonical-Eq environment.
The empty starting context, definition soundness, Eq rigidity and registry
agreement are supplied here rather than assumed as abstract interfaces. -/
theorem EnvironmentCore.recursive_annotation_inferred_without_join
    {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq) (U : Nat) :
    letI := henv.params U
    ∃ Γ A C u,
      OnCtx Γ (env.IsType U) ∧
      env.HasType U Γ A (.sort u) ∧ env.HasType U Γ C (.sort u) ∧
      env.HasType U Γ (.lam A (.sort .zero)) (.forallE A (.sort (.succ .zero))) ∧
      env.HasType U Γ (.lam C (.sort .zero)) (.forallE A (.sort (.succ .zero))) ∧
      BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion definitions) Δ false) (proofEraseCtx Γ)
        (proofErase Γ (.lam A (.sort .zero))) (proofErase Γ (.lam C (.sort .zero))) ∧
      (¬ ∃ shared, ScopedCompute (ErasedJointUnion definitions) (proofEraseCtx Γ) (proofErase Γ A) shared ∧
        ScopedCompute (ErasedJointUnion definitions) (proofEraseCtx Γ) (proofErase Γ C) shared) ∧
      ¬ ∃ shared,
        ScopedCompute (ErasedJointUnion definitions) (proofEraseCtx Γ) (proofErase Γ (.lam A (.sort .zero))) shared ∧
        ScopedCompute (ErasedJointUnion definitions) (proofEraseCtx Γ) (proofErase Γ (.lam C (.sort .zero))) shared := by
  letI := henv.params U
  exact Strengthening.recursive_annotation_inferred_without_join heq sound rfl
    (no_rigid (heq.rigid henv)) (Γ := []) (by trivial)

end Lean4Lean.VEnv.Strengthening
