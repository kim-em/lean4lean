import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveCastJoins

/-! # Lambda annotation repair from recursive domain joins

The lambdas need no explicit cast wrapper. A recursive computation join of
their annotations constructs their common typing and literal erased join.
Arbitrary typed consumers may then use either lambda, retaining computation
joins and inferred comparisons after newly created beta reductions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- Joined written domains align same-body lambdas. Actual type conversion,
body-erasure agreement and the new lambda's common typing are all constructed
from the two domain paths. Proof-valued lambdas are included. -/
theorem recursive_lambda_annotation_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (RA : RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ A) shared)
    (RC : RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ C) shared) :
    env.HasType univs Γ (.lam C b) (.forallE A B) ∧
    ∃ out, RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ (.lam A b)) out ∧
      RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ (.lam C b)) out := by
  have HAC := RA.join_defeq heq hs hregistry hΓ hA hC RC
  have HL := IsDefEq.lamDF HAC hb
  refine ⟨HL.hasType.2, ?_⟩
  by_cases hp : IsProof Γ (.lam A b)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HL).1 hp)]
    exact ⟨.proof, .core .refl, .core .refl⟩
  have hpc : ¬ IsProof Γ (.lam C b) := fun H => hp ((isProof_congr hΓ HL).2 H)
  have EB := proofErase_defeqCtx (Γ₁ := A :: Γ) ⟨hΓ, u, hA⟩
    (IsDefEqCtx.succ .zero HAC) hb
  rw [show proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b)
    from if_neg hp, show proofErase Γ (.lam C b) = .lam (proofErase Γ C) (proofErase (C :: Γ) b)
    from if_neg hpc, ← EB]
  exact ⟨.lam shared (proofErase (A :: Γ) b), .lam RA (.core .refl), .lam RC (.core .refl)⟩

/-- Annotation repair propagates through any typed consumer, retaining a
recursive computation join at its actual instances. The consumer may duplicate
the lambda or apply it, and no target recovery or argument equality is assumed. -/
theorem recursive_lambda_annotation_consumer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (RA : RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ A) shared)
    (RC : RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ C) shared) :
    env.HasType univs Γ (.lam C b) (.forallE A B) ∧
    ∃ out, RecursiveCastCompute D (proofEraseCtx Γ)
        (proofErase Γ (t.inst (.lam A b))) out ∧
      RecursiveCastCompute D (proofEraseCtx Γ)
        (proofErase Γ (t.inst (.lam C b))) out := by
  obtain ⟨hc, out, RL, RR⟩ := recursive_lambda_annotation_join heq hs hregistry hΓ hA hC hb RA RC
  have hf := HasType.lam hA hb
  obtain ⟨z, _, _, RZ, RZ'⟩ := RL.inst_joined heq hs hregistry
    ⟨hΓ, hf.isType henv hΓ⟩ ht hf hc RR
  exact ⟨hc, _, RZ, RZ'⟩

/-- Every beta residual of the two actual consumers has a finite inferred
comparison. This promotes the supplied domain computation evidence into the
function-head checking mode required when a consumer exposes a lambda. -/
theorem recursive_lambda_annotation_consumer_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (RA : RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ A) shared)
    (RC : RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ C) shared)
    (PL : ProofShape.BetaRed (proofErase Γ (t.inst (.lam A b))) left)
    (PR : ProofShape.BetaRed (proofErase Γ (t.inst (.lam C b))) right) :
    ∃ n, JointCompare (ErasedJointStage D n) (proofEraseCtx Γ) false left right := by
  obtain ⟨hc, out, RL, RR⟩ := recursive_lambda_annotation_consumer heq hs hregistry hΓ hA hC hb ht RA RC
  obtain ⟨out, SL, SR⟩ := RL.join_beta heq hs hregistry hΓ
    (ht.instN henv Ctx.InstN.zero (HasType.lam hA hb)) (ht.instN henv Ctx.InstN.zero hc) RR PL PR
  have H : JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) false left right :=
    .compute (SL.mono erased_beta_stable_joint_into_union) (SR.mono erased_beta_stable_joint_into_union) (.leaf .refl)
  exact H.finite_stage erased_joint_stage_mono

/-- A reflexive universe cast in a written lambda annotation is repaired in
every typed consumer. The cast is inside the domain, not around the lambda;
the domain paths are constructed here, without an annotation-coverage premise.
The consumer body and the lambda body are unrestricted. -/
theorem recursive_cast_annotation_consumer_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hr : env.HasType univs Γ r
      (eqApp (.succ (.succ u)) (.sort (.succ u)) (.sort u) (.sort u)))
    (hb : env.HasType univs (A :: Γ) b B)
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (PL : ProofShape.BetaRed (proofErase Γ (t.inst (.lam A b))) left)
    (PR : ProofShape.BetaRed
      (proofErase Γ (t.inst (.lam (typeCast (.succ u) (.sort u) (.sort u) r A) b))) right) :
    ∃ n, JointCompare (ErasedJointStage D n) (proofEraseCtx Γ) false left right := by
  have hC := HasType.typeCast henv heq (u := .succ u) (by exact hu)
    (HasType.sort hu) (HasType.sort hu) hr hA
  have RC : RecursiveCastCompute D (proofEraseCtx Γ)
      (proofErase Γ (typeCast (.succ u) (.sort u) (.sort u) r A)) (proofErase Γ A) :=
    .cast (by exact hu) hΓ (HasType.sort hu) (HasType.sort hu) hr hA (.core .refl) (.core .refl)
  exact recursive_lambda_annotation_consumer_beta heq hs hregistry hΓ hA hC hb ht
    (.core .refl) RC PL PR

omit [Params] in
/-- Actual canonical-Eq environments discharge the soundness and registry
premises for annotation repair. Any supplied recursive domain join suffices;
no assertion that all semantic domain conversions have such joins is made. -/
theorem EnvironmentCore.recursive_lambda_annotation_consumer_beta
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ A C u b B t T shared left right}, env.HasCanonicalEq → OnCtx Γ (env.IsType U) →
      env.HasType U Γ A (.sort u) → env.HasType U Γ C (.sort u) →
      env.HasType U (A :: Γ) b B → env.HasType U (.forallE A B :: Γ) t T →
      RecursiveCastCompute definitions (proofEraseCtx Γ) (proofErase Γ A) shared →
      RecursiveCastCompute definitions (proofEraseCtx Γ) (proofErase Γ C) shared →
      ProofShape.BetaRed (proofErase Γ (t.inst (.lam A b))) left →
      ProofShape.BetaRed (proofErase Γ (t.inst (.lam C b))) right →
      ∃ n, JointCompare (ErasedJointStage definitions n) (proofEraseCtx Γ) false left right := by
  letI := henv.params U
  intro Γ A C u b B t T shared left right heq hΓ hA hC hb ht RA RC PL PR
  exact Strengthening.recursive_lambda_annotation_consumer_beta heq sound rfl hΓ hA hC hb ht RA RC PL PR

end Lean4Lean.VEnv.Strengthening
