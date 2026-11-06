import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationCoreComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEnvironmentCore

/-! # Arbitrary annotation consumers after full core reduction

Recursive level-core domain guards supply paired annotation variants. Every
ordinary typed consumer retains those variants, and independent full core paths
have an inferred residual comparison. The result includes recursive delta,
projection, registered iota, quotient rules and explicit universe conversion.
It does not assume arbitrary core stability of the beta-only family grammar.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- A recursive level-core domain check constructs common Pi typing and a
marked pair of same-body lambdas, including proof-valued lambdas. -/
theorem level_recursive_lambda_annotation_variant
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (HA : LevelRecursiveGuard D false (proofErase Γ A) (proofErase Γ C)) :
    env.HasType univs Γ (.lam C b) (.forallE A B) ∧
      AnnotationVariant (LevelRecursiveGuard D false) 0
        (proofErase Γ (.lam A b)) (proofErase Γ (.lam C b)) := by
  have HC : JointCompare (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) true
      (proofErase Γ A) (proofErase Γ C) :=
    (((HA.forward hs hl hcon hc .refl .refl).common).scoped (fun H => .base H)).joint
  have HAC := proofErase_joint_carrier_reflect (erased_level_core_descent hs) hΓ hA hC (.carrierChecked HC)
  have HL := IsDefEq.lamDF HAC hb
  refine ⟨HL.hasType.2, ?_⟩
  by_cases hp : IsProof Γ (.lam A b)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HL).1 hp)]
    exact .refl
  have hpc : ¬ IsProof Γ (.lam C b) := fun H => hp ((isProof_congr hΓ HL).2 H)
  have EB := proofErase_defeqCtx (Γ₁ := A :: Γ) ⟨hΓ, u, hA⟩ (IsDefEqCtx.succ .zero HAC) hb
  rw [show proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b)
      from if_neg hp,
    show proofErase Γ (.lam C b) = .lam (proofErase Γ C) (proofErase (C :: Γ) b)
      from if_neg hpc, ← EB]
  simpa only [ProofShape.liftN_zero] using
    (AnnotationVariant.marked (n := 0) (b := proofErase (A :: Γ) b) HA .refl)

/-- Any typed consumer of a certified reannotation pair has inferred comparison
at every pair of full level-core residuals. The consumer may create arbitrary
new redexes by applying or duplicating the supplied lambdas. No domain join,
normal form, native recovery of the consumer, or global guarded confluence is
required. -/
theorem level_recursive_annotation_consumer_core
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (HA : LevelRecursiveGuard D false (proofErase Γ A) (proofErase Γ C))
    (RL : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam A b))) left)
    (RR : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam C b))) right) :
    RawCheckedCompare (ErasedLevelCore D) false left right := by
  obtain ⟨hC', V⟩ := level_recursive_lambda_annotation_variant hs hl hcon hc hΓ hA hC hb HA
  have hf := HasType.lam hA hb
  have hΓPi : OnCtx (.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, hf.isType henv hΓ⟩
  have VT : AnnotationVariant (LevelRecursiveGuard D false) 0
      (proofErase Γ (t.inst (.lam A b))) (proofErase Γ (t.inst (.lam C b))) := by
    rw [proofErase_instN hΓPi hf Ctx.InstN.zero ht, proofErase_instN hΓPi hC' Ctx.InstN.zero ht]
    simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN]
    apply AnnotationVariant.subst_images
    intro i
    cases i with
    | zero => exact V
    | succ i => exact .refl
  exact annotation_level_core_residual_check hs hl hcon hc hΓ
    (ht.instN henv Ctx.InstN.zero hC') VT RL RR

omit [Params] in
/-- Actual well-formed environments discharge core soundness, universe
compatibility, concrete pattern checks and typed core confluence. Only the
constructive recursive domain guard remains as an alignment premise. -/
theorem EnvironmentCore.level_recursive_annotation_consumer_core
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ A C u b B t T left right}, OnCtx Γ (env.IsType U) →
      env.HasType U Γ A (.sort u) → env.HasType U Γ C (.sort u) →
      env.HasType U (A :: Γ) b B → env.HasType U (.forallE A B :: Γ) t T →
      LevelRecursiveGuard definitions false (proofErase Γ A) (proofErase Γ C) →
      Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst (.lam A b))) left →
      Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst (.lam C b))) right →
      RawCheckedCompare (ErasedLevelCore definitions) false left right := by
  letI := henv.params U
  intro Γ A C u b B t T left right hΓ hA hC hb ht HA RL RR
  exact Strengthening.level_recursive_annotation_consumer_core sound
    (levelCompatible (fun H => H)) (fun H => H) (typed_level_core_confluence (fun H => H))
    hΓ hA hC hb ht HA RL RR

end Lean4Lean.VEnv.Strengthening
