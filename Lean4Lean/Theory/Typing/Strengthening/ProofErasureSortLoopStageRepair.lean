import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursivePrefixResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSortRecursiveSubstitutionBoundary

/-! # Repair the sort-valued substitution witness at the first singleton stage

The mixed loop still has an inferred raw comparison before its newly exposed
beta contraction. That contraction loses every level-core raw comparison of the
loops. A concrete stage-one cast computation repairs the resulting annotations.
Thus the failure concerns forward stability after substitution; endpoint
substitution alone does retain a raw certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private erase_diagonal from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRecursiveCoverage
variable [Params] {D : Definitions}

/-- Arbitrary raw substitution retains a raw inferred comparison from a
recursive guard. It need not retain the stronger forward-stable guard: newly
created beta contractions are exactly the additional obligation. -/
theorem LevelRecursiveGuard.subst_raw
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : LevelRecursiveGuard D mode a b) (σ : ProofShape.Subst) :
    RawCheckedCompare (ErasedLevelCore D) mode (a.subst σ) (b.subst σ) :=
  (H.forward hs hl hcon hc .refl .refl).subst (fun H => erased_level_core_subst H)

/-- A genuine reflexive canonical-Eq cast computes at stage one, including an
opaque proof major and arbitrary payload. This uses the existing prefix rule. -/
theorem first_stage_reflexive_cast_compute
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hX : env.HasType univs Γ X (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X X))
    (hx : env.HasType univs Γ x X) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (typeCast u X X q x)) (proofErase Γ x) := by
  have HC := IsDefEq.typeCast_refl henv heq hu hΓ hX hq hx
  by_cases hp : IsProof Γ (typeCast u X X q x)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HC).1 hp)]
    exact .refl
  · have ES := proofErase_const_spine hΓ
      (args := [.sort u, X, castMotive u X, x, X, q]) HC.hasType.1 hp
    change proofErase Γ (typeCast u X X q x) = _ at ES
    rw [ES]
    exact (show RawCheckedCompare (ErasedLevelCore D) true (proofErase Γ X)
      (proofErase Γ X) from .base .refl).first_stage_full

/-- Removing a reflexive cast in both diagonal annotations repairs the full
self loop at stage one. This path does not attempt to normalize the loop. -/
theorem first_stage_reflexive_cast_loop_compute
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hX : env.HasType univs Γ X (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X X))
    (hx : env.HasType univs Γ x X) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
      (selfLoop (proofErase Γ (typeCast u X X q x))) (selfLoop (proofErase Γ x)) := by
  have R := first_stage_reflexive_cast_compute (D := D) heq hu hΓ hX hq hx
  exact .app (.lam R .refl) (.lam R .refl)

omit [Params] in
/-- A single newly exposed beta contraction destroys level-core inferred
comparison on the cast-loop witness, but one singleton stage computes the
contracted loop back to the reference loop. No confluence claim is assumed. -/
theorem EnvironmentCore.cast_loop_beta_repair {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {u Γ X i A B}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ X (.sort u) →
      env.HasType U Γ (.bvar i) (eqApp (.succ u) (.sort u) X X) →
      env.HasType U Γ (.forallE A B) X →
      let P := proofErase Γ (.forallE A B)
      let C := proofErase Γ (typeCast u X X (.bvar i) (.forallE A B))
      RawCheckedCompare (ErasedLevelCore definitions) false (selfLoop P) (.app (diagonal P) (diagonal C)) ∧
      ProofShape.BetaRed (.app (diagonal P) (diagonal C)) (selfLoop C) ∧
      (∀ mode, ¬ RawCheckedCompare (ErasedLevelCore definitions) mode (selfLoop P) (selfLoop C)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage definitions 1) (proofEraseCtx Γ)
        (selfLoop C) (selfLoop P) := by
  letI := henv.params U
  intro u Γ X i A B heq hu hΓ hX hq hpi
  dsimp only
  refine ⟨.app (.base .refl) (.lamCommon (.base .refl)), ?_, ?_,
    first_stage_reflexive_cast_loop_compute heq hu hΓ hX hq hpi⟩
  · simpa [diagonal, selfLoop, ProofShape.inst, ProofShape.liftN_zero] using
      (ProofShape.BetaRed.beta (A := proofErase Γ (.forallE A B))
        (b := .app (.bvar 0) (.bvar 0))
        (a := diagonal (proofErase Γ (typeCast u X X (.bvar i) (.forallE A B)))))
  · intro mode H
    have HC := H.level_selfLoop_annotations
    obtain ⟨⟨_, hA⟩, _, hB⟩ := hpi.forallE_inv henv
    have hn := not_isProof_of_sort hΓ (HasType.forallE hA hB)
    rw [show proofErase Γ (.forallE A B) = .forallE _ _ from if_neg hn] at HC
    obtain ⟨C, E, R⟩ := HC.level_pi_exposure
    exact level_cast_no_pi henv U heq hu hΓ hX hq hpi R

/-- Convertible recursive carriers give actual proposition typings for both
self loops and the mixed loop. Their erasures are the raw shapes in the beta
repair theorem, so that obstruction is not an artifact of untyped self-application. -/
theorem recursive_mixed_loops_realize
    (hΓ : OnCtx Γ (env.IsType univs))
    (Hrec : env.IsDefEq univs Γ A (.forallE A (.sort .zero)) (.sort u))
    (HAB : env.IsDefEq univs Γ A B (.sort u)) :
    env.HasType univs Γ (RecursiveDomain.omegaTerm A) (.sort .zero) ∧
    env.HasType univs Γ (.app (RecursiveDomain.diagonal A) (RecursiveDomain.diagonal B)) (.sort .zero) ∧
    env.HasType univs Γ (RecursiveDomain.omegaTerm B) (.sort .zero) ∧
    proofErase Γ (RecursiveDomain.omegaTerm A) = selfLoop (proofErase Γ A) ∧
    proofErase Γ (.app (RecursiveDomain.diagonal A) (RecursiveDomain.diagonal B)) =
      .app (diagonal (proofErase Γ A)) (diagonal (proofErase Γ B)) ∧
    proofErase Γ (RecursiveDomain.omegaTerm B) = selfLoop (proofErase Γ B) := by
  have hv : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have hb : env.HasType univs (A :: Γ) RecursiveDomain.selfBody (.sort .zero) :=
    ((Hrec.weakN henv Ctx.LiftN.one).defeq hv).app hv
  have hb' : env.HasType univs (B :: Γ) RecursiveDomain.selfBody (.sort .zero) :=
    hb.defeqDFC henv (.succ .zero HAB)
  have Hdiag := IsDefEq.lamDF HAB hb
  have hx := Hrec.symm.defeq Hdiag.hasType.1
  have hy := Hrec.symm.defeq Hdiag.hasType.2
  have htL : env.HasType univs Γ (RecursiveDomain.omegaTerm A) (.sort .zero) := Hdiag.hasType.1.app hx
  have htM : env.HasType univs Γ (.app (RecursiveDomain.diagonal A) (RecursiveDomain.diagonal B)) (.sort .zero) :=
    Hdiag.hasType.1.app hy
  have htR : env.HasType univs Γ (RecursiveDomain.omegaTerm B) (.sort .zero) := Hdiag.hasType.2.app hy
  have EA := erase_diagonal hΓ HAB.hasType.1 hb
  have EB := erase_diagonal hΓ HAB.hasType.2 hb'
  refine ⟨htL, htM, htR, ?_, ?_, ?_⟩
  · rw [show proofErase Γ (RecursiveDomain.omegaTerm A) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ htL), EA]
    rfl
  · rw [show proofErase Γ (.app (RecursiveDomain.diagonal A) (RecursiveDomain.diagonal B)) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ htM), EA, EB]
  · rw [show proofErase Γ (RecursiveDomain.omegaTerm B) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ htR), EB]
    rfl

omit [Params] in
/-- The loss and first-stage repair occur between three actual propositions
in one well-formed context. The recursive Pi and free equality major are the
same premises realized by the installed canonical-Eq counterexample. -/
theorem EnvironmentCore.typed_sort_loop_beta_repair {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {u v Γ i A B}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ (.sort v) (.sort u) →
      env.HasType U Γ (.bvar i) (eqApp (.succ u) (.sort u) (.sort v) (.sort v)) →
      env.IsDefEq U Γ (.forallE A B) (.forallE (.forallE A B) (.sort .zero)) (.sort v) →
      ∃ left mixed right,
        env.HasType U Γ left (.sort .zero) ∧ env.HasType U Γ mixed (.sort .zero) ∧
        env.HasType U Γ right (.sort .zero) ∧
        RawCheckedCompare (ErasedLevelCore definitions) false (proofErase Γ left) (proofErase Γ mixed) ∧
        ProofShape.BetaRed (proofErase Γ mixed) (proofErase Γ right) ∧
        ¬ RawCheckedCompare (ErasedLevelCore definitions) false (proofErase Γ left) (proofErase Γ right) ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionStage definitions 1) (proofEraseCtx Γ)
          (proofErase Γ right) (proofErase Γ left) := by
  letI := henv.params U
  intro u v Γ i A B heq hu hΓ hX hq Hrec
  have HC := IsDefEq.typeCast_refl henv heq hu hΓ hX hq Hrec.hasType.1
  obtain ⟨hL, hM, hR, EL, EM, ER⟩ := recursive_mixed_loops_realize hΓ Hrec HC.symm
  have H := cast_loop_beta_repair henv U heq hu hΓ hX hq Hrec.hasType.1
  refine ⟨_, _, _, hL, hM, hR, ?_⟩
  rw [EL, EM, ER]
  exact ⟨H.1, H.2.1, H.2.2.1 false, H.2.2.2⟩

end Lean4Lean.VEnv.Strengthening
