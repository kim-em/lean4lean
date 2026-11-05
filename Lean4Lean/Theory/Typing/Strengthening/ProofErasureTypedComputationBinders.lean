import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationApplication
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureGenericNestedEta

/-! # Binder congruence for typed computation chains

Body computations run under their original domain. Domain computations change
only the annotation; ordinary context conversion identifies the body's erasure.
Symmetric and transitive domain paths retag intermediate lambda assignments.
No forward native-context transport or computational confluence is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- A body computation chain lifts under its unchanged lambda domain,
including arbitrary data-valued and proof-valued bodies. -/
theorem TypedComputationEq.lam_body
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (H : TypedComputationEq D (A :: Γ) b b' B) :
    TypedComputationEq D Γ (.lam A b) (.lam A b') (.forallE A B) := by
  induction H with
  | step HE R => exact .step (.lamDF hA HE) (proofErase_scoped_compute_lam_eq hΓ hA HE R)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A typed computation of a lambda annotation leaves the body's erased
syntax unchanged, using ordinary equality of the two binder contexts. -/
theorem proofErase_scoped_compute_lam_domain
    (hΓ : OnCtx Γ (env.IsType univs)) (HA : env.IsDefEq univs Γ A A' (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (RA : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ A')) :
    ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ (.lam A b)) (proofErase Γ (.lam A' b)) := by
  have HE := IsDefEq.lamDF HA hb
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HA.hasType.1⟩
  classical
  by_cases hp : IsProof Γ (.lam A b)
  · have hp' := (isProof_congr hΓ HE).1 hp
    rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 hp']
    exact .refl
  have hp' : ¬ IsProof Γ (.lam A' b) := fun h => hp ((isProof_congr hΓ HE).2 h)
  rw [show proofErase Γ (.lam A b) = .lam _ _ from if_neg hp,
    show proofErase Γ (.lam A' b) = .lam _ _ from if_neg hp',
    ← proofErase_defeqCtx hΓA (IsDefEqCtx.succ .zero HA) hb]
  exact .lam RA .refl

/-- A domain computation chain changes a lambda's annotation while preserving
its body. Every intermediate lambda is assigned the original Pi type by ordinary
conversion. No computational join of the domains or native evidence is used. -/
theorem TypedComputationEq.lam_domain
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : TypedComputationEq D Γ A A' (.sort u)) (hb : env.HasType univs (A :: Γ) b B) :
    TypedComputationEq D Γ (.lam A b) (.lam A' b) (.forallE A B) := by
  generalize ET : VExpr.sort u = T at H
  induction H generalizing u b B with
  | step HE R =>
    cases ET
    exact .step (.lamDF HE hb) (proofErase_scoped_compute_lam_domain hΓ HE hb R)
  | symm H ih =>
    cases ET
    have hb₀ := hb.defeqDFC henv (IsDefEqCtx.succ .zero H.defeq.symm)
    have hΓA : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, u, H.defeq.hasType.1⟩
    obtain ⟨v, hB⟩ := hb₀.isType henv hΓA
    exact ((ih hb₀ rfl).symm).convert (.forallEDF H.defeq hB)
  | trans H₁ _ ih₁ ih₂ =>
    cases ET
    have hb₁ := hb.defeqDFC henv (IsDefEqCtx.succ .zero H₁.defeq)
    have hΓA : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, u, H₁.defeq.hasType.1⟩
    obtain ⟨v, hB⟩ := hb.isType henv hΓA
    exact (ih₁ hb rfl).trans ((ih₂ hb₁ rfl).convert (IsDefEq.forallEDF H₁.defeq hB).symm)

/-- Full lambda congruence for computation chains, including unrelated written
domains along a typed domain chain and arbitrary data-valued body chains. -/
theorem TypedComputationEq.lam
    (hΓ : OnCtx Γ (env.IsType univs))
    (HA : TypedComputationEq D Γ A A' (.sort u))
    (HB : TypedComputationEq D (A :: Γ) b b' B) :
    TypedComputationEq D Γ (.lam A b) (.lam A' b') (.forallE A B) :=
  (HB.lam_body hΓ HA.defeq.hasType.1).trans (HA.lam_domain hΓ HB.defeq.hasType.2)

/-- A type-body chain lifts under an unchanged Pi binder. -/
theorem TypedComputationEq.forall_body
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (H : TypedComputationEq D (A :: Γ) B B' (.sort v)) :
    TypedComputationEq D Γ (.forallE A B) (.forallE A B') (.sort (.imax u v)) := by
  generalize ET : VExpr.sort v = T at H
  induction H generalizing v with
  | step HE R =>
    cases ET
    have HP := IsDefEq.forallEDF hA HE
    apply TypedComputationEq.step HP
    rw [show proofErase Γ (.forallE A _) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ HP.hasType.1),
      show proofErase Γ (.forallE A _) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ HP.hasType.2)]
    exact .forallE .refl R
  | symm _ ih => exact (ih ET).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ ET).trans (ih₂ ET)

/-- Changing only a Pi domain follows its type computation chain. The body
is transported by ordinary context equality, without transporting its native
certificates or its computational paths. -/
theorem TypedComputationEq.forall_domain
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : TypedComputationEq D Γ A A' (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v)) :
    TypedComputationEq D Γ (.forallE A B) (.forallE A' B) (.sort (.imax u v)) := by
  generalize ET : VExpr.sort u = T at H
  induction H generalizing u B with
  | step HE R =>
    cases ET
    have HP := IsDefEq.forallEDF HE hB
    have hΓA : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, u, HE.hasType.1⟩
    apply TypedComputationEq.step HP
    rw [show proofErase Γ (.forallE _ B) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ HP.hasType.1),
      show proofErase Γ (.forallE _ B) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ HP.hasType.2),
      ← proofErase_defeqCtx hΓA (IsDefEqCtx.succ .zero HE) hB]
    exact .forallE R .refl
  | symm H ih =>
    cases ET
    exact (ih (hB.defeqDFC henv (IsDefEqCtx.succ .zero H.defeq.symm)) rfl).symm
  | trans H₁ _ ih₁ ih₂ =>
    cases ET
    exact (ih₁ hB rfl).trans (ih₂ (hB.defeqDFC henv (IsDefEqCtx.succ .zero H₁.defeq)) rfl)

/-- Full dependent Pi congruence follows from domain and original-context
codomain computation chains, with no confluence assumption. -/
theorem TypedComputationEq.forallE
    (hΓ : OnCtx Γ (env.IsType univs))
    (HA : TypedComputationEq D Γ A A' (.sort u))
    (HB : TypedComputationEq D (A :: Γ) B B' (.sort v)) :
    TypedComputationEq D Γ (.forallE A B) (.forallE A' B') (.sort (.imax u v)) :=
  (HB.forall_body hΓ HA.defeq.hasType.1).trans (HA.forall_domain hΓ HB.defeq.hasType.2)

end Lean4Lean.VEnv.Strengthening
