import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCertificateStrengthening
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnionHeadExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoverablePropFunction

/-! # Any-output recovery of inhabited propositions carries the front

A Pi with an arbitrary type as domain and a closed inhabited equality as
codomain is itself an inhabited proposition. Recovering any type for this Pi
forces universe recovery of its domain. Exact certificate descent then removes
the fresh-variable test for universe exposure in the actual joint union.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private closedProposition closedProposition_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoverablePropFunction
variable [Params]

/-- Missing coverage restricted to inhabited propositions. Neither the
recovered output nor its head is prescribed, and no recovery is requested for
arbitrary data or uninhabited propositions. This premise is not proved here. -/
def InhabitedPropositionRecovery
    (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ P p}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ P (.sort .zero) →
    env.HasType univs Γ p P →
    ∃ out, ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ P) out

/-- An inhabited proposition tests universe recovery of any typed domain.
The test has an explicit proof, and its arbitrary recovered output can be
inverted without computation closure, confluence, or a recovery premise on A. -/
theorem inhabited_proposition_recovery_test
    (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u)) :
    ∃ P p, env.HasType univs Γ P (.sort .zero) ∧ env.HasType univs Γ p P ∧
      ∀ {out}, ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ P) out →
        ∃ v, ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ A) (.sort v) := by
  let P : VExpr := .forallE A closedProposition
  let q := eqReflApp (.succ (.succ .zero)) (.sort (.succ .zero)) (.sort .zero)
  have hq : env.HasType univs (A :: Γ) q closedProposition :=
    HasType.eqReflApp heq (by trivial) (.sort (by trivial)) (.sort (by trivial))
  have hu : (VLevel.imax u .zero).WF univs := ⟨hA.sort_r henv hΓ, by trivial⟩
  have hP : env.HasType univs Γ P (.sort .zero) :=
    (IsDefEq.sortDF hu (by trivial)
      (show VLevel.imax u .zero ≈ .zero from rfl)).defeq
        (HasType.forallE hA (closedProposition_typed heq))
  refine ⟨P, .lam A q, hP, HasType.lam hA hq, ?_⟩
  intro out R
  have EP : proofErase Γ P = .forallE (proofErase Γ A)
      (proofErase (A :: Γ) closedProposition) := if_neg (not_isProof_of_sort hΓ hP)
  rw [EP] at R
  exact R.forallE_domain_inv

/-- Any-output recovery of inhabited propositions already forces some-universe
recovery of every typed type, at exactly the same computation relation. -/
theorem InhabitedPropositionRecovery.sort_recovery
    (heq : env.HasCanonicalEq) (H : InhabitedPropositionRecovery Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u)) :
    ∃ v, ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ A) (.sort v) := by
  obtain ⟨P, p, hP, hp, HT⟩ := inhabited_proposition_recovery_test (Step := Step) heq hΓ hA
  obtain ⟨out, R⟩ := H hΓ hP hp
  exact HT R

/-- For the actual joint union, recovery of inhabited propositions exposes
all types convertible to a universe. The fresh variable is removed by typed
certificate descent; no arbitrary primitive substitution or raw filler is used. -/
theorem InhabitedPropositionRecovery.joint_union_sort_exposure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : InhabitedPropositionRecovery (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (HT : env.IsDefEqU univs Γ T (.sort v)) :
    ∃ w, ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ T) (.sort w) := by
  have hΓT : OnCtx (T :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  have hx : env.HasType univs (T :: Γ) (.bvar 0) T.lift := .bvar .zero
  have hxv : env.HasType univs (T :: Γ) (.bvar 0) (.sort v) :=
    ((HT.of_l henv hΓ hT).weak henv).defeq hx
  obtain ⟨w, R⟩ := H.sort_recovery heq hΓT hxv
  rw [show proofErase (T :: Γ) (.bvar 0) = .bvar 0 from
    if_neg (not_isProof_of_sort hΓT hxv)] at R
  have C : ScopedCompute (ErasedJointUnion D) (proofEraseCtx (T :: Γ))
      ((proofErase Γ T).liftN 1) (.sort w) := R.bvar_compute
  exact ⟨w, (proofErase_joint_union_compute_lift_iff heq hs hΓ hΓT Ctx.LiftN.one hT
    (out := .sort w)).1 C⟩

/-- Even any-output recovery restricted to inhabited propositions suffices
for the original proposition front in the joint union. The Eq probe needs
only the sort-exposure consequence; no positive unit type is required.
This is a sufficient coverage obligation, not a proved coverage theorem or
an assertion that the obligation is strictly smaller than PropositionFront. -/
theorem InhabitedPropositionRecovery.joint_union_propositionFront
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : InhabitedPropositionRecovery (ErasedJointUnion D)) : PropositionFront := by
  apply EqProbeSortExposure.joint_union_propositionFront heq hs hregistry hEq hRec
  intro Γ P Q q hΓ hP hQ hq HPQ
  exact H.joint_union_sort_exposure heq hs hΓ (eqSortProbe_typed heq hΓ hP hQ hq)
    ⟨_, eqSortProbe_defeq heq hΓ hP hQ hq HPQ⟩

end Lean4Lean.VEnv.Strengthening
