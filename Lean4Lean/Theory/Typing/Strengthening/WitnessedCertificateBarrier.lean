import Lean4Lean.Theory.Typing.Strengthening.InhabitedFrontBarrier
import Lean4Lean.Theory.Typing.Strengthening.EqFamilyFrontBarrier

/-! # Ambient equality witnesses do not reduce certificate completeness

Every actual proposition conversion already types a reflexivity proof at the
corresponding object-language Eq. Even requiring that both propositions are
inhabited therefore leaves the full front when certificates have unrestricted
common-type descent. A witness specifically available below an insertion, or
the exact generated extraction program, would be a different restriction.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Ambient conversion always supplies an object-language Eq witness. -/
theorem proposition_conversion_witness (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero)) (H : env.IsDefEqU univs Γ P Q) :
    env.HasType univs Γ (eqReflApp (.succ .zero) (.sort .zero) P) (propositionEq P Q) :=
  (IsDefEq.eqApp_r heq (by trivial) (.sort (by trivial)) hP
    (H.of_l henv hΓ hP)).defeq
      (HasType.eqReflApp heq (by trivial) (.sort (by trivial)) hP)

/-- An unproved ambient completeness premise restricted to two inhabited
propositions with a typed equality witness. It is still at least as strong as
PropositionFront for every relation with EndpointDescent, as proved below. -/
def WitnessedPropCoverage (Cmp : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {Γ P Q p q witness}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ P (.sort .zero) → env.HasType univs Γ Q (.sort .zero) →
    env.HasType univs Γ p P → env.HasType univs Γ q Q →
    env.HasType univs Γ witness (propositionEq P Q) →
    env.IsDefEqU univs Γ P Q → Cmp Γ P Q

/-- The object equality witness adds no restriction to ambient completeness
once the two inhabited propositions are already definitionally equal. -/
theorem WitnessedPropCoverage.inhabitedFront (heq : env.HasCanonicalEq)
    (hc : EndpointDescent Cmp) (hcov : WitnessedPropCoverage Cmp) :
    InhabitedPropositionFront := by
  intro Γ X P Q p q hΓ hX hP hQ hp hq H
  have hΓ' : OnCtx (X :: Γ) (env.IsType univs) := ⟨hΓ, hX⟩
  have hP' : env.HasType univs (X :: Γ) P.lift (.sort .zero) := hP.weak henv
  have hQ' : env.HasType univs (X :: Γ) Q.lift (.sort .zero) := hQ.weak henv
  have HG := hcov hΓ' hP' hQ' (hp.weak henv) (hq.weak henv)
    (proposition_conversion_witness heq hΓ' hP' H) H
  have HG' : Cmp (X :: Γ) (P.lift' (.skip .refl)) (Q.lift' (.skip .refl)) := by
    simpa only [← lift_eq_lift'] using HG
  exact hc (.skip .refl) hΓ hΓ' hP hQ HG'

/-- Combining inhabitation and an ambient propositional equality witness
does not turn certificate completeness into a smaller strengthening problem. -/
theorem WitnessedPropCoverage.propositionFront (heq : env.HasCanonicalEq)
    (hc : EndpointDescent Cmp) (hcov : WitnessedPropCoverage Cmp) : PropositionFront :=
  inhabitedFront_iff_propositionFront.1 (hcov.inhabitedFront heq hc)

end Lean4Lean.VEnv.Strengthening
