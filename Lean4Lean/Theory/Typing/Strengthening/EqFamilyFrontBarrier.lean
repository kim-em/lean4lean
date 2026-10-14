import Lean4Lean.Theory.Typing.Strengthening.ReannotationBarrier
import Lean4Lean.Theory.Typing.Strengthening.SingletonIndexAlignmentBoundary
import Lean4Lean.Theory.Typing.Strengthening.GuardedKComputation

/-! # Diagonal Eq family conversion retains the proposition front

Restricting a comparison to rigid family propositions does not by itself give a
smaller strengthening obligation. Even the pair `Eq Prop P P`, `Eq Prop P Q`
encodes arbitrary proposition conversion. This boundary concerns ambient family
coverage, not the more structured generated-prefix coverage predicate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- The canonical equality family at two proposition-valued endpoints. -/
def propositionEq (P Q : VExpr) : VExpr := eqApp (.succ .zero) (.sort .zero) P Q

/-- These family propositions are typed without assuming endpoint conversion. -/
theorem propositionEq_typed (heq : env.HasCanonicalEq)
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero)) :
    env.HasType univs Γ (propositionEq P Q) (.sort .zero) :=
  HasType.eqApp heq (by trivial) (.sort (by trivial)) hP hQ

/-- Conversion from the diagonal family is exactly conversion of its endpoints.
The reverse direction uses Eq's rigidity, not proof irrelevance. -/
theorem propositionEq_diagonal_iff (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero)) :
    env.IsDefEqU univs Γ (propositionEq P P) (propositionEq P Q) ↔
      env.IsDefEqU univs Γ P Q := by
  constructor
  · intro H
    have H' : env.IsDefEqU univs Γ
        (mkApps (.const ``Eq [.succ .zero]) [.sort .zero, P, P])
        (mkApps (.const ``Eq [.succ .zero]) [.sort .zero, P, Q]) := H
    obtain ⟨_, hargs⟩ := H'.rigidApp_inv henv hΓ (heq.rigid henv)
      (propositionEq_typed heq hP hP)
    cases hargs with | cons _ hargs =>
    cases hargs with | cons _ hargs =>
    cases hargs with | cons hPQ _ => exact hPQ
  · intro H
    exact ⟨_, IsDefEq.eqApp_r heq (by trivial) (.sort (by trivial)) hP
      (H.of_l henv hΓ hP)⟩

/-- Reflection restricted to this single canonical family shape. This is an
unproved obligation, and the theorem below identifies it with PropositionFront. -/
def EqDiagonalFront : Prop :=
  ∀ {Γ X P Q}, OnCtx Γ (env.IsType univs) → env.IsType univs Γ X →
    env.HasType univs Γ P (.sort .zero) → env.HasType univs Γ Q (.sort .zero) →
    env.IsDefEqU univs (X :: Γ) (propositionEq P P).lift (propositionEq P Q).lift →
    env.IsDefEqU univs Γ (propositionEq P P) (propositionEq P Q)

/-- A rigid family head, fixed carrier and diagonal left endpoint do not make
this front strictly smaller than proposition strengthening. -/
theorem eqDiagonalFront_iff_propositionFront (heq : env.HasCanonicalEq) :
    EqDiagonalFront ↔ PropositionFront := by
  constructor
  · intro H Γ X P Q hΓ hX hP hQ HE
    have hΓ' : OnCtx (X :: Γ) (env.IsType univs) := ⟨hΓ, hX⟩
    have hP' : env.HasType univs (X :: Γ) P.lift (.sort .zero) := hP.weak henv
    have HF := (propositionEq_diagonal_iff heq hΓ' hP').2 HE
    have HF' : env.IsDefEqU univs (X :: Γ)
        (propositionEq P P).lift (propositionEq P Q).lift := by
      simpa only [propositionEq, eqApp, lift, liftN] using HF
    exact (propositionEq_diagonal_iff heq hΓ hP).1 (H hΓ hX hP hQ HF')
  · intro H Γ X P Q hΓ hX hP hQ HF
    exact H hΓ hX (propositionEq_typed heq hP hP) (propositionEq_typed heq hP hQ) HF

/-- Ambient completeness only for diagonal canonical Eq-family conversions.
This premise is unproved for the finite certificate models. It differs from
FamilyCertificateCoverage, which also carries a generated prefix and its check. -/
def EqDiagonalCoverage (Cmp : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {Γ P Q}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ P (.sort .zero) → env.HasType univs Γ Q (.sort .zero) →
    env.IsDefEqU univs Γ (propositionEq P P) (propositionEq P Q) →
    Cmp Γ (propositionEq P P) (propositionEq P Q)

/-- Completeness of any descending certificate relation on these diagonal
families already proves the original proposition front. Thus arbitrary ambient
family completeness cannot be justified merely by the restricted outer shape. -/
theorem EqDiagonalCoverage.propositionFront (heq : env.HasCanonicalEq)
    (hc : EndpointDescent Cmp) (hcov : EqDiagonalCoverage Cmp) : PropositionFront := by
  apply (eqDiagonalFront_iff_propositionFront heq).1
  intro Γ X P Q hΓ hX hP hQ HF
  have hΓ' : OnCtx (X :: Γ) (env.IsType univs) := ⟨hΓ, hX⟩
  have hP' : env.HasType univs (X :: Γ) P.lift (.sort .zero) := hP.weak henv
  have hQ' : env.HasType univs (X :: Γ) Q.lift (.sort .zero) := hQ.weak henv
  have HF' : env.IsDefEqU univs (X :: Γ)
      (propositionEq P.lift P.lift) (propositionEq P.lift Q.lift) := by
    simpa only [propositionEq, eqApp, lift, liftN] using HF
  have HG := hcov hΓ' hP' hQ' HF'
  have HG' : Cmp (X :: Γ) ((propositionEq P P).lift' (.skip .refl))
      ((propositionEq P Q).lift' (.skip .refl)) := by
    have hl (e : VExpr) : e.lift' (.skip .refl) = e.lift :=
      lift'_consN_skipN (k := 0) (n := 1)
    simpa only [hl, propositionEq, eqApp, lift, liftN] using HG
  exact hc (.skip .refl) hΓ hΓ' (propositionEq_typed heq hP hP)
    (propositionEq_typed heq hP hQ) HG'

end Lean4Lean.VEnv.Strengthening
