import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedFirstHeadStep
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSemanticRecovery
import Lean4Lean.Theory.Typing.Strengthening.EqRecResultBoundary

/-! # A canonical equality probe for semantic head exposure

The probe returns Prop through a constant motive. It is always typed in the
presence of an equality proof, while definitional equality of the endpoints
makes it definitionally Prop. Sort exposure must therefore cross an actual
Eq.rec primitive prefix; computing its arguments alone cannot suffice.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A type-valued constant-motive recursor, used to test arbitrary proposition
endpoint conversion. Its equality major need not have a constructor head. -/
def eqSortProbe (P Q q : VExpr) : VExpr :=
  eqRecApp (.succ (.succ .zero)) (.succ .zero) (.sort .zero) P
    (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ .zero)))
    (.sort .zero) Q q

/-- The probe has a fixed universe independently of definitional endpoint
conversion. Only the propositional equality major is needed for its typing. -/
theorem eqSortProbe_typed (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q)) :
    env.HasType univs Γ (eqSortProbe P Q q) (.sort (.succ .zero)) :=
  constant_eqRec_typed henv heq (by trivial) (by trivial) hΓ
    (HasType.sort (by trivial)) hP (HasType.sort (by trivial))
    (HasType.sort (by trivial)) hQ hq

/-- Actual definitional endpoint conversion licenses K and makes the probe
equal to the literal universe Prop. This does not assume head exposure. -/
theorem eqSortProbe_defeq (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (HPQ : env.IsDefEqU univs Γ P Q) :
    env.IsDefEq univs Γ (eqSortProbe P Q q) (.sort .zero) (.sort (.succ .zero)) :=
  eqRecApp_simAt henv heq hΓ HPQ _ (eqSortProbe_typed heq hΓ hP hQ hq)

/-- The typed probe erases to a fixed six-argument spine. Its equality major
is the proof marker even when the supplied proof has no constructor head. -/
theorem eqSortProbe_erase (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q)) :
    proofErase Γ (eqSortProbe P Q q) =
      mkApps (.const ``Eq.rec [.succ (.succ .zero), .succ .zero])
        [.sort .zero, proofErase Γ P,
          proofErase Γ (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ .zero))),
          .sort .zero, proofErase Γ Q, .proof] := by
  have ht := eqSortProbe_typed heq hΓ hP hQ hq
  have HE := proofErase_const_spine hΓ (args := [.sort .zero, P,
    constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ .zero)),
    .sort .zero, Q, q]) ht (not_isProof_of_sort hΓ ht)
  change proofErase Γ (eqSortProbe P Q q) = _ at HE
  have Hq : proofErase Γ q = .proof := proofErase_eq_proof.2
    ⟨_, hq, HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP hQ⟩
  have HS : proofErase Γ (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))
  simpa only [List.map_cons, List.map_nil, Hq, HS] using HE

/-- Missing adequacy only for the fixed constant-motive Eq probe. Ordinary
endpoint conversion must produce some literal sort by erased computation.
No exposure for arbitrary types, Pis, or structure families is requested.
The definition does not assert a strict reduction from PropositionFront. -/
def EqProbeSortExposure
    (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ P Q q}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ P (.sort .zero) → env.HasType univs Γ Q (.sort .zero) →
    env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q) →
    env.IsDefEqU univs Γ P Q →
    ∃ w, ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ (eqSortProbe P Q q)) (.sort w)

/-- General semantic head exposure supplies the restricted probe obligation
using only its sort component. The other two components are irrelevant here. -/
theorem ScopedSemanticHeadExposure.eq_probe_sort
    (H : ScopedSemanticHeadExposure Step) (heq : env.HasCanonicalEq) : EqProbeSortExposure Step := by
  intro Γ P Q q hΓ hP hQ hq HPQ
  exact H.sort hΓ (eqSortProbe_typed heq hΓ hP hQ hq)
    ⟨_, eqSortProbe_defeq heq hΓ hP hQ hq HPQ⟩

/-- Sort exposure of this probe must use a primitive at a computed Eq.rec
prefix. The witness includes the preceding paths for every supplied argument;
no choice of prefix arity or singleton rule is assumed. -/
theorem EqProbeSortExposure.head_occurrence
    (H : EqProbeSortExposure Step) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (HPQ : env.IsDefEqU univs Γ P Q) :
    ScopedHeadOccurrence Step (proofEraseCtx Γ) ``Eq.rec
      [.succ (.succ .zero), .succ .zero]
      [.sort .zero, proofErase Γ P,
        proofErase Γ (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ .zero))),
        .sort .zero, proofErase Γ Q, .proof] := by
  obtain ⟨w, R⟩ := H hΓ hP hQ hq HPQ
  rw [eqSortProbe_erase heq hΓ hP hQ hq] at R
  exact R.head_occurrence (by simp only [constHead, ne_eq, reduceCtorEq, not_false_eq_true])

/-- Sort exposure of this probe must use a primitive at a computed Eq.rec
prefix. The witness includes the preceding paths for every supplied argument;
no choice of prefix arity or singleton rule is assumed. -/
theorem ScopedSemanticHeadExposure.eq_probe_head_occurrence
    (H : ScopedSemanticHeadExposure Step) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (HPQ : env.IsDefEqU univs Γ P Q) :
    ScopedHeadOccurrence Step (proofEraseCtx Γ) ``Eq.rec
      [.succ (.succ .zero), .succ .zero]
      [.sort .zero, proofErase Γ P,
        proofErase Γ (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ .zero))),
        .sort .zero, proofErase Γ Q, .proof] :=
  EqProbeSortExposure.head_occurrence (H.eq_probe_sort heq) heq hΓ hP hQ hq HPQ

end Lean4Lean.VEnv.Strengthening
