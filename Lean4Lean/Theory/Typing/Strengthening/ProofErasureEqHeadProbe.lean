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
        .sort .zero, proofErase Γ Q, .proof] := by
  have ht := eqSortProbe_typed heq hΓ hP hQ hq
  obtain ⟨w, R⟩ := H.sort hΓ ht ⟨_, eqSortProbe_defeq heq hΓ hP hQ hq HPQ⟩
  have HE := proofErase_const_spine hΓ (args := [.sort .zero, P,
    constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ .zero)),
    .sort .zero, Q, q]) ht (not_isProof_of_sort hΓ ht)
  change proofErase Γ (eqSortProbe P Q q) = _ at HE
  rw [HE] at R
  have Hq : proofErase Γ q = .proof := proofErase_eq_proof.2
    ⟨_, hq, HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP hQ⟩
  have HS : proofErase Γ (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))
  simpa only [List.map_cons, List.map_nil, Hq, HS] using
    R.head_occurrence (by simp only [constHead, ne_eq, reduceCtorEq, not_false_eq_true])

end Lean4Lean.VEnv.Strengthening
