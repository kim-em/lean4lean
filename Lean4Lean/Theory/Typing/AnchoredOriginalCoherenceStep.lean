import Lean4Lean.Theory.Typing.AnchoredOriginalStateFold
import Lean4Lean.Theory.Typing.AnchoredOriginalVariableCase
import Lean4Lean.Theory.Typing.AnchoredOriginalSortCase
import Lean4Lean.Theory.Typing.AnchoredOriginalConstantCase
import Lean4Lean.Theory.Typing.AnchoredOriginalEliminatorCase
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationCase
import Lean4Lean.Theory.Typing.AnchoredOriginalLambdaCase
import Lean4Lean.Theory.Typing.AnchoredOriginalPiCase

/-! The nonprojection step of original displayed type coherence. Its only
semantic hypotheses are the strictly earlier original F and displayed C
clauses of the combined well-founded induction. Projection remains an explicit
syntactic branch boundary; this file does not assert global coherence. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Fixed smaller original endpoint pairs, with both source environments
retained separately from the final environment. -/
def CoherenceBelow (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (bound : Nat) : Prop :=
  ∀ {leftEnv rightEnv displayed expression leftType rightType}
    (left : EndpointDisplay leftEnv U displayed expression leftType)
    (right : EndpointDisplay rightEnv U displayed expression rightType),
    leftEnv ≤ env → rightEnv ≤ env →
    schedule .coherence (left.cost + right.cost) < bound →
    DisplayCoherence env U registry left right

/-- Exactly the seven source-expression cases assembled below. -/
def NonProjection : VExpr → Prop
  | .proj .. => False
  | _ => True

/-- All original formation and prefix calls are discharged from the same
lower F hypothesis. Body/function comparisons are fixed smaller pairs.
Eliminator uniqueness is declaration metadata, not a source typing principle. -/
theorem EndpointDisplay.coherenceStep
    (left : EndpointDisplay leftEnv U displayed expression leftType)
    (right : EndpointDisplay rightEnv U displayed expression rightType)
    (henv : env.Ordered) (hscoped : registry.Scoped) (unique : env.EliminatorsUnique)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (leftF : FundamentalBelow leftEnv env U registry (schedule .coherence (left.cost + right.cost)))
    (rightF : FundamentalBelow rightEnv env U registry (schedule .coherence (left.cost + right.cost)))
    (comparisons : CoherenceBelow env U registry (schedule .coherence (left.cost + right.cost)))
    (nonprojection : NonProjection expression) :
    DisplayCoherence env U registry left right := by
  cases expression with
  | bvar index =>
    apply left.variableCoherence right henv hscoped leftBelow rightBelow
    · constructor
      · intro source first second type original call
        exact leftF _ original (left.variablePrefix.conversion_schedule call right.cost)
      · apply StateFundamental.ofBelow henv hscoped leftBelow leftF
        · exact left.variablePrefix.selected.view.location.originalDomains
        · exact left.variablePrefix.formation_schedule right.cost
    · intro source first second type original call
      apply rightF _ original
      simpa only [Nat.add_comm] using right.variablePrefix.conversion_schedule call left.cost
  | sort level =>
    apply left.sortCoherence right henv hscoped leftBelow rightBelow
    · intro source first second type original call
      exact leftF _ original (left.sortPrefix.conversion_schedule call right.cost)
    · intro source first second type original call
      apply rightF _ original
      simpa only [Nat.add_comm] using right.sortPrefix.conversion_schedule call left.cost
  | const name levels =>
    apply left.constantCoherence right henv hscoped leftBelow rightBelow
    · intro source first second type original call
      exact leftF _ original (left.constantPrefix.call_schedule call right.cost)
    · intro source first second type original call
      apply rightF _ original
      simpa only [Nat.add_comm] using right.constantPrefix.call_schedule call left.cost
  | elim block index levels =>
    apply left.eliminatorCoherence right henv hscoped unique leftBelow rightBelow
    · constructor
      · intro source first second type original call
        exact leftF _ original (left.eliminatorPrefix.conversion_schedule call right.cost)
      · intro source first second type original call
        exact leftF _ original (left.eliminatorPrefix.ambient_schedule call right.cost)
    · constructor
      · intro source first second type original call
        apply rightF _ original
        simpa only [Nat.add_comm] using right.eliminatorPrefix.conversion_schedule call left.cost
      · intro source first second type original call
        apply rightF _ original
        simpa only [Nat.add_comm] using right.eliminatorPrefix.ambient_schedule call left.cost
  | app function argument =>
    apply left.applicationCoherence right henv hscoped leftBelow rightBelow
    constructor
    · intro source first second type original call
      exact leftF _ original (left.applicationPrefix.conversion_schedule call right.cost)
    · intro source first second type original call
      apply rightF _ original
      simpa only [Nat.add_comm] using right.applicationPrefix.conversion_schedule call left.cost
    · apply StateFundamental.ofBelow henv hscoped leftBelow leftF
      · exact (Located.appArgument left.applicationPrefix.selected.view.location).originalDomains
      · exact left.applicationPrefix.argument_schedule right.cost
    · apply StateFundamental.ofBelow henv hscoped rightBelow rightF
      · exact (Located.appDomain right.applicationPrefix.selected.view.location).originalDomains
      · simpa only [Nat.add_comm] using (right.applicationPrefix.formation_schedule left.cost).1
    · apply StateFundamental.ofBelow henv hscoped rightBelow rightF
      · exact (Located.appCodomain right.applicationPrefix.selected.view.location).originalDomains
      · simpa only [Nat.add_comm] using (right.applicationPrefix.formation_schedule left.cost).2
    · exact comparisons _ _ leftBelow rightBelow
        (left.applicationPrefix.function_pair_schedule right.applicationPrefix)
  | lam annotation body =>
    apply left.lambdaCoherence right henv hscoped leftBelow rightBelow
    · constructor
      · intro source first second type original call
        exact leftF _ original (left.lambdaPrefix.conversion_schedule call right.cost)
      · apply StateFundamental.ofBelow henv hscoped leftBelow leftF
        · exact (Located.lamDomain left.lambdaPrefix.selected.view.location).originalDomains
        · exact (left.lambdaPrefix.formation_schedule right.cost).1
      · apply StateFundamental.ofBelow henv hscoped leftBelow leftF
        · exact (Located.lamCodomain left.lambdaPrefix.selected.view.location).originalDomains
        · exact (left.lambdaPrefix.formation_schedule right.cost).2
    · constructor
      · intro source first second type original call
        apply rightF _ original
        simpa only [Nat.add_comm] using right.lambdaPrefix.conversion_schedule call left.cost
      · apply StateFundamental.ofBelow henv hscoped rightBelow rightF
        · exact (Located.lamDomain right.lambdaPrefix.selected.view.location).originalDomains
        · simpa only [Nat.add_comm] using (right.lambdaPrefix.formation_schedule left.cost).1
      · apply StateFundamental.ofBelow henv hscoped rightBelow rightF
        · exact (Located.lamCodomain right.lambdaPrefix.selected.view.location).originalDomains
        · simpa only [Nat.add_comm] using (right.lambdaPrefix.formation_schedule left.cost).2
    · exact comparisons _ _ leftBelow rightBelow (left.lambdaPrefix.body_pair_schedule right.lambdaPrefix)
  | forallE annotation body =>
    apply left.piCoherence right henv hscoped leftBelow rightBelow
    constructor
    · intro source first second type original call
      exact leftF _ original (left.piPrefix.conversion_schedule call right.cost)
    · intro source first second type original call
      apply rightF _ original
      simpa only [Nat.add_comm] using right.piPrefix.conversion_schedule call left.cost
    · exact comparisons _ _ leftBelow rightBelow (left.piPrefix.child_pair_schedule right.piPrefix).1
    · exact comparisons _ _ leftBelow rightBelow (left.piPrefix.child_pair_schedule right.piPrefix).2
  | proj name index major => exact nonprojection.elim

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
