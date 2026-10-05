import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryProvenance
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryReply

/-! The record R-to-F continuation belongs above the query annotations and
actual bounded replies; the finite query-provenance grammar does not depend
on the replay interpreter. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- The actual first-R to forward-F seam: extract the record observer in the
SAME returned frame, retain its computed foreign dependencies, and lower the
destination call while keeping the source sponsor. Coverage and individual
opening bounds are still obligations of the R producer, not consequences of
numeric capacity or this annotation. -/
theorem BoundedGeneratedQueryReply.recordContinuation
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {strata : EquationStratification env}
    (henv : env.Ordered) (ordered : display.sourceEnv.Ordered)
    (prior : OriginalCaptureRealization display.graph env registry target
      locals commonLeft commonRight available)
    (reply : BoundedGeneratedQueryReply base caps display commonLeft commonRight
      (Profile.singleton (n := n + 1) (.record (record : RecordData (Profile n))))
      (environmentCost (prior.frame.dependencyEnvironment ordered)))
    (annotation : WorldObsProvenance strata reply.answer.reply.query.observation)
    (cutoff : Nat) (fuel : Nat → Nat)
    (source : EquationWorldClosureOrder.World strata.rules.length)
    (priorCaptures nextCaptures : List (EquationWorldClosureOrder.World strata.rules.length))
    (covered : EquationWorldClosureOrder.Covered (@EquationControlMeasure.Less strata.rules.length)
      nextCaptures priorCaptures)
    (foreignBound : ∀ child ∈ annotation.worlds,
      EquationWorldClosureOrder.WorldBelow strata.rules.length child source) :
    let previous := EquationWorldClosureOrder.Closure.node
      (EquationControlMeasure.key strata.rules.length cutoff fuel ordered.constantCount
        (richSchedule .expressionReindex
          (Closure.close (display.node.dependencyOrigin ordered)
            (prior.frame.dependencyEnvironment ordered)).cost)) priorCaptures
    let next := EquationWorldClosureOrder.Closure.node
      (EquationControlMeasure.key strata.rules.length cutoff fuel ordered.constantCount
        (richSchedule .fundamental
          (Closure.close (display.node.dependencyOrigin ordered)
            (reply.answer.reply.realization.frame.dependencyEnvironment ordered)).cost)) nextCaptures
    ∃ footprint, ∃ observation : RichObs display.sourceEnv env U registry target display.node
      reply.answer.reply.locals (display.raw.comp commonLeft)
      (Profile.singleton (n := n + 1) (.record record)) footprint,
      ∃ output : WorldObsProvenance strata observation,
        footprint.Available reply.answer.reply.available ∧ output.worlds = annotation.worlds ∧
        EquationWorldClosureOrder.CallBelow strata.rules.length [source, next] [source, previous] ∧
        EquationWorldClosureOrder.Sponsored [source, next] (output.worlds ++ nextCaptures) := by
  obtain ⟨footprint, observation, output, resources, same⟩ :=
    reply.answer.reply.query.recordObservation_worlds henv annotation
  obtain ⟨decrease, sponsored⟩ := reply.sponsoredFundamentalDecrease ordered prior
    strata.rules.length cutoff fuel source priorCaptures nextCaptures annotation.worlds covered foreignBound
  exact ⟨footprint, observation, output, resources, same, decrease, by simpa only [same] using sponsored⟩


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
