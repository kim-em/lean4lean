import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationTypeRouteSide

/-! The finite source data for specializing a function-type history at an
actual argument. The left Pi is the application's retained formation node;
the two codomains keep their original contexts and explicit capture maps.
This file does not assert the still separate semantic row/capture replay. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- A later-prefix specialization retains the whole previous Pi history.
In particular its next domain history is a strict subhistory, rather than a
completed semantic alignment supplied by the caller. -/
structure OriginalApplyPiHistory
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (commonLeft commonRight : Subst)
    (left : OriginalApplicationTypeRouteSide U common)
    (right : OriginalPiTypeRouteSide U common) where
  leftOrdered : left.sourceEnv.Ordered
  rightOrdered : right.sourceEnv.Ordered
  leftBelow : left.sourceEnv ≤ env
  rightDomain : EndpointRef right.sourceEnv U right.source right.A (.sort right.u)
  rightDomainEq : right.domain = .ref rightDomain
  sourceFrame : OriginalTypeRouteFrame env registry target left.graph commonLeft commonRight
  headerFrame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight
  whole : RawGeneratedTypeRoute env registry target commonLeft commonRight
    left.pi.display right.display
    (sourceFrame.realization.frame.dependencyEnvironment leftOrdered)
    (headerFrame.realization.frame.dependencyEnvironment rightOrdered)

variable {U : Nat} {common : List VExpr}
  {left : OriginalApplicationTypeRouteSide U common}
  {right : OriginalPiTypeRouteSide U common}

noncomputable def OriginalApplyPiHistory.final
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right) : List Closure :=
  history.headerFrame.realization.frame.dependencyEnvironment history.rightOrdered

noncomputable def OriginalApplyPiHistory.destination
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right) :
    OriginalNestedDisplay U common
      (right.B.subst (right.raw.cons (left.a.subst left.raw))) (.sort right.v) :=
  right.capturedBody history.rightDomain history.rightDomainEq left

/-- The actual assigned formation of the argument first changes occurrence
at the SAME raw source type, then follows the previous whole-Pi history's
domain projection. No argument typing at the declared domain is invented. -/
noncomputable def OriginalApplyPiHistory.argumentDomainRoute
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right) :
    RawGeneratedTypeRoute env registry target commonLeft commonRight
      left.argumentDisplay.formationDisplay right.domainDisplay
      (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered) history.final :=
  .trans
    (.same left.argumentDisplay.formationDisplay left.pi.domainDisplay
      history.leftOrdered history.leftOrdered
      (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered) history.sourceFrame)
    (.piDomain left.pi right history.leftBelow history.whole)

/-- Reserve the exact application and header-Pi closures as self-pairs. All
new child calls lie below their respective parent; the child history keeps
its complete reserve even though replay changes the queried Pi profile. -/
noncomputable def OriginalApplyPiHistory.reserve
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right) : List Closure :=
  let application := Closure.close (left.node.dependencyOrigin history.leftOrdered)
    (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)
  let header := Closure.close ((EndpointState.pi right.hu right.hv right.domain right.body).dependencyOrigin history.rightOrdered)
    history.final
  history.whole.reserve ++ [.bundle application application, .bundle header header]

noncomputable def OriginalApplyPiHistory.schedule
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right) : Nat :=
  max history.whole.schedule
    (max
      (richSchedule .fundamental (Closure.close (left.node.dependencyOrigin history.leftOrdered)
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost)
      (richSchedule .fundamental (Closure.close
        ((EndpointState.pi right.hu right.hv right.domain right.body).dependencyOrigin history.rightOrdered)
        history.final).cost))

private theorem environment_append (first second : List Closure) :
    environmentCost (first ++ second) = max (environmentCost first) (environmentCost second) := by
  induction first with
  | nil => simp [environmentCost]
  | cons head tail ih => simp only [List.cons_append, environmentCost, ih, Nat.max_assoc]

theorem OriginalApplyPiHistory.schedule_le
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right) :
    history.schedule ≤ richSchedule .expressionReindex (environmentCost history.reserve) := by
  have child := history.whole.schedule_le
  simp only [schedule, reserve, environment_append, environmentCost, Closure.cost,
    Nat.max_zero, richSchedule, RichPhase.code] at child ⊢
  omega

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
