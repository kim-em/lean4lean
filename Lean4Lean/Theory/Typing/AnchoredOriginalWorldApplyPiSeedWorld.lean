import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiReplayBound
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteBoundary
import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiSeedHistory

/-! The actual argument seed reserve, computed from the selected source and whole-history ledgers. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

private theorem applicationSeedWorld_worlds
    {strata : EquationStratification env}
    {sourceEnv headerEnv : VEnv}
    (argument : EndpointState sourceEnv U source a A)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (headerDomain : EndpointRef headerEnv U headerSource C (.sort cu))
    (sourceControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata headerEnv)
    (sourceWorld : WorldEnvironmentProvenance strata U sourceEnvironment)
    (priorWorld : WorldEnvironmentProvenance strata U headerEnvironment)
    (wholeWorld : WorldEnvironmentProvenance strata U wholeReserve)
    (claim : claimedSeedReserve =
      ([Closure.bundle (.close (argument.typeFormation.node.dependencyOrigin sourceControls.ordered) sourceEnvironment)
        (.close (domain.dependencyOrigin sourceControls.ordered) sourceEnvironment)] ++ wholeReserve) ++
      [Closure.bundle (.close (headerDomain.dependencyOrigin headerControls.ordered) headerEnvironment)
        (.close (headerDomain.dependencyOrigin headerControls.ordered) headerEnvironment)]) :
    (applicationSeedWorld argument domain headerDomain sourceControls headerControls sourceWorld priorWorld wholeWorld claim).worlds =
      [originalCallWorld sourceControls .expressionReindex argument.typeFormation.node sourceWorld,
       originalCallWorld sourceControls .expressionReindex (.ref domain) sourceWorld] ++ wholeWorld.worlds ++
      [originalCallWorld headerControls .expressionReindex (.ref headerDomain) priorWorld,
       originalCallWorld headerControls .expressionReindex (.ref headerDomain) priorWorld] := by
  cases claim
  simp only [applicationSeedWorld, WorldEnvironmentProvenance.worlds_append]
  rfl

/-- The full seed reserve is annotated from the actual argument formation,
the retained whole history, and the actual declared-domain reframe. -/
noncomputable def OriginalApplyPiHistory.argumentSeedWorld
    {strata : EquationStratification env}
    {left : OriginalApplicationTypeRouteSide U common}
    {right : OriginalPiTypeRouteSide U common}
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right)
    (sourceControls : OriginalWorldControls strata left.sourceEnv)
    (headerControls : OriginalWorldControls strata right.sourceEnv)
    (sourceWorld : WorldEnvironmentProvenance strata U
      (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered))
    (priorWorld : WorldEnvironmentProvenance strata U history.final)
    (wholeInputs : history.whole.WorldInputs strata) :
    WorldEnvironmentProvenance strata U history.argumentSeedReserve :=
  applicationSeedWorld left.argument left.domain history.rightDomain sourceControls headerControls
    sourceWorld priorWorld (history.whole.worldReserve wholeInputs) (by
      simp only [OriginalApplyPiHistory.argumentSeedReserve, OriginalApplyPiHistory.argumentDomainRoute,
        RawGeneratedTypeRoute.reserve, history.rightDomainEq]
      rfl)

theorem OriginalApplyPiHistory.argumentSeedWorld_worlds
    {strata : EquationStratification env}
    {left : OriginalApplicationTypeRouteSide U common}
    {right : OriginalPiTypeRouteSide U common}
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right)
    (sourceControls : OriginalWorldControls strata left.sourceEnv)
    (headerControls : OriginalWorldControls strata right.sourceEnv)
    (sourceWorld : WorldEnvironmentProvenance strata U
      (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered))
    (priorWorld : WorldEnvironmentProvenance strata U history.final)
    (wholeInputs : history.whole.WorldInputs strata) :
    (history.argumentSeedWorld sourceControls headerControls sourceWorld priorWorld wholeInputs).worlds =
      [originalCallWorld sourceControls .expressionReindex left.argument.typeFormation.node sourceWorld,
       originalCallWorld sourceControls .expressionReindex (.ref left.domain) sourceWorld] ++
      (history.whole.worldReserve wholeInputs).worlds ++
      [originalCallWorld headerControls .expressionReindex right.domain priorWorld,
       originalCallWorld headerControls .expressionReindex (.ref history.rightDomain) priorWorld] := by
  unfold argumentSeedWorld
  rw [applicationSeedWorld_worlds]
  simp only [history.rightDomainEq]


/-- The fixed application result envelope contains exactly this history's
seed reserve and baseline group. Its owner ledger is explicit and is never
recovered from the source frame's numerical capacity. -/
noncomputable def OriginalApplyPiHistory.outputWorld
    {strata : EquationStratification env}
    {left : OriginalApplicationTypeRouteSide U common}
    {right : OriginalPiTypeRouteSide U common}
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right)
    (field : EndpointRef left.sourceEnv U left.source fieldExpression fieldType)
    (major : EndpointRef left.sourceEnv U left.source majorExpression majorType)
    (sourceControls : OriginalWorldControls strata left.sourceEnv)
    (headerControls : OriginalWorldControls strata right.sourceEnv)
    (ownerWorld : WorldEnvironmentProvenance strata U ownerInitial)
    (sourceWorld : WorldEnvironmentProvenance strata U
      (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered))
    (priorWorld : WorldEnvironmentProvenance strata U history.final)
    (wholeInputs : history.whole.WorldInputs strata) :
    WorldEnvironmentProvenance strata U (history.outputEnvironment field major ownerInitial) :=
  .groupHistory field major history.rightDomain sourceControls headerControls ownerWorld priorWorld
    (history.argumentSeedWorld sourceControls headerControls sourceWorld priorWorld wholeInputs)


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
