import Lean4Lean.Theory.Typing.AnchoredOriginalWorldProvenance
import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRoute

/-! Route-indexed world provenance. The recursive input retains only source
controls and typed environments. The reserve's original endpoints are read
from the route itself, never supplied by a matching numerical ledger. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

noncomputable def RawGeneratedTypeRoute.WorldInputs
    {env : VEnv} (strata : EquationStratification env)
    {left : OriginalNestedDisplay U common le lt}
    {right : OriginalNestedDisplay U common re rt}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final) : Type :=
  match route with
  | .identity .. => Unit
  | .same left right lf rf initial frame | .assigned left right lf rf initial frame =>
      OriginalWorldControls strata left.sourceEnv × OriginalWorldControls strata right.sourceEnv ×
      WorldEnvironmentProvenance strata U initial ×
      WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment rf)
  | .equality (sourceEnv := sourceEnv) _ _ _ _ _ initial =>
      OriginalWorldControls strata sourceEnv × WorldEnvironmentProvenance strata U initial
  | .typedEquality (sourceEnv := sourceEnv) (left := left) (ordered := ordered)
      (environment := initial) (frame := frame) .. =>
      OriginalWorldControls strata left.sourceEnv × OriginalWorldControls strata sourceEnv ×
      WorldEnvironmentProvenance strata U initial ×
      WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment ordered)
  | .trans first second => first.WorldInputs strata × second.WorldInputs strata
  | .piDomain _ _ _ child => child.WorldInputs strata
  | .applyPi (sourceEnv := sourceEnv) (headerEnv := headerEnv)
      (sourceOrdered := sourceOrdered) (headerOrdered := headerOrdered)
      (sourceFrame := sourceFrame) (headerFrame := headerFrame) (whole := whole) .. =>
      OriginalWorldControls strata sourceEnv × OriginalWorldControls strata headerEnv ×
      WorldEnvironmentProvenance strata U (sourceFrame.realization.frame.dependencyEnvironment sourceOrdered) ×
      WorldEnvironmentProvenance strata U (headerFrame.realization.frame.dependencyEnvironment headerOrdered) ×
      whole.WorldInputs strata
termination_by structural route

noncomputable def RawGeneratedTypeRoute.worldReserve
    {env : VEnv} {strata : EquationStratification env}
    {left : OriginalNestedDisplay U common le lt}
    {right : OriginalNestedDisplay U common re rt}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final)
    (inputs : route.WorldInputs strata) :
    WorldEnvironmentProvenance strata U route.reserve :=
  match route, inputs with
  | .identity .., inputs => by
    rw [reserve.eq_def]
    exact .nil
  | .same left right lf rf initial frame, inputs => by
    rw [WorldInputs.eq_def] at inputs
    rw [reserve.eq_def]
    exact .cons (.bundle (.scheduled .expressionReindex left.node inputs.1 inputs.2.2.1)
      (.scheduled .expressionReindex right.node inputs.2.1 inputs.2.2.2)) .nil
  | .assigned left right lf rf initial frame, inputs => by
    rw [WorldInputs.eq_def] at inputs
    rw [reserve.eq_def]
    exact .cons (.bundle (.scheduled .assignedComparison left.node inputs.1 inputs.2.2.1)
      (.scheduled .assignedComparison right.node inputs.2.1 inputs.2.2.2)) .nil
  | .equality graph original forward ordered below initial, inputs => by
    rw [WorldInputs.eq_def] at inputs
    rw [reserve.eq_def]
    exact .cons (.original (.ref (.left original)) inputs.1 inputs.2) .nil
  | .typedEquality graph original left agreement lf ordered below initial frame, inputs => by
    rw [WorldInputs.eq_def] at inputs
    rw [reserve.eq_def]
    let equality := WorldClosureProvenance.original (.ref (.left original)) inputs.2.1 inputs.2.2.2
    exact .cons (.bundle (.scheduled .expressionReindex left.node inputs.1 inputs.2.2.1)
      (.scheduled .expressionReindex (.ref (.left original)) inputs.2.1 inputs.2.2.2))
      (.cons equality .nil)
  | .trans first second, inputs => by
    rw [WorldInputs.eq_def] at inputs
    rw [reserve.eq_def]
    exact (first.worldReserve inputs.1).append (second.worldReserve inputs.2)
  | .piDomain left right below child, inputs => by
    rw [WorldInputs.eq_def] at inputs
    rw [reserve.eq_def]
    exact child.worldReserve inputs
  | .applyPi initial domain body function argument result hu hv location sourceGraph noBinders
      headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph sourceOrdered headerOrdered
      sourceBelow headerBelow sourceFrame headerFrame ownerInitial sourceBound whole claimed, inputs => by
    rw [WorldInputs.eq_def] at inputs
    rw [reserve.eq_def]
    let application := WorldClosureProvenance.original (.app hu hv (.ref domain) body function argument result)
      inputs.1 inputs.2.2.1
    let header := WorldClosureProvenance.original (.pi hcu hdv (.ref headerDomain) headerBody)
      inputs.2.1 inputs.2.2.2.1
    exact (whole.worldReserve inputs.2.2.2.2).append
      (.cons (.bundle application application) (.cons (.bundle header header) .nil))
termination_by structural route

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
