import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRouteGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedAssignedComparison
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationReplayCalls
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedTypedEquality

/-! The exact original F/R/C clauses used by a finite raw history. The
predicate is independent of its generated-frame proof and of semantic replay. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target common : List VExpr}

def RawGeneratedTypeRoute.Calls
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final)
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    (limit : Nat) : Prop :=
  match route with
  | .identity .. => True
  | .same left right lf rf _ _ =>
      GeneratedObservationCall base commonCaps left right commonLeft commonRight lf rf limit
  | .equality (context := context) _ original forward ordered _ _ =>
      ParameterEqualityInductionAt env registry ordered context original forward limit
  | .typedEquality (context := context) graph original left expressionEq lf ordered _ _ _ =>
      GeneratedObservationCall base commonCaps (expressionEq ▸ left) (graph.typeEqualityDisplay original true)
        commonLeft commonRight (by cases expressionEq; exact lf) ordered limit ∧
      GeneratedAssignedCall base commonCaps (expressionEq ▸ left) (graph.typeEqualityDisplay original true)
        commonLeft commonRight (by cases expressionEq; exact lf) ordered limit ∧
      OriginalEqualityInductionAt env registry ordered context original limit
  | .assigned left right lf rf _ _ =>
      GeneratedAssignedCall base commonCaps left right commonLeft commonRight lf rf limit
  | .trans first second => first.Calls base commonCaps limit ∧ second.Calls base commonCaps limit
  | .piDomain _ _ _ route => route.Calls base commonCaps limit
  | .applyPi (initial := initial) (domain := domain) (body := body) (function := function) (argument := argument)
      (result := result) (hu := hu) (hv := hv) (location := location) (sourceGraph := sourceGraph)
      (headerInitial := headerInitial) (headerDomain := headerDomain) (headerBody := headerBody)
      (hcu := hcu) (hdv := hdv) (headerLocation := headerLocation) (headerGraph := headerGraph)
      (sourceOrdered := sourceOrdered) (headerOrdered := headerOrdered) (sourceBelow := sourceBelow)
      (sourceFrame := sourceFrame) (headerFrame := headerFrame) (whole := whole) .. =>
      let history : OriginalApplyPiHistory env registry target commonLeft commonRight
          (originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph)
          (originalNativePiRouteSide headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph) :=
        ⟨sourceOrdered, headerOrdered, sourceBelow, headerDomain, rfl, sourceFrame, headerFrame, whole⟩
      whole.Calls base commonCaps limit ∧
        history.ApplicationCalls initial domain body function argument result hu hv location sourceGraph
          headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph limit
termination_by sizeOf route

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
