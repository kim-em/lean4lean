import Lean4Lean.Theory.Typing.AnchoredOriginalParameterCaptureStep

/-! Exact source displays for retained original equality routes. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail

def parameterEqualitySide
    (original : Derivation sourceEnv U source A B (.sort level)) (left : Bool) :
    EndpointRef sourceEnv U source (if left then A else B) (.sort level) := by
  cases left
  · exact .right original
  · exact .left original

noncomputable def parameterEqualityDisplay
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (original : Derivation sourceEnv U source A B (.sort level)) (left : Bool) :
    OriginalNestedDisplay U common ((if left then A else B).subst raw) (.sort level) :=
  graph.parameterCellDisplay (parameterEqualitySide original left) (.ofLocation .here context)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
