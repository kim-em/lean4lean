import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeDependencyInterpretation
import Lean4Lean.Theory.Typing.AnchoredSortableVariableTraceCompile
import Lean4Lean.Theory.Typing.AnchoredSortablePruning

/-! Literal-variable queries, including charged recipes, compile to ordinary
source syntax by evaluating their retained dependency programs. The original
API requires only actual resources in a singleton-closed table. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

 theorem RichObs.variableQuery
    {node : EndpointState sourceEnv U source (.bvar index) assigned}
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (closed : available.AtomClosed) (resources : footprint.Available available) :
    ∃ required, Nonempty (SortableObs env U registry target locals σ (.bvar index)
      profile required) ∧ required.Available available := by
  obtain ⟨footprint, ⟨trace⟩, supplied⟩ := query.variableDependency closed resources
  exact ⟨trace.compiledFootprint, ⟨trace.observation locals σ⟩, trace.compiledAvailable supplied⟩

 theorem RichCert.variableQuery
    {node : EndpointState sourceEnv U source (.bvar index) assigned}
    (query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (closed : available.AtomClosed) (resources : footprint.Available available) :
    ∃ required, Nonempty (SortableCert env U registry target locals σ (.bvar index)
      relevant profile required) ∧ required.Available available := by
  obtain ⟨footprint, ⟨trace⟩, supplied⟩ := query.variableDependency closed resources
  exact ⟨trace.compiledFootprint, ⟨.observe (trace.observation locals σ) query.formed⟩,
    trace.compiledAvailable supplied⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
