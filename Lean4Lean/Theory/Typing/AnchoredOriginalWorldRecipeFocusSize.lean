import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeCursor
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalRichRecipeNativeCursor

/-! Focusing follows the finite retained recipe program to its literal root.
The source certificate and its annotation both strictly decrease; no semantic
F result or rebuilt recipe is substituted for the recursive input. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem WorldCodeRecipeProvenance.focusExecutableInputSized
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {strata : EquationStratification env}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (annotation : WorldCodeRecipeProvenance strata recipe)
    (sources : annotation.Sources P) :
    ∃ input : RichRecipeRootInput env U registry target,
      Nonempty (RichRecipeContext input recipe) ∧
      sizeOf input.certificate < sizeOf recipe ∧ input.strata = strata ∧
      P input.owner.selected.origin.source ∧
      ∃ child : WorldCertProvenance strata input.certificate,
      ∃ controls : OriginalWorldControls strata input.owner.selected.origin.source,
      ∃ provenance : EndpointProvenance (.nil : ContextDerivation input.owner.selected.origin.source U []) input.node,
        List.Subset ((WorldQuerySite.empty (registry := registry) (target := target)
          controls provenance input.realization).worlds ++ child.worlds) annotation.worlds ∧
        sizeOf child < sizeOf annotation := by
  match annotation with
  | .root source locals σ owner node closed expressionEq realization certificate supplied child controls provenance =>
    refine ⟨⟨_, _, owner, _, _, _, node, closed, expressionEq, source, locals, σ,
      realization, _, _, _, _, certificate, supplied⟩, ⟨.root⟩, ?_, rfl, sources,
      child, controls, provenance, ?_, ?_⟩
    · simp_wf
      omega
    · exact List.Subset.refl _
    · simp_wf
      omega
  | .domain child =>
    obtain ⟨input, ⟨pending⟩, smaller, strataEq, sourceReady, cert, controls, provenance, included, annotationSmaller⟩ := child.focusExecutableInputSized sources
    refine ⟨input, ⟨.domain pending⟩, Nat.lt_trans smaller ?_, strataEq, sourceReady,
      cert, controls, provenance, included, Nat.lt_trans annotationSmaller ?_⟩
    all_goals simp_wf; omega
  | .body child selected anchor =>
    obtain ⟨input, ⟨pending⟩, smaller, strataEq, sourceReady, cert, controls, provenance, included, annotationSmaller⟩ := child.focusExecutableInputSized sources
    refine ⟨input, ⟨.body pending selected anchor⟩, Nat.lt_trans smaller ?_, strataEq, sourceReady,
      cert, controls, provenance, included, Nat.lt_trans annotationSmaller ?_⟩
    all_goals simp_wf; omega
  | .fixedBody child selected admitted =>
    obtain ⟨input, ⟨pending⟩, smaller, strataEq, sourceReady, cert, controls, provenance, included, annotationSmaller⟩ := child.focusExecutableInputSized sources
    refine ⟨input, ⟨.fixedBody pending selected admitted⟩, Nat.lt_trans smaller ?_, strataEq, sourceReady,
      cert, controls, provenance, included, Nat.lt_trans annotationSmaller ?_⟩
    all_goals simp_wf; omega
  | .resources child transfer =>
    obtain ⟨input, ⟨pending⟩, smaller, strataEq, sourceReady, cert, controls, provenance, included, annotationSmaller⟩ := child.focusExecutableInputSized sources
    refine ⟨input, ⟨.resources pending _⟩, Nat.lt_trans smaller ?_, strataEq, sourceReady,
      cert, controls, provenance, ?_, Nat.lt_trans annotationSmaller ?_⟩
    · simp_wf
      omega
    · intro world member
      exact List.mem_append_left _ (included member)
    · simp_wf
      omega
  | .action change child =>
    obtain ⟨input, ⟨pending⟩, smaller, strataEq, sourceReady, cert, controls, provenance, included, annotationSmaller⟩ := child.focusExecutableInputSized sources
    refine ⟨input, ⟨.action pending change⟩, Nat.lt_trans smaller ?_, strataEq, sourceReady,
      cert, controls, provenance, included, Nat.lt_trans annotationSmaller ?_⟩
    all_goals simp_wf; omega

termination_by sizeOf annotation
decreasing_by all_goals simp_wf; omega


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
