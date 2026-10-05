import Lean4Lean.Theory.Typing.AnchoredOriginalRichRecipeCursor
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryProvenance

/-! Focusing keeps the exact retained input annotation. It never reinitializes
canonical controls or invents a new sponsor when crossing a charged leaf. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalEndpointFactor
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem WorldCodeRecipeProvenance.focusInput
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {strata : EquationStratification env}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (annotation : WorldCodeRecipeProvenance strata recipe) :
    ∃ input : RichRecipeRootInput env U registry target,
      Nonempty (RichRecipeContext input recipe) ∧
      sizeOf input.certificate < sizeOf recipe ∧ input.strata = strata ∧
      ∃ child : WorldCertProvenance strata input.certificate,
      ∃ controls : OriginalWorldControls strata input.owner.selected.origin.source,
      ∃ provenance : EndpointProvenance (.nil : ContextDerivation input.owner.selected.origin.source U []) input.node,
        List.Subset ((WorldQuerySite.empty (registry := registry) (target := target)
          controls provenance input.realization).worlds ++ child.worlds) annotation.worlds := by
  match annotation with
  | .root source locals σ owner node closed expressionEq realization certificate supplied child controls provenance =>
    refine ⟨⟨_, _, owner, _, _, _, node, closed, expressionEq, source, locals, σ,
      realization, _, _, _, _, certificate, supplied⟩, ⟨.root⟩, ?_, rfl,
      child, controls, provenance, ?_⟩
    · simp_wf
      omega
    · exact List.Subset.refl _
  | .domain child =>
    obtain ⟨input, ⟨pending⟩, smaller, strataEq, cert, controls, provenance, included⟩ := child.focusInput
    refine ⟨input, ⟨.domain pending⟩, Nat.lt_trans smaller ?_, strataEq,
      cert, controls, provenance, included⟩
    simp_wf
    omega
  | .body child selected anchor =>
    obtain ⟨input, ⟨pending⟩, smaller, strataEq, cert, controls, provenance, included⟩ := child.focusInput
    refine ⟨input, ⟨.body pending selected anchor⟩, Nat.lt_trans smaller ?_, strataEq,
      cert, controls, provenance, included⟩
    simp_wf
    omega
  | .fixedBody child selected admitted =>
    obtain ⟨input, ⟨pending⟩, smaller, strataEq, cert, controls, provenance, included⟩ := child.focusInput
    refine ⟨input, ⟨.fixedBody pending selected admitted⟩, Nat.lt_trans smaller ?_, strataEq,
      cert, controls, provenance, included⟩
    simp_wf
    omega
  | .resources child transfer =>
    obtain ⟨input, ⟨pending⟩, smaller, strataEq, cert, controls, provenance, included⟩ := child.focusInput
    refine ⟨input, ⟨.resources pending _⟩, Nat.lt_trans smaller ?_, strataEq,
      cert, controls, provenance, ?_⟩
    · simp_wf
      omega
    · intro world member
      exact List.mem_append_left _ (included member)
  | .action change child =>
    obtain ⟨input, ⟨pending⟩, smaller, strataEq, cert, controls, provenance, included⟩ := child.focusInput
    refine ⟨input, ⟨.action pending change⟩, Nat.lt_trans smaller ?_, strataEq,
      cert, controls, provenance, included⟩
    simp_wf
    omega

termination_by sizeOf annotation
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
