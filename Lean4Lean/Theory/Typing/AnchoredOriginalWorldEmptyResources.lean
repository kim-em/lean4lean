import Lean4Lean.Theory.Typing.AnchoredOriginalWorldGeneration

/-! Positive generation at the actual empty capture graph preserves an
empty resource table, including merges of selected replies. This conclusion
uses the graph constructors rather than the shape or cost of a raw frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

private def emptyGraphResources
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw) (available : Valuation) : Prop :=
  match graph with
  | .empty _ => available = (fun _ => [])
  | _ => True

private theorem emptyGraphResources_merge
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (one : emptyGraphResources graph left) (two : emptyGraphResources graph right) :
    emptyGraphResources graph (fun i => left i ++ right i) := by
  cases graph <;> try trivial
  change left = (fun _ => []) at one
  change right = (fun _ => []) at two
  rw [one, two]
  rfl

private theorem WorldGenerated.empty_property
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame controls) :
    emptyGraphResources graph available := by
  induction generated with
  | merge first second one two => exact emptyGraphResources_merge _ one two
  | empty => rfl
  | identity => trivial
  | bind => trivial
  | weaken => trivial
  | capture => trivial
  | historyGroup => trivial

/-- The selected table is literally empty, even when the selected raw
frame was reconstructed as a merge. -/
theorem WorldGenerated.emptyAvailable
    {base : OriginalCaptureBase env U registry target}
    {frame : RawOriginalRichFrame sourceEnv env U registry target .nil locals σ τ available}
    (generated : WorldGenerated strata P base caps commonLeft commonRight
      (.empty common) frame controls) : available = (fun _ => []) :=
  generated.empty_property

/-- In particular every actual admitted query at that selected frame has
an empty footprint. No annotation or query is independently reselected. -/
theorem WorldGenerated.emptyFootprint
    {base : OriginalCaptureBase env U registry target}
    {frame : RawOriginalRichFrame sourceEnv env U registry target .nil locals σ τ available}
    (generated : WorldGenerated strata P base caps commonLeft commonRight
      (.empty common) frame controls)
    {footprint : Footprint}
    (resources : footprint.Available available) : footprint = [] := by
  rw [generated.emptyAvailable] at resources
  apply List.eq_nil_iff_forall_not_mem.mpr
  rintro ⟨index, need⟩ member
  exact nomatch resources index need member

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
