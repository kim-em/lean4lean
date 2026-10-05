import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyReplayAssembly
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureMergePreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldControlPrefix

/-! Retain the concrete prior family prefix after a whole-Pi replay. The
selected query stays unchanged, while both actual generations and their
retained controls are combined in the same maximum-capacity frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- Controlled counterpart of `retainPrefix`, using the actual selected
world generation. Coverage is explicit hereditary evidence about that
selection, not a consequence of its numerical capacity bound. -/
theorem AmbientBoundedParameterReply.retainPrefixControlled
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata display.sourceEnv}
    {frontier : List (World strata.rules.length)}
    (whole : AmbientBoundedParameterReply base caps start display commonLeft commonRight profile capacity)
    (baseline : OriginalTypeRouteFrame env registry target display.graph commonLeft commonRight)
    (selected : WorldGenerated strata P base caps commonLeft commonRight display.graph
      whole.reply.answer.reply.realization.frame.raw controls)
    (previous : WorldGenerated strata P base caps commonLeft commonRight display.graph
      baseline.realization.frame.raw controls)
    (selectedReady : selected.Controlled frontier)
    (previousReady : previous.Controlled frontier)
    (queryReady : ControlledStoredQuery controls frontier (.observation whole.reply.answer.reply.query.observation))
    (selectedPrefix : selected.UsesControlPrefix controls.cutoff controls.fuel)
    (previousPrefix : previous.UsesControlPrefix controls.cutoff controls.fuel)
    (bounded : ∀ ordered : display.sourceEnv.Ordered,
      environmentCost (baseline.realization.frame.dependencyEnvironment ordered) ≤ capacity)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) selected.worlds previous.worlds) :
    ∃ output : AmbientBoundedParameterReply base caps start display commonLeft commonRight profile capacity,
      ∃ generation : WorldGenerated strata P base caps commonLeft commonRight display.graph
          output.reply.answer.reply.realization.frame.raw controls,
        Nonempty (generation.Controlled frontier) ∧
        Nonempty (ControlledStoredQuery controls frontier (.observation output.reply.answer.reply.query.observation)) ∧
        generation.UsesControlPrefix controls.cutoff controls.fuel ∧
        (∀ index need, need ∈ baseline.available index → need ∈ output.reply.answer.reply.available index) ∧
        (∀ index need, need ∈ whole.reply.answer.reply.available index → need ∈ output.reply.answer.reply.available index) ∧
        HEq output.reply.answer.reply.query.observation whole.reply.answer.reply.query.observation ∧
        output.reply.answer.reply.query.footprint = whole.reply.answer.reply.query.footprint ∧
        generation.worlds = selected.worlds ++ previous.worlds ∧
        Covered (@EquationControlMeasure.Less strata.rules.length) generation.worlds previous.worlds := by
  rcases whole with ⟨⟨⟨⟨⟨locals, available, realization, sourceGenerated, query, closed⟩, capped⟩, bound⟩,
    related, path⟩, ambient⟩
  rcases baseline with ⟨oldLocals, oldAvailable, oldRealization, oldClosed⟩
  have sameLocals : oldLocals = locals :=
    previous.erase.ambientGenerated.capped.generated.locals_eq.trans sourceGenerated.locals_eq.symm
  cases sameLocals
  let merged := realization.frame.merge oldRealization.frame
  let generation := selected.merge previous
  have included : ∀ index need, need ∈ available index → need ∈ (available.append oldAvailable) index :=
    fun _ _ member => List.mem_append_left _ member
  have oldIncluded : ∀ index need, need ∈ oldAvailable index → need ∈ (available.append oldAvailable) index :=
    fun _ _ member => List.mem_append_right _ member
  have combinedClosed : (available.append oldAvailable).AtomClosed := by
    intro i need member atom atomMember
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append_left _ (closed i need member atom atomMember)
    · exact List.mem_append_right _ (oldClosed i need member atom atomMember)
  let output : AmbientBoundedParameterReply base caps start display commonLeft commonRight profile capacity := {
    reply := {
      answer := {
        reply := ⟨locals, available.append oldAvailable, ⟨merged, realization.substitutions⟩,
          generation.erase.ambientGenerated.capped.generated, query.availableMono included, combinedClosed⟩
        capped := generation.erase.ambientGenerated.capped }
      bounded := fun ordered => by
        change environmentCost ((realization.frame.merge oldRealization.frame).dependencyEnvironment ordered) ≤ capacity
        rw [OriginalRichFrame.merge_environmentCost]
        exact Nat.max_le.mpr ⟨bound ordered, bounded ordered⟩ }
    related := related
    path := path
    generation := generation.erase.ambientGenerated }
  refine ⟨output, generation, ⟨selectedReady.merge previousReady⟩, ⟨queryReady⟩,
    ⟨selectedPrefix, previousPrefix⟩, oldIncluded, included, HEq.rfl, rfl, ?_, ?_⟩
  · exact WorldGenerated.merge_worlds
  · exact WorldGenerated.retainBaseline_covered covered

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
