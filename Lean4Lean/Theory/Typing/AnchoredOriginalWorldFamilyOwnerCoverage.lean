import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyEntryRestriction
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldOwnerEnvironment

/-! Actual family-entry restriction preserves the selected owner world
annotation. The source admission is a hereditary coverage proof, separate
from the old numeric frame bound. No semantic owner reply is assumed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000


section
variable
    {strata : EquationStratification env}
    {base : OriginalCaptureBase env U registry target}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {controls : OriginalWorldControls strata headerEnv}
    {ownerControls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue}

/-- The finite entries are really constructed by `coverNeedsWorlds` from
this packet. Their exact generations keep its world list, so coverage is
retained even when the requested grades and certificate supports change. -/
theorem WorldFamilyEntry.coverNeedsOwnerCovered
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (packet : WorldFamilyEntry (base := base) P common ownerRaw commonLeft commonRight caps
      controls ownerControls frontier entry)
    (initial : WorldEnvironmentProvenance strata U ownerInitial)
    (ownerCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      packet.generation.worlds (entry.owner.worldEnvironment ownerControls initial).worlds)
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {ownerBase : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    (extension : OriginalFrameExtension ownerBase entry.frame.raw)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ entry.rank)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade entry.rank).atoms, atom ∈ entry.input.atoms) :
    ∃ entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue,
      (∀ need ∈ needs, need ∈ entries.needs) ∧
      (∀ selected ∈ entries, selected.owner = entry.owner) ∧
      (∀ selected ∈ entries, Nonempty (OriginalFrameExtension ownerBase selected.frame.raw)) ∧
      (∀ selected ∈ entries,
        ∃ output : WorldFamilyEntry (base := base) P common ownerRaw commonLeft commonRight caps
            controls ownerControls frontier selected,
          output.generation.worlds = packet.generation.worlds ∧
          Covered (@EquationControlMeasure.Less strata.rules.length) output.generation.worlds
            (selected.owner.worldEnvironment ownerControls initial).worlds ∧
          selected.answer.value.support.sortFlags = entry.answer.value.support.sortFlags) := by
  obtain ⟨entries, coverage, owners, extensions, packets⟩ :=
    packet.coverNeedsWorlds henv formed extension needs bounded covered
  refine ⟨entries, coverage, owners, extensions, ?_⟩
  intro selected member
  obtain ⟨output, worlds, supports⟩ := packets selected member
  refine ⟨output, worlds, ?_, supports⟩
  rw [worlds, owners selected member]
  exact ownerCovered

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
