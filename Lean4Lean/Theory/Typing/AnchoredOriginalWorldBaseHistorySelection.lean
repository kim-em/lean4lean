import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBaseHistory

/-! Positional selection retains actual finite ancestry. In particular merge
branches and dormant owners are selected without deduplicating equal sites. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

theorem sublist_flatMap_member {values : List α} (f : α → List β) (member : a ∈ values) :
    (f a).Sublist (values.flatMap f) := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact List.sublist_append_left _ _
    · exact (ih member).trans (List.sublist_append_right _ _)

theorem WorldBaseHistories.restrictReady
    (histories : WorldBaseHistories strata U registry target P sites)
    (ready : histories.Ready frontier cutoff fuel)
    (selected : next.Sublist sites) :
    ∃ result : WorldBaseHistories strata U registry target P next,
      result.Ready frontier cutoff fuel := by
  induction selected with
  | slnil => exact ⟨.nil, trivial⟩
  | cons site selected ih =>
    cases histories with
    | cons head tail => exact ih tail ready.2
  | cons_cons site selected ih =>
    cases histories with
    | cons head tail =>
      obtain ⟨result, resultReady⟩ := ih tail ready.2
      exact ⟨.cons head result, ready.1, resultReady⟩

theorem WorldGenerated.Hereditary.selectGeneration
    {base : OriginalCaptureBase env U registry target}
    {nextBase : OriginalCaptureBase env U registry target}
    {generation : WorldGenerated strata P base caps left right graph frame controls}
    (hereditary : generation.Hereditary frontier)
    (next : WorldGenerated strata P nextBase nextCaps nextLeft nextRight nextGraph nextFrame nextControls)
    (closed : next.TablesClosed)
    (selected : next.baseUses.Sublist generation.baseUses)
    (sameCutoff : nextControls.cutoff = controls.cutoff)
    (sameFuel : nextControls.fuel = controls.fuel) :
    Nonempty (next.Hereditary frontier) := by
  obtain ⟨bases, ready⟩ := hereditary.bases.restrictReady hereditary.ready selected
  exact ⟨⟨closed, bases, by simpa only [sameCutoff, sameFuel] using ready⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
