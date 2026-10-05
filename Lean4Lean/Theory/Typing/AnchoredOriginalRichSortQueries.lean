import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSortableSyntax
import Lean4Lean.Theory.Typing.AnchoredSortablePruning

/-! At a literal original universe, typed projection metadata cannot occur
inside the query. All rich wrappers admit an actual computational source
query with the same demand, without erasing any stored domain certificate. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

mutual
 theorem RichCert.sortQuery
    {node : EndpointState sourceEnv U source (.sort level) assigned}
    (query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (closed : available.AtomClosed) (resources : footprint.Available available) :
    ∃ required, Nonempty (SortableCert env U registry target locals σ (.sort level)
      relevant profile required) ∧ required.Available available := by
  match query with
  | .legacy certificate => exact ⟨_, ⟨certificate⟩, resources⟩
  | .observe observation formed =>
    obtain ⟨_, ⟨source⟩, resources⟩ := observation.sortQuery closed resources
    exact ⟨_, ⟨.observe source formed⟩, resources⟩
  | .route _ source => exact source.sortQuery closed resources
  | .union left right =>
    obtain ⟨_, ⟨left⟩, hl⟩ := left.sortQuery closed
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨_, ⟨right⟩, hr⟩ := right.sortQuery closed
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨_, ⟨.union left right⟩, fun i need hm =>
      (List.mem_append.mp hm).elim (hl i need) (hr i need)⟩
  | .pad source =>
    obtain ⟨_, ⟨source⟩, resources⟩ := source.sortQuery closed resources
    exact ⟨_, ⟨.pad source⟩, resources⟩
  | .down source =>
    obtain ⟨_, ⟨source⟩, resources⟩ := source.sortQuery closed resources
    exact ⟨_, ⟨.down source⟩, resources⟩
  | .map view source =>
    obtain ⟨_, ⟨source⟩, resources⟩ := source.sortQuery closed resources
    exact ⟨_, ⟨.map view source⟩, resources⟩
  | .support action source =>
    obtain ⟨_, ⟨source⟩, resources⟩ := source.sortQuery closed resources
    exact ⟨_, ⟨.support action source⟩, resources⟩
  | .select source member =>
    obtain ⟨_, ⟨source⟩, resources⟩ := source.sortQuery closed resources
    exact ⟨_, ⟨.select source member⟩, resources⟩
 termination_by sizeOf query
 decreasing_by all_goals simp_wf <;> omega

 theorem RichObs.sortQuery
    {node : EndpointState sourceEnv U source (.sort level) assigned}
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (closed : available.AtomClosed) (resources : footprint.Available available) :
    ∃ required, Nonempty (SortableObs env U registry target locals σ (.sort level)
      profile required) ∧ required.Available available := by
  match query with
  | .legacy observation => exact ⟨_, ⟨observation⟩, resources⟩
  | .code source =>
    obtain ⟨_, ⟨source⟩, resources⟩ := source.sortQuery closed resources
    exact ⟨_, ⟨.code _ source⟩, resources⟩
  | .route _ source => exact source.sortQuery closed resources
  | .union left right =>
    obtain ⟨_, ⟨left⟩, hl⟩ := left.sortQuery closed
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨_, ⟨right⟩, hr⟩ := right.sortQuery closed
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨_, ⟨.union left right⟩, fun i need hm =>
      (List.mem_append.mp hm).elim (hl i need) (hr i need)⟩
  | .view source view =>
    obtain ⟨_, ⟨source⟩, resources⟩ := source.sortQuery closed resources
    exact ⟨_, ⟨.view source view⟩, resources⟩
  | .action source action =>
    obtain ⟨_, ⟨source⟩, resources⟩ := source.sortQuery closed resources
    exact ⟨_, ⟨.action source action⟩, resources⟩
  | .select source member =>
    obtain ⟨_, ⟨source⟩, resources⟩ := source.sortQuery closed resources
    obtain ⟨selected⟩ := source.atom member
    exact ⟨_, ⟨selected.observation⟩, selected.atomizes.available_closed resources closed⟩
  | .pad source =>
    obtain ⟨_, ⟨source⟩, resources⟩ := source.sortQuery closed resources
    exact ⟨_, ⟨.pad source⟩, resources⟩
  | .unpad source =>
    obtain ⟨_, ⟨source⟩, resources⟩ := source.sortQuery closed resources
    exact ⟨_, ⟨.unpad source⟩, resources⟩
 termination_by sizeOf query
 decreasing_by all_goals simp_wf <;> omega
end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
