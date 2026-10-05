import Lean4Lean.Theory.Typing.AnchoredOriginalRichGroupedCapture

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem environmentCost_le_of_members {environment : List Closure}
    (bound : ∀ closure ∈ environment, closure.cost ≤ maximum) : environmentCost environment ≤ maximum := by
  induction environment with
  | nil => exact Nat.zero_le _
  | cons head tail ih =>
    exact Nat.max_le.mpr ⟨bound head List.mem_cons_self,
      ih (fun closure member => bound closure (List.mem_cons_of_mem _ member))⟩

/-- Query selection cannot spend more than the two roots already present in
an empty slot. The prior frame may be replaced by any actual recursive answer
whose computed environment has not grown; all owner occurrences remain exact. -/
theorem RichGroupedCapture.environment_mono
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    (nextEntries : RichGroupedCapture (field := field) (major := major) domain env registry target
      nextLocals nextσ nextAvailable initial nextRawCapture nextLeftValue nextRightValue)
    (previous nextPrevious : List Closure)
    (tailBound : environmentCost nextPrevious ≤ environmentCost previous) :
    environmentCost (nextEntries.environment ordered headerOrdered initial nextPrevious) ≤
      environmentCost (entries.environment ordered headerOrdered initial previous) := by
  let declared := Closure.close (domain.dependencyOrigin headerOrdered) previous
  let nextDeclared := Closure.close (domain.dependencyOrigin headerOrdered) nextPrevious
  have declaredBound : nextDeclared.cost ≤ declared.cost :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left tailBound 1)
  have fieldMember : Closure.bundle (.close (field.dependencyOrigin ordered) initial) declared ∈
      entries.environment ordered headerOrdered initial previous :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have majorMember : Closure.bundle (.close (major.dependencyOrigin ordered) initial) declared ∈
      entries.environment ordered headerOrdered initial previous :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have previousBound : environmentCost previous ≤
      environmentCost (entries.environment ordered headerOrdered initial previous) := by
    apply environmentCost_le_of_members
    intro closure member
    exact environment_entry (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_right _ member))))
  apply environmentCost_le_of_members
  intro closure member
  rcases List.mem_cons.mp member with rfl | member
  · exact Nat.le_trans declaredBound (environment_entry List.mem_cons_self)
  rcases List.mem_cons.mp member with rfl | member
  · exact Nat.le_trans (Nat.add_le_add_left declaredBound _) (environment_entry fieldMember)
  rcases List.mem_cons.mp member with rfl | member
  · exact Nat.le_trans (Nat.add_le_add_left declaredBound _) (environment_entry majorMember)
  rcases List.mem_append.mp member with member | member
  · obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
    cases ownerEq : entry.owner with
    | inl occurrence =>
      have ownerBound := occurrence.location.dependency_cost_le ordered initial
      exact Nat.le_trans (Nat.add_le_add ownerBound declaredBound) (environment_entry fieldMember)
    | inr occurrence =>
      have ownerBound := occurrence.location.dependency_cost_le ordered initial
      exact Nat.le_trans (Nat.add_le_add ownerBound declaredBound) (environment_entry majorMember)
  · exact Nat.le_trans (environment_entry member) (Nat.le_trans tailBound previousBound)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
