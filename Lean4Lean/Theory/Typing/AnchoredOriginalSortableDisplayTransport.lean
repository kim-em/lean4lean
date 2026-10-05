import Lean4Lean.Theory.Typing.AnchoredSortableRenaming
import Lean4Lean.Theory.Typing.AnchoredSortableReflection
import Lean4Lean.Theory.Typing.AnchoredOriginalDisplayTransport

/-! Exact source-syntax transport between two original source displays.
Only existing observations and certificates are renamed and reflected;
no weakened source derivation is reified. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Lift into the common display and reflect into the other source tail.
The exact demand stays fixed, and all new source leaves come from the same
common valuation. This transports current Obs syntax, not source typing. -/
theorem SortableObs.betweenDisplays
    {leftAvailable rightAvailable commonAvailable : Valuation}
    (observation : SortableObs env U registry target leftLocals σ left demand footprint)
    (leftMap rightMap : Lift) (common : Subst)
    (leftRealization : Subst.lift_l leftMap common = σ)
    (rightRealization : Subst.lift_l rightMap common = τ)
    (same : left.lift' leftMap = right.lift' rightMap)
    (commonLocals rightLocals : List Nat)
    (resources : footprint.Available leftAvailable)
    (leftAvailableEq : ∀ index, leftAvailable index = commonAvailable (leftMap.liftVar index))
    (rightAvailableEq : ∀ index, rightAvailable index = commonAvailable (rightMap.liftVar index)) :
    ∃ required, Nonempty (SortableObs env U registry target rightLocals τ right demand required) ∧
      required.Available rightAvailable := by
  have lifted := observation.renameSource leftMap common leftRealization commonLocals
  have liftedAvailable : (footprint.sourceLift leftMap).Available commonAvailable := by
    intro index need member
    obtain ⟨⟨originalIndex, originalNeed⟩, originalMember, equal⟩ := List.mem_map.mp member
    cases equal
    rw [← leftAvailableEq]
    exact resources originalIndex need originalMember
  obtain ⟨required, ⟨reflected⟩, footprintEq⟩ :=
    lifted.reflectSource rightMap same rightLocals
  rw [rightRealization] at reflected
  refine ⟨required, ⟨reflected⟩, ?_⟩
  intro index need member
  rw [rightAvailableEq]
  apply liftedAvailable (rightMap.liftVar index) need
  rw [footprintEq]
  exact List.mem_map.mpr ⟨(index, need), member, rfl⟩

/-- Lift into the common display and reflect into the other source tail.
The exact demand stays fixed, and all new source leaves come from the same
common valuation. This transports current Obs syntax, not source typing. -/
theorem SortableCert.betweenDisplays
    {leftAvailable rightAvailable commonAvailable : Valuation}
    (observation : SortableCert env U registry target leftLocals σ left relevant demand footprint)
    (leftMap rightMap : Lift) (common : Subst)
    (leftRealization : Subst.lift_l leftMap common = σ)
    (rightRealization : Subst.lift_l rightMap common = τ)
    (same : left.lift' leftMap = right.lift' rightMap)
    (commonLocals rightLocals : List Nat)
    (resources : footprint.Available leftAvailable)
    (leftAvailableEq : ∀ index, leftAvailable index = commonAvailable (leftMap.liftVar index))
    (rightAvailableEq : ∀ index, rightAvailable index = commonAvailable (rightMap.liftVar index)) :
    ∃ required, Nonempty (SortableCert env U registry target rightLocals τ right relevant demand required) ∧
      required.Available rightAvailable := by
  have lifted := observation.renameSource leftMap common leftRealization commonLocals
  have liftedAvailable : (footprint.sourceLift leftMap).Available commonAvailable := by
    intro index need member
    obtain ⟨⟨originalIndex, originalNeed⟩, originalMember, equal⟩ := List.mem_map.mp member
    cases equal
    rw [← leftAvailableEq]
    exact resources originalIndex need originalMember
  obtain ⟨required, ⟨reflected⟩, footprintEq⟩ :=
    lifted.reflectSource rightMap same rightLocals
  rw [rightRealization] at reflected
  refine ⟨required, ⟨reflected⟩, ?_⟩
  intro index need member
  rw [rightAvailableEq]
  apply liftedAvailable (rightMap.liftVar index) need
  rw [footprintEq]
  exact List.mem_map.mpr ⟨(index, need), member, rfl⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
