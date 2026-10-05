import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceRenaming
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceReflection

/-! Exact source-syntax transport between two original source displays.
Only existing observations and certificates are renamed and reflected;
no weakened source derivation is reified. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- The same displayed source expression has the same target realization,
even when its original contexts and source substitutions differ. -/
theorem realized_between_displays
    {left right : VExpr} {leftMap rightMap : Lift} {common σ τ : Subst}
    (same : left.lift' leftMap = right.lift' rightMap)
    (leftRealization : Subst.lift_l leftMap common = σ)
    (rightRealization : Subst.lift_l rightMap common = τ) :
    left.subst σ = right.subst τ := by
  have equal := congrArg (fun expression => expression.subst common) same
  simpa only [subst_lift', leftRealization, rightRealization] using equal

/-- Lift into the common display and reflect into the other source tail.
The exact demand stays fixed, and all new source leaves come from the same
common valuation. This transports current Obs syntax, not source typing. -/
theorem Obs.betweenDisplays
    {leftAvailable rightAvailable commonAvailable : Valuation}
    (observation : Obs env U registry target leftLocals σ left demand footprint)
    (leftMap rightMap : Lift) (common : Subst)
    (leftRealization : Subst.lift_l leftMap common = σ)
    (rightRealization : Subst.lift_l rightMap common = τ)
    (same : left.lift' leftMap = right.lift' rightMap)
    (commonLocals rightLocals : List Nat)
    (resources : footprint.Available leftAvailable)
    (leftAvailableEq : ∀ index, leftAvailable index = commonAvailable (leftMap.liftVar index))
    (rightAvailableEq : ∀ index, rightAvailable index = commonAvailable (rightMap.liftVar index)) :
    ∃ required, Nonempty (Obs env U registry target rightLocals τ right demand required) ∧
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
theorem CodeCert.betweenDisplays
    {leftAvailable rightAvailable commonAvailable : Valuation}
    (observation : CodeCert env U registry target leftLocals σ left demand footprint)
    (leftMap rightMap : Lift) (common : Subst)
    (leftRealization : Subst.lift_l leftMap common = σ)
    (rightRealization : Subst.lift_l rightMap common = τ)
    (same : left.lift' leftMap = right.lift' rightMap)
    (commonLocals rightLocals : List Nat)
    (resources : footprint.Available leftAvailable)
    (leftAvailableEq : ∀ index, leftAvailable index = commonAvailable (leftMap.liftVar index))
    (rightAvailableEq : ∀ index, rightAvailable index = commonAvailable (rightMap.liftVar index)) :
    ∃ required, Nonempty (CodeCert env U registry target rightLocals τ right demand required) ∧
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
