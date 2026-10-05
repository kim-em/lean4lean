import Lean4Lean.Theory.Typing.AnchoredSortableVariableTrace
import Lean4Lean.Theory.Typing.AnchoredSortableCodeActionCertificate

/-! Compile finite variable traces to ordinary source observations. Code
actions compute their actual footprint; duplicated leaves remain available
in the same table. No typing interpretation or original-proof call is used. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable def VariableTrace.observation
    (trace : VariableTrace env U registry target index profile footprint)
    (locals : List Nat) (σ : Subst) :
    Obs env U registry target locals σ (.bvar index) profile footprint :=
  match trace with
  | .leaf profile => .var locals σ index profile
  | .empty => .empty
  | .union left right => .union (VariableTrace.observation left locals σ) (VariableTrace.observation right locals σ)
  | .view child change => .view (VariableTrace.observation child locals σ) change
  | .pad child => .pad (VariableTrace.observation child locals σ)
  | .unpad child => .unpad (VariableTrace.observation child locals σ)
  | .rowShift child => .rowShift (VariableTrace.observation child locals σ)

def SortableVariableTrace.compiledFootprint
    (trace : SortableVariableTrace env U registry target index profile footprint) : Footprint :=
  match trace with
  | .legacy _ => footprint
  | .union left right => left.compiledFootprint ++ right.compiledFootprint
  | .code child change _ => change.footprint child.compiledFootprint
  | .action child _ | .pad child | .unpad child => child.compiledFootprint

noncomputable def SortableVariableTrace.observation
    (trace : SortableVariableTrace env U registry target index profile footprint)
    (locals : List Nat) (σ : Subst) :
    SortableObs env U registry target locals σ (.bvar index) profile trace.compiledFootprint :=
  match trace with
  | .legacy child => .legacy (VariableTrace.observation child locals σ)
  | .union left right => .union (left.observation locals σ) (right.observation locals σ)
  | .code child change formed =>
    .code _ (change.applyCertificate (.observe (child.observation locals σ) formed))
  | .action child change => .action (child.observation locals σ) change
  | .pad child => .pad (child.observation locals σ)
  | .unpad child => .unpad (child.observation locals σ)

theorem SortableVariableTrace.compiledAvailable
    (trace : SortableVariableTrace env U registry target index profile footprint)
    (resources : footprint.Available available) :
    trace.compiledFootprint.Available available := by
  induction trace with
  | legacy => exact resources
  | union left right leftIH rightIH =>
    intro index need member
    rcases List.mem_append.mp member with member | member
    · exact leftIH (fun i need h => resources i need (List.mem_append_left _ h)) index need member
    · exact rightIH (fun i need h => resources i need (List.mem_append_right _ h)) index need member
  | code child action formed ih => exact action.available (ih resources)
  | action child action ih | pad child ih | unpad child ih => exact ih resources

end Lean4Lean.AnchoredSource.Adapted
