import Lean4Lean.Theory.Typing.AnchoredFunctionGradeView
import Lean4Lean.Theory.Typing.AnchoredSourceFootprint

/-! The binder pack of an eta body splits into the reflected function's
external leaves and exactly the observed argument variable's local leaves. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem VariableTrace.indices
    (trace : VariableTrace env U registry Γ i demand footprint)
    (hm : (j, need) ∈ footprint) : j = i := by
  induction trace with
  | leaf demand => cases List.mem_singleton.mp hm; rfl
  | empty => cases hm
  | union left right ihleft ihright =>
    rcases List.mem_append.mp hm with h | h
    · exact ihleft h
    · exact ihright h
  | view source change ih => exact ih hm
  | pad source ih => exact ih hm
  | unpad source ih => exact ih hm
  | rowShift source ih => exact ih hm

private theorem BinderPack.local_only {input : Profile n} {required outside : Footprint}
    (pack : BinderPack n input required outside)
    (localOnly : ∀ j need, (j, need) ∈ required → j = 0) :
    input = required.atGrade n ∧
      (∀ j need, (j, need) ∈ required → need.rank ≤ n) ∧ outside = [] := by
  induction required generalizing input outside with
  | nil =>
    cases pack
    refine ⟨rfl, ?_, rfl⟩
    intro j need h
    cases h
  | cons entry rest ih =>
    rcases entry with ⟨j, need⟩
    have hj := localOnly j need (List.mem_cons_self ..)
    subst j
    cases pack with
    | «local» _ bound tail =>
      obtain ⟨hinput, hbounds, houtside⟩ := ih tail
        (fun j need hm => localOnly j need (List.mem_cons_of_mem _ hm))
      refine ⟨?_, ?_, houtside⟩
      · change (need.atGrade n).union _ = (need.atGrade n).union (Footprint.atGrade n rest)
        rw [hinput]
      · intro j need' hm
        rcases List.mem_cons.mp hm with he | hm
        · cases he; exact bound
        · exact hbounds j need' hm

private theorem BinderPack.external_prefix {input : Profile n} {function argument outside : Footprint}
    (pack : BinderPack n input (function.sourceLift (.skip .refl) ++ argument) outside)
    (localOnly : ∀ j need, (j, need) ∈ argument → j = 0) :
    input = argument.atGrade n ∧
      (∀ j need, (j, need) ∈ argument → need.rank ≤ n) ∧ outside = function := by
  induction function generalizing outside with
  | nil => exact pack.local_only localOnly
  | cons entry rest ih =>
    rcases entry with ⟨i, need⟩
    change BinderPack n input
      ((i + 1, need) :: (Footprint.sourceLift (.skip .refl) rest ++ argument)) outside at pack
    cases pack with
    | external _ _ tail =>
      obtain ⟨hinput, hbounds, houtside⟩ := ih tail
      exact ⟨hinput, hbounds, congrArg (List.cons (i, need)) houtside⟩

/-- No argument leaf may be hidden or assigned a different grade by an eta
body's binder pack. The function's external footprint is preserved literally. -/
theorem BinderPack.etaFootprint {input : Profile n}
    (argument : VariableTrace env U registry Γ 0 demand argumentFootprint)
    (pack : BinderPack n input
      (functionFootprint.sourceLift (.skip .refl) ++ argumentFootprint) outside) :
    input = argumentFootprint.atGrade n ∧
      (∀ j need, (j, need) ∈ argumentFootprint → need.rank ≤ n) ∧
      outside = functionFootprint :=
  pack.external_prefix (fun _ _ hm => argument.indices hm)

end Lean4Lean.AnchoredSource
