import Lean4Lean.Theory.Typing.AnchoredGeneralAdapters

/-! Composition is a finite program transformation. In particular no
intermediate function-type capability is an input to adapter interpretation. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles AnchoredSource.Adapted
set_option backward.isDefEq.respectTransparency false

private theorem not_fn_sortable {key : Key n} {output : Atom n}
    (formed : (Profile.fn key output).HasType (.sort relevant)) : False := by
  obtain ⟨cover, member, impossible⟩ := formed.2.2 _ (List.mem_singleton_self _)
  cases List.mem_singleton.mp member
  contradiction

theorem GeneralAtomAdapter.sortable
    {a b : Atom n} (adapter : GeneralAtomAdapter env U registry Γ a b)
    (formed : (Profile.singleton a).HasType (.sort relevant)) :
    (Profile.singleton b).HasType (.sort relevant) := by
  match n, a, b, adapter with
  | _, _, _, .refl _ => exact formed
  | _, _, _, .code action _ => exact action.preservesSort formed
  | _ + 1, _, _, .fn .. => exact (not_fn_sortable formed).elim
  | _ + 1, _, _, .pad child =>
    change (Profile.singleton _).pad.HasType _ at formed ⊢
    have low := formed.pad_inv
    rw [Profile.down_sort] at low
    exact (child.sortable low).pad_sort
termination_by n

noncomputable def GeneralAtomAdapter.toCode
    {a b : Atom n} (adapter : GeneralAtomAdapter env U registry Γ a b)
    (formed : (Profile.singleton a).HasType (.sort relevant)) :
    SortableCodeAction env U registry Γ relevant (.singleton a) relevant (.singleton b) := by
  match n, a, b, adapter with
  | _, _, _, .refl _ => exact .id
  | _, _, _, .code action required =>
    exact .comp (.retag required) (.comp action (.retag (action.preservesSort formed)))
  | _ + 1, _, _, .fn .. => exact (not_fn_sortable formed).elim
  | _ + 1, _, _, .pad child =>
    change (Profile.singleton _).pad.HasType _ at formed
    have low := formed.pad_inv
    rw [Profile.down_sort] at low
    simpa only [Profile.pad_singleton] using
      SortableCodeAction.comp .unpad (.comp (child.toCode low) .pad)
termination_by n

theorem GeneralAtomAdapter.sortableOrigin
    {a b : Atom n} (adapter : GeneralAtomAdapter env U registry Γ a b)
    (formed : (Profile.singleton b).HasType (.sort relevant)) :
    ∃ sourceFlag, (Profile.singleton a).HasType (.sort sourceFlag) := by
  match n, a, b, adapter with
  | _, _, _, .refl _ => exact ⟨_, formed⟩
  | _, _, _, .code _ required => exact ⟨_, required⟩
  | _ + 1, _, _, .fn .. => exact (not_fn_sortable formed).elim
  | _ + 1, _, _, .pad child =>
    change (Profile.singleton _).pad.HasType _ at formed
    have low := formed.pad_inv
    rw [Profile.down_sort] at low
    obtain ⟨flag, sorted⟩ := child.sortableOrigin low
    exact ⟨flag, sorted.pad_sort⟩
termination_by n

theorem GeneralAtomAdapter.toCodeAtOutput
    {a b : Atom n} (adapter : GeneralAtomAdapter env U registry Γ a b)
    (formed : (Profile.singleton b).HasType (.sort relevant)) :
    ∃ sourceFlag, (Profile.singleton a).HasType (.sort sourceFlag) ∧
      Nonempty (SortableCodeAction env U registry Γ sourceFlag (.singleton a)
        relevant (.singleton b)) := by
  obtain ⟨flag, sourceFormed⟩ := adapter.sortableOrigin formed
  exact ⟨flag, sourceFormed, ⟨.comp (adapter.toCode sourceFormed) (.retag formed)⟩⟩

noncomputable def GeneralAtomAdapter.comp {a b c : Atom n}
    (first : GeneralAtomAdapter env U registry Γ a b)
    (second : GeneralAtomAdapter env U registry Γ b c) :
    GeneralAtomAdapter env U registry Γ a c := by
  match n, a, b, first with
  | _, _, _, .refl _ => exact second
  | _, _, _, .code action formed =>
    have middle := action.preservesSort formed
    exact .code (.comp (.comp action (.retag middle)) (second.toCode middle)) formed
  | _ + 1, _, _, .fn keys result =>
    match c, second with
    | _, .refl _ => exact .fn keys result
    | _, .code _ formed => exact (not_fn_sortable formed).elim
    | _, .fn nextKeys nextResult => exact .fn (.comp keys nextKeys) (result.comp nextResult)
  | _ + 1, _, _, .pad child =>
    match c, second with
    | _, .refl _ => exact .pad child
    | _, .pad next => exact .pad (child.comp next)
    | _, .code action formed =>
      have origin := (GeneralAtomAdapter.pad child).toCodeAtOutput formed
      let flag := Classical.choose origin
      have sourceFormed := (Classical.choose_spec origin).1
      let program := Classical.choice (Classical.choose_spec origin).2
      exact .code (.comp program action) sourceFormed
termination_by n

noncomputable def GeneralProfileAdapter.comp {source middle target : Profile n}
    (first : GeneralProfileAdapter env U registry Γ source middle)
    (second : GeneralProfileAdapter env U registry Γ middle target) :
    GeneralProfileAdapter env U registry Γ source target := by
  match second with
  | .nil _ => exact .nil _
  | .cons member head tail =>
    let origin := first.origin member
    let original := Classical.choose origin
    have originalMember := (Classical.choose_spec origin).1
    let entry := Classical.choice (Classical.choose_spec origin).2
    exact .cons originalMember (entry.comp head) (first.comp tail)
termination_by sizeOf second

end Lean4Lean.AnchoredSemantics
