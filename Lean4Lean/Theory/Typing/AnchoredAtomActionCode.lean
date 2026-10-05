import Lean4Lean.Theory.Typing.AnchoredAtomAction

/-! On sortable atoms, a hereditary action is an explicit finite code
program. This permits composition without asking for an intermediate type
capability at a function boundary. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles AnchoredSource.Adapted
set_option backward.isDefEq.respectTransparency false

private theorem not_fn_sortable {key : Key n} {output : Atom n}
    (formed : (Profile.fn key output).HasType (.sort relevant)) : False := by
  obtain ⟨cover, member, impossible⟩ := formed.2.2 _ (List.mem_singleton_self _)
  cases List.mem_singleton.mp member
  contradiction

theorem AtomView.sortable_source_rigid
    {a b : Atom n} (view : AtomView env U registry Γ a b)
    (formed : (Profile.singleton a).HasType (.sort relevant)) : a = b := by
  match n, a, b, view with
  | _, _, _, .refl _ => rfl
  | _ + 1, _, _, .reanchor _ => exact (not_fn_sortable formed).elim
  | _ + 1, _, _, .domainRekey .. => exact (not_fn_sortable formed).elim
  | _ + 1, _, _, .input .. => exact (not_fn_sortable formed).elim
  | _ + 2, _, _, .commutePadFn _ _ =>
    change (Profile.fn _ _).pad.HasType _ at formed
    have low := formed.pad_inv
    rw [Profile.down_sort] at low
    exact (not_fn_sortable low).elim
  | _ + 2, _, _, .uncommutePadFn _ _ => exact (not_fn_sortable formed).elim
  | _ + 1, _, _, .fn _ _ => exact (not_fn_sortable formed).elim
  | _ + 1, _, _, .pad child =>
    change (Profile.singleton _).pad.HasType _ at formed
    have low := formed.pad_inv
    rw [Profile.down_sort] at low
    exact congrArg AtomData.pad (child.sortable_source_rigid low)
  | _, _, _, .trans first second =>
    have equal := first.sortable_source_rigid formed
    exact equal.trans (second.sortable_source_rigid (equal ▸ formed))
termination_by sizeOf view

theorem AtomAction.sortable
    {a b : Atom n} (action : AtomAction env U registry Γ a b)
    (formed : (Profile.singleton a).HasType (.sort relevant)) :
    (Profile.singleton b).HasType (.sort relevant) := by
  induction action with
  | view v => exact v.sortable_source_rigid formed ▸ formed
  | code leaf _ => exact leaf.preservesSort formed
  | fn => exact (not_fn_sortable formed).elim
  | pad child ih =>
    change (Profile.singleton _).pad.HasType _ at formed ⊢
    exact (ih (by simpa only [Profile.down_sort] using formed.pad_inv)).pad_sort
  | comp first second firstIH secondIH => exact secondIH (firstIH formed)

noncomputable def AtomAction.toCode
    {a b : Atom n} (action : AtomAction env U registry Γ a b)
    (formed : (Profile.singleton a).HasType (.sort relevant)) :
    SortableCodeAction env U registry Γ relevant (.singleton a) relevant (.singleton b) := by
  match n, a, b, action with
  | _, _, _, .view v => exact v.sortable_source_rigid formed ▸ .id
  | _, _, _, .code leaf required =>
    exact .comp (.retag required) (.comp leaf (.retag (leaf.preservesSort formed)))
  | _ + 1, _, _, .fn _ _ => exact (not_fn_sortable formed).elim
  | _ + 1, _, _, .pad child =>
    change (Profile.singleton _).pad.HasType _ at formed
    have low := formed.pad_inv
    rw [Profile.down_sort] at low
    simpa only [Profile.pad_singleton] using
      SortableCodeAction.comp .unpad (.comp (child.toCode low) .pad)
  | _, _, _, .comp first second =>
    exact .comp (first.toCode formed) (second.toCode (first.sortable formed))
termination_by sizeOf action

/-- A code output always has a genuinely sortable input. The input flag
can differ after focusing, so it is recovered rather than guessed. -/
theorem AtomAction.sortableOrigin
    (henv : env.Ordered) {a b : Atom n} (action : AtomAction env U registry Γ a b)
    (formed : (Profile.singleton b).HasType (.sort relevant)) :
    ∃ sourceFlag, (Profile.singleton a).HasType (.sort sourceFlag) := by
  induction action generalizing relevant with
  | view v =>
    have equal := (v.inverse henv).sortable_source_rigid formed
    exact ⟨relevant, equal ▸ formed⟩
  | code _ original => exact ⟨_, original⟩
  | fn => exact (not_fn_sortable formed).elim
  | pad child ih =>
    change (Profile.singleton _).pad.HasType _ at formed
    have low := formed.pad_inv
    rw [Profile.down_sort] at low
    obtain ⟨flag, sorted⟩ := ih low
    exact ⟨flag, sorted.pad_sort⟩
  | comp first second firstIH secondIH =>
    obtain ⟨flag, sorted⟩ := secondIH formed
    exact firstIH sorted

theorem AtomAction.toCodeAtOutput
    (henv : env.Ordered) {a b : Atom n} (action : AtomAction env U registry Γ a b)
    (formed : (Profile.singleton b).HasType (.sort relevant)) :
    ∃ sourceFlag, (Profile.singleton a).HasType (.sort sourceFlag) ∧
      Nonempty (SortableCodeAction env U registry Γ sourceFlag (.singleton a)
        relevant (.singleton b)) := by
  obtain ⟨flag, sourceFormed⟩ := action.sortableOrigin henv formed
  exact ⟨flag, sourceFormed, ⟨.comp (action.toCode sourceFormed) (.retag formed)⟩⟩

end Lean4Lean.AnchoredSemantics
