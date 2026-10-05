import Lean4Lean.Theory.Typing.AnchoredAdapterNormalization
import Lean4Lean.Theory.Typing.AnchoredSourceSubstitution

/-! Canonicalize actual source observations by their existing guarded views.
Every retained leaf is an original leaf or its literal singleton selection. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem Footprint.Atomizes.trans {first middle last : Footprint}
    (left : first.Atomizes middle) (right : middle.Atomizes last) :
    first.Atomizes last := by
  intro index need member
  obtain ⟨mid, hm, hfirst⟩ := left index need member
  obtain ⟨old, ho, hsecond⟩ := right index mid hm
  refine ⟨old, ho, ?_⟩
  rcases hfirst with rfl | selected
  · exact hsecond
  · rcases hsecond with rfl | selectedMid
    · exact .inr selected
    · obtain ⟨atom, ha, rfl⟩ := List.mem_map.mp selectedMid
      have same : need = ⟨old.rank, .singleton atom⟩ := List.mem_singleton.mp selected
      subst need
      exact .inr (List.mem_map.mpr ⟨atom, ha, rfl⟩)

private theorem Obs.profileView_selected
    (observation : Obs env U registry Γ locals σ expression (whole : Profile n) footprint)
    (view : ProfileView env U registry Γ (source : Profile n) target)
    (included : List.Subset source whole) :
    ∃ selected, Nonempty (Obs env U registry Γ locals σ expression target selected) ∧
      selected.Atomizes footprint := by
  match view with
  | .nil => exact ⟨[], ⟨.empty⟩, fun _ _ h => nomatch h⟩
  | .cons head tail =>
    obtain ⟨first⟩ := observation.atom (included List.mem_cons_self)
    obtain ⟨tailFootprint, ⟨tailObservation⟩, selected⟩ :=
      observation.profileView_selected tail (fun _ hm => included (List.mem_cons_of_mem _ hm))
    exact ⟨first.footprint ++ tailFootprint,
      ⟨.union (.view first.observation head) tailObservation⟩, first.atomizes.append selected⟩
termination_by sizeOf view
decreasing_by simp_wf; omega

theorem Obs.normalize
    (henv : env.Ordered)
    (observation : Obs env U registry Γ locals σ expression (demand : Profile n) footprint) :
    ∃ selected, Nonempty (Obs env U registry Γ locals σ expression
      (AdapterNormal.profile demand) selected) ∧ selected.Atomizes footprint :=
  observation.profileView_selected (AdapterNormal.profileView henv demand) (fun _ h => h)

end Lean4Lean.AnchoredSource
