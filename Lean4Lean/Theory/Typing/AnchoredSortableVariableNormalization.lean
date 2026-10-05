import Lean4Lean.Theory.Typing.AnchoredSortableVariableTrace
import Lean4Lean.Theory.Typing.AnchoredAtomActionGeneralAdapter
import Lean4Lean.Theory.Typing.AnchoredSortableCodeActionGrades

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

noncomputable def SortableCodeAction.toGeneralAdapter
    (action : SortableCodeAction env U registry Γ relevant (p : Profile n) next (q : Profile n))
    (formed : p.HasType (.sort relevant)) :
    GeneralNormalProfileAdapter env U registry Γ p q := by
  let rec build (target : Profile n) (included : ∀ a ∈ target.atoms, a ∈ q.atoms) :
      GeneralProfileAdapter env U registry Γ (AdapterNormal.profile p)
        (AdapterNormal.profile target) := by
    match target with
    | [] => exact .nil _
    | b :: rest =>
      let origin := action.atom (included b List.mem_cons_self)
      let a := Classical.choose origin
      have member := (Classical.choose_spec origin).1
      let leaf := Classical.choice (Classical.choose_spec origin).2
      have af := formed.singleton_of_mem member
      have bf := leaf.preservesSort af
      have entry : GeneralAtomAdapter env U registry Γ (AdapterNormal.atom a) (AdapterNormal.atom b) := by
        rw [AdapterNormal.atom_sortable af, AdapterNormal.atom_sortable bf]
        exact .code leaf af
      exact .cons (List.mem_map.mpr ⟨a, member, rfl⟩) entry
        (build rest (fun a h => included a (List.mem_cons_of_mem _ h)))
  exact build q (fun _ h => h)

private noncomputable def singletonAdapter
    (adapter : GeneralNormalAtomAdapter env U registry Γ a b) :
    GeneralNormalProfileAdapter env U registry Γ (.singleton a) (.singleton b) :=
  .cons (List.mem_singleton_self _) adapter (.nil _)

noncomputable def SortableVariableTrace.normalize
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (trace : SortableVariableTrace env U registry Γ i (demand : Profile n) footprint)
    (N : Nat) (hN : trace.height ≤ N) :
    GeneralNormalProfileAdapter env U registry Γ (footprint.atGrade N)
      (raiseProfile N (Nat.le_trans trace.output_bound hN) demand) := by
  induction trace with
  | legacy source => exact (source.normalize N hN).toGeneralAdapter henv hscoped hΓ
  | union left right hl hr =>
    have l := Nat.le_trans (Nat.le_max_left _ _) hN
    have r := Nat.le_trans (Nat.le_max_right _ _) hN
    simpa only [Footprint.atGrade_append, raiseProfile_union] using
      GeneralNormalProfileAdapter.union (hl l) (hr r)
  | @code n p fp relevant next m q source action formed ih =>
    have hs : source.height ≤ N := Nat.le_trans (Nat.le_max_right _ _) hN
    have hout : m ≤ N := Nat.le_trans (Nat.le_max_left _ _) hN
    have hin : n ≤ N := Nat.le_trans source.output_bound hs
    have raisedFormed := (SortableCodeAction.raiseTo (env := env) (U := U)
      (registry := registry) (target := Γ) (relevant := relevant) hin).preservesSort formed
    exact (ih hs).comp ((action.atGrade hin hout).toGeneralAdapter raisedFormed)
  | action source action ih =>
    have bound := Nat.le_trans source.output_bound hN
    exact (ih hN).comp (GeneralNormalProfileAdapter.raise henv hscoped hΓ bound
      (singletonAdapter (action.toGeneralAdapter henv hscoped hΓ)))
  | pad source ih =>
    have hs := Nat.le_trans (Nat.le_max_right _ _) hN
    have hout := Nat.le_trans (Nat.le_max_left _ _) hN
    simpa only [raiseProfile_pad hout] using ih hs
  | unpad source ih => simpa only [raiseProfile_pad] using ih hN

end Lean4Lean.AnchoredSource.Adapted
