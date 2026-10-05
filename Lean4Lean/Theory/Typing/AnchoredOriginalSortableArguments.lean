import Lean4Lean.Theory.Typing.AnchoredSortableGrades
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableFactor
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceFactorArguments

/-! Finite mixed argument cuts are assembled at a common grade without
coercing native formation syntax to legacy observations. Every requested
local leaf is covered by the computed binder pack. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure SortableFactoredArguments (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (argument : VExpr) (required : Footprint) (minimum : Nat) where
  rank : Nat
  bound : minimum ≤ rank
  input : Profile rank
  argumentFootprint : Footprint
  observation : SortableObs env U registry Γ locals σ argument input argumentFootprint
  argumentAvailable : argumentFootprint.Available available
  outside : Footprint
  pack : BinderPack rank input required outside
  outsideAvailable : outside.Available available


namespace OriginalFactorCut
open OriginalClosureMeasure OriginalEndpointFactor

noncomputable def SortableCutPayload.observation
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {origin : CutOriginAt root boundary argument baseDepth}
    (payload : SortableCutPayload (env := env) origin registry Γ locals σ demand footprint) :
    SortableObs env U registry Γ locals σ argument demand footprint := by
  cases payload with
  | legacy observation _ => exact .legacy observation
  | observed observation _ => exact observation
  | sortable relevant certificate _ => exact .code relevant certificate

theorem SortableLocatedFootprint.arguments
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (factor : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth 0 budget before after)
    (available : Valuation) (resources : before.Available available) (minimum : Nat) :
    Nonempty (SortableFactoredArguments env U registry Γ locals σ available argument after minimum) := by
  induction factor with
  | nil =>
    exact ⟨⟨minimum, Nat.le_refl _, .empty, [], .legacy .empty,
      (fun _ _ h => nomatch h), [], .nil, (fun _ _ h => nomatch h)⟩⟩
  | keep index need rest ih =>
    obtain ⟨tail⟩ := ih (fun i need hm => resources i need (List.mem_cons_of_mem _ hm))
    exact ⟨{
      rank := tail.rank
      bound := tail.bound
      input := tail.input
      argumentFootprint := tail.argumentFootprint
      observation := tail.observation
      argumentAvailable := tail.argumentAvailable
      outside := (index, need) :: tail.outside
      pack := by simpa only [insertIndex, Nat.not_lt_zero, ite_false] using
        BinderPack.external index need tail.pack
      outsideAvailable := by
        intro i original hm
        rcases List.mem_cons.mp hm with he | hm
        · cases he; exact resources index need List.mem_cons_self
        · exact tail.outsideAvailable i original hm }⟩
  | @cut n before after demand argumentFootprint origin payload bounded rest ih =>
    rw [shiftFootprint_zero] at resources
    obtain ⟨tail⟩ := ih (fun i need hm => resources i need (List.mem_append_right _ hm))
    let N := max n tail.rank
    have hn : n ≤ N := Nat.le_max_left _ _
    have ht : tail.rank ≤ N := Nat.le_max_right _ _
    exact ⟨{
      rank := N
      bound := Nat.le_trans tail.bound ht
      input := (raiseProfile N hn demand).union (raiseProfile N ht tail.input)
      argumentFootprint := argumentFootprint ++ tail.argumentFootprint
      observation := .union (payload.observation.raise hn) (tail.observation.raise ht)
      argumentAvailable := by
        intro i need hm
        exact (List.mem_append.mp hm).elim
          (fun h => resources i need (List.mem_append_left _ h))
          (tail.argumentAvailable i need)
      outside := tail.outside
      pack := by
        simpa only [Need.atGrade, dif_pos hn] using
          BinderPack.local ⟨n, demand⟩ hn (tail.pack.raise ht)
      outsideAvailable := tail.outsideAvailable }⟩

end OriginalFactorCut
end Lean4Lean.AnchoredSource.Adapted
