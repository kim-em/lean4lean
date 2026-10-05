import Lean4Lean.Theory.Typing.AnchoredOriginalSortableDepthFootprint

namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false
theorem SortableLocatedFootprint.arguments_allDepth
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (factor : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth 0 budget before after)
    (available : Valuation) (resources : before.Available available) (minimum : Nat) :
    ∃ result : SortableFactoredArguments env U registry Γ locals σ available argument after minimum,
      ∀ current, result.observation.nativeDepth current ≤ factor.nativeDepth current := by
  induction factor with
  | nil =>
    exact ⟨⟨minimum, Nat.le_refl _, .empty, [], .legacy .empty,
      (fun _ _ h => nomatch h), [], .nil, (fun _ _ h => nomatch h)⟩, by intro current; simp only [SortableObs.nativeDepth, Obs.nativeDepth, nativeDepth]; exact Nat.le_refl _⟩
  | keep index need rest ih =>
    obtain ⟨tail, tailDepth⟩ := ih (fun i need hm => resources i need (List.mem_cons_of_mem _ hm))
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
        · exact tail.outsideAvailable i original hm }, tailDepth⟩
  | @cut n before after demand argumentFootprint origin payload bounded rest ih =>
    rw [shiftFootprint_zero] at resources
    obtain ⟨tail, tailDepth⟩ := ih (fun i need hm => resources i need (List.mem_append_right _ hm))
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
      outsideAvailable := tail.outsideAvailable }, by
      intro current
      simp only [SortableObs.nativeDepth, SortableObs.nativeDepth_raise, nativeDepth]
      have := tailDepth current
      omega⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
