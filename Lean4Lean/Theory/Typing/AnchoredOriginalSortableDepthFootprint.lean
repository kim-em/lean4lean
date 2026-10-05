import Lean4Lean.Theory.Typing.AnchoredOriginalSortableArguments
import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepthGrades

/-! Declaration depths of the actual retained cuts. Original locations and
pre-reflection queries remain in the same ledger. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false
open private BinderPack.strip_external from Lean4Lean.Theory.Typing.AnchoredOriginalFactorTraversal

def BoundedLocatedFootprintAt.nativeDepth
    (trace : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after)
    (current : Name → Bool) : Nat :=
  match trace with
  | .nil => 0
  | .keep _ _ tail => tail.nativeDepth current
  | .cut origin observation whole bounded tail => max (observation.nativeDepth current) (tail.nativeDepth current)

@[simp] theorem BoundedLocatedFootprintAt.nativeDepth_rec {α : Sort v} {a b : α}
    (current : Name → Bool) (equal : a = b) (before after : α → Footprint)
    (trace : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget (before a) (after a)) :
    (equal ▸ trace : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget (before b) (after b)).nativeDepth current = trace.nativeDepth current := by
  cases equal; rfl

@[simp] theorem BoundedLocatedFootprintAt.nativeDepth_mpr
    (current : Name → Bool) (hb : before = before') (ha : after = after')
    (equal : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before' after' =
      BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after)
    (trace : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after) :
    (equal.mpr trace).nativeDepth current = trace.nativeDepth current := by
  cases hb; cases ha; cases equal; rfl

@[simp] theorem BoundedLocatedFootprintAt.nativeDepth_weaken
    (trace : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after)
    {larger : List Closure → Nat}
    (bound : ∀ initial, budget initial ≤ larger initial) (current : Name → Bool) :
    (trace.weaken bound).nativeDepth current = trace.nativeDepth current := by
  induction trace with
  | nil => rfl
  | keep _ _ _ ih => exact ih
  | cut origin observation whole bounded tail ih =>
    simp only [weaken] at ih
    simpa only [weaken, nativeDepth] using congrArg (max _) ih

@[simp] theorem BoundedLocatedFootprintAt.nativeDepth_append
    (first : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before₁ after₁)
    (second : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before₂ after₂)
    (current : Name → Bool) :
    (first.append second).nativeDepth current = max (first.nativeDepth current) (second.nativeDepth current) := by
  induction first with
  | nil => simp only [append, nativeDepth, Nat.zero_max]
  | keep _ _ _ ih => exact ih
  | cut origin observation whole bounded tail ih =>
    simp only [append] at ih
    simp only [append, nativeDepth_mpr current (List.append_assoc _ _ _).symm List.cons_append, nativeDepth, ih, Nat.max_assoc]

theorem BoundedLocatedFootprintAt.underBinder_allDepth
    (factor : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth (depth + 1) budget before after)
    (pack : BinderPack n input before outside) :
    ∃ newOutside, BinderPack n input after newOutside ∧
      ∃ result : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget outside newOutside,
      ∀ current, result.nativeDepth current = factor.nativeDepth current := by
  induction factor generalizing input outside with
  | nil => cases pack; exact ⟨[], .nil, .nil, fun _ => rfl⟩
  | keep index need tail ih =>
    cases index with
    | zero =>
      cases pack with
      | «local» _ bound rest =>
        obtain ⟨newOutside, normal, result, resultDepth⟩ := ih rest
        exact ⟨newOutside, by simpa only [insertIndex_zero] using BinderPack.local need bound normal,
          result, resultDepth⟩
    | succ index =>
      cases pack with
      | external _ _ rest =>
        obtain ⟨newOutside, normal, result, resultDepth⟩ := ih rest
        exact ⟨(insertIndex depth index, need) :: newOutside,
          by simpa only [insertIndex_succ] using BinderPack.external _ need normal,
          BoundedLocatedFootprintAt.keep index need result, resultDepth⟩
  | cut origin observation whole bounded tail ih =>
    rw [shiftFootprint_succ] at pack
    obtain ⟨rest, normal, he⟩ := BinderPack.strip_external pack
    obtain ⟨newOutside, normal', result, resultDepth⟩ := ih normal
    subst outside
    exact ⟨(depth, _) :: newOutside, .external depth _ normal',
      BoundedLocatedFootprintAt.cut origin observation whole bounded result, by intro current; simp only [nativeDepth, resultDepth]⟩


noncomputable def SortableLocatedFootprint.nativeDepth
    (trace : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after)
    (current : Name → Bool) : Nat :=
  match trace with
  | .nil => 0
  | .keep _ _ tail => tail.nativeDepth current
  | .cut origin payload bounded tail => max (payload.observation.nativeDepth current) (tail.nativeDepth current)

@[simp] theorem SortableLocatedFootprint.nativeDepth_rec {α : Sort v} {a b : α}
    (current : Name → Bool) (equal : a = b) (before after : α → Footprint)
    (trace : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget (before a) (after a)) :
    (equal ▸ trace : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget (before b) (after b)).nativeDepth current = trace.nativeDepth current := by
  cases equal; rfl

@[simp] theorem SortableLocatedFootprint.nativeDepth_mpr
    (current : Name → Bool) (hb : before = before') (ha : after = after')
    (equal : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before' after' =
      SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after)
    (trace : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after) :
    (equal.mpr trace).nativeDepth current = trace.nativeDepth current := by
  cases hb; cases ha; cases equal; rfl

@[simp] theorem SortableLocatedFootprint.nativeDepth_weaken
    (trace : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after)
    {larger : List Closure → Nat}
    (bound : ∀ initial, budget initial ≤ larger initial) (current : Name → Bool) :
    (trace.weaken bound).nativeDepth current = trace.nativeDepth current := by
  induction trace with
  | nil => rfl
  | keep _ _ _ ih => exact ih
  | cut origin payload bounded tail ih =>
    simp only [weaken] at ih
    simpa only [weaken, nativeDepth] using congrArg (max _) ih

@[simp] theorem SortableLocatedFootprint.nativeDepth_append
    (first : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before₁ after₁)
    (second : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before₂ after₂)
    (current : Name → Bool) :
    (first.append second).nativeDepth current = max (first.nativeDepth current) (second.nativeDepth current) := by
  induction first with
  | nil => simp only [append, nativeDepth, Nat.zero_max]
  | keep _ _ _ ih => exact ih
  | cut origin payload bounded tail ih =>
    simp only [append] at ih
    simp only [append, nativeDepth_mpr current (List.append_assoc _ _ _).symm List.cons_append, nativeDepth, ih, Nat.max_assoc]

theorem SortableLocatedFootprint.underBinder_allDepth
    (factor : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth (depth + 1) budget before after)
    (pack : BinderPack n input before outside) :
    ∃ newOutside, BinderPack n input after newOutside ∧
      ∃ result : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget outside newOutside,
      ∀ current, result.nativeDepth current = factor.nativeDepth current := by
  induction factor generalizing input outside with
  | nil => cases pack; exact ⟨[], .nil, .nil, fun _ => rfl⟩
  | keep index need tail ih =>
    cases index with
    | zero =>
      cases pack with
      | «local» _ bound rest =>
        obtain ⟨newOutside, normal, result, resultDepth⟩ := ih rest
        exact ⟨newOutside, by simpa only [insertIndex_zero] using BinderPack.local need bound normal,
          result, resultDepth⟩
    | succ index =>
      cases pack with
      | external _ _ rest =>
        obtain ⟨newOutside, normal, result, resultDepth⟩ := ih rest
        exact ⟨(insertIndex depth index, need) :: newOutside,
          by simpa only [insertIndex_succ] using BinderPack.external _ need normal,
          SortableLocatedFootprint.keep index need result, resultDepth⟩
  | cut origin payload bounded tail ih =>
    rw [shiftFootprint_succ] at pack
    obtain ⟨rest, normal, he⟩ := BinderPack.strip_external pack
    obtain ⟨newOutside, normal', result, resultDepth⟩ := ih normal
    subst outside
    exact ⟨(depth, _) :: newOutside, .external depth _ normal',
      SortableLocatedFootprint.cut origin payload bounded result, by intro current; simp only [nativeDepth, resultDepth]⟩

@[simp] theorem SortableLocatedFootprint.nativeDepth_ofLegacy
    (trace : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after)
    (current : Name → Bool) : (SortableLocatedFootprint.ofLegacy trace).nativeDepth current = trace.nativeDepth current := by
  induction trace with
  | nil => rfl
  | keep _ _ _ ih => exact ih
  | cut origin observation whole bounded tail ih =>
    simp only [ofLegacy] at ih
    simp only [ofLegacy, nativeDepth, BoundedLocatedFootprintAt.nativeDepth,
      SortableCutPayload.observation, SortableObs.nativeDepth, ih]

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
