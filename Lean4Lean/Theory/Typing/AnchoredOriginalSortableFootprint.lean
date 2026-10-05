import Lean4Lean.Theory.Typing.AnchoredSortableReflection
import Lean4Lean.Theory.Typing.AnchoredOriginalFactorTraversal

/-! Original-location inverse-substitution evidence with an explicit sortable
whole-cut channel. Native proof-relevant Pi rows remain certificates; they are
never represented as a legacy computational observation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false

structure WholeSortableCutQuery
    {sourceEnv env : VEnv} {U : Nat} {rootSource : List VExpr} {rootExpression rootType : VExpr}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {argument : VExpr} {baseDepth : Nat}
    (origin : OriginalEndpointFactor.CutOriginAt root boundary argument baseDepth)
    (registry : CanonicalHead.Registry) (Γ : List VExpr) (σ : Subst)
    (relevant : Bool) (demand : Profile n) (argumentFootprint : Footprint) where
  locals : List Nat
  realization : Subst
  footprint : Footprint
  certificate : SortableCert env U registry Γ locals realization origin.expression relevant demand footprint
  tail_eq : Subst.lift_l (.skipN .refl origin.depth) realization = σ
  footprint_eq : footprint = argumentFootprint.sourceLift (.skipN .refl origin.depth)


structure WholeObservedCutQuery
    {sourceEnv env : VEnv} {U : Nat} {rootSource : List VExpr} {rootExpression rootType : VExpr}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {argument : VExpr} {baseDepth : Nat}
    (origin : OriginalEndpointFactor.CutOriginAt root boundary argument baseDepth)
    (registry : CanonicalHead.Registry) (Γ : List VExpr) (σ : Subst)
    (demand : Profile n) (argumentFootprint : Footprint) where
  locals : List Nat
  realization : Subst
  footprint : Footprint
  observation : SortableObs env U registry Γ locals realization origin.expression demand footprint
  tail_eq : Subst.lift_l (.skipN .refl origin.depth) realization = σ
  footprint_eq : footprint = argumentFootprint.sourceLift (.skipN .refl origin.depth)


/-- A captured request is either an actual legacy observation or a complete
Boolean-indexed formation query, together with its pre-reflection syntax. -/
inductive SortableCutPayload
    {env : VEnv}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (origin : CutOriginAt root boundary argument baseDepth)
    (registry : CanonicalHead.Registry) (Γ : List VExpr) (locals : List Nat)
    (σ : Subst) (demand : Profile n) (footprint : Footprint) : Type where
  | legacy
      (observation : Obs env U registry Γ locals σ argument demand footprint)
      (whole : WholeCutQuery (env := env) origin registry Γ σ demand footprint) :
      SortableCutPayload (env := env) origin registry Γ locals σ demand footprint
  | observed
      (observation : SortableObs env U registry Γ locals σ argument demand footprint)
      (whole : WholeObservedCutQuery (env := env) origin registry Γ σ demand footprint) :
      SortableCutPayload (env := env) origin registry Γ locals σ demand footprint
  | sortable (relevant : Bool)
      (certificate : SortableCert env U registry Γ locals σ argument relevant demand footprint)
      (whole : WholeSortableCutQuery (env := env) origin registry Γ σ relevant demand footprint) :
      SortableCutPayload (env := env) origin registry Γ locals σ demand footprint

inductive SortableLocatedFootprint
    {sourceEnv env : VEnv} {U : Nat} {rootSource : List VExpr} {rootExpression rootType : VExpr}
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (boundary : List VExpr) (registry : CanonicalHead.Registry) (Γ : List VExpr) (locals : List Nat)
    (σ : Subst) (argument : VExpr) (baseDepth depth : Nat)
    (budget : List Closure → Nat) : Footprint → Footprint → Type where
  | nil : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget [] []
  | keep (index : Nat) (need : Need)
      (tail : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after) :
      SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget
        ((index, need) :: before) ((insertIndex depth index, need) :: after)
  | cut {demand : Profile n} {argumentFootprint : Footprint}
      (origin : OriginalEndpointFactor.CutOriginAt root boundary argument baseDepth)
      (payload : SortableCutPayload (env := env) origin registry Γ locals σ demand argumentFootprint)
      (bounded : ∀ initial, (Closure.close origin.view.origin
        (origin.location.environment initial)).cost ≤ budget initial)
      (tail : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after) :
      SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget
        (shiftFootprint depth argumentFootprint ++ before) ((depth, ⟨n, demand⟩) :: after)

noncomputable def SortableLocatedFootprint.ofLegacy
    (trace : BoundedLocatedFootprintAt (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after) :
    SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after := by
  induction trace with
  | nil => exact .nil
  | keep index need _ ih => exact .keep index need ih
  | cut origin observation whole bounded _ ih => exact .cut origin (.legacy observation whole) bounded ih

def SortableLocatedFootprint.cost
    (trace : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after)
    (initial : List Closure) : Nat :=
  match trace with
  | .nil => 0
  | .keep _ _ tail => tail.cost initial
  | .cut origin _ _ tail => max
      (Closure.close origin.view.origin (origin.location.environment initial)).cost
      (tail.cost initial)

theorem SortableLocatedFootprint.cost_le
    (trace : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after)
    (initial : List Closure) : trace.cost initial ≤ budget initial := by
  induction trace with
  | nil => exact Nat.zero_le _
  | keep _ _ _ ih => exact ih
  | cut _ _ bounded _ ih => exact Nat.max_le.mpr ⟨bounded initial, ih⟩

private theorem BinderPack.strip_external
    (pack : BinderPack n input (before.sourceLift (.skip .refl) ++ required) outside) :
    ∃ rest, BinderPack n input required rest ∧ outside = before ++ rest := by
  induction before generalizing outside with
  | nil => exact ⟨outside, pack, rfl⟩
  | cons entry tail ih =>
    obtain ⟨index, need⟩ := entry
    cases pack with
    | external _ _ rest =>
      obtain ⟨outside, normal, he⟩ := ih rest
      exact ⟨outside, normal, congrArg (List.cons (index, need)) he⟩

noncomputable def SortableLocatedFootprint.weaken
    (trace : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before after)
    (bound : ∀ initial, budget initial ≤ larger initial) :
    SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth larger before after := by
  induction trace with
  | nil => exact .nil
  | keep index need _ ih => exact .keep index need ih
  | cut origin payload bounded _ ih =>
    exact .cut origin payload (fun initial => Nat.le_trans (bounded initial) (bound initial)) ih

noncomputable def SortableLocatedFootprint.append
    (first : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before₁ after₁)
    (second : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget before₂ after₂) :
    SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget
      (before₁ ++ before₂) (after₁ ++ after₂) := by
  induction first with
  | nil => exact second
  | keep index need _ ih => exact .keep index need ih
  | cut origin payload bounded _ ih =>
    simpa only [List.append_assoc, List.cons_append] using
      SortableLocatedFootprint.cut origin payload bounded ih

theorem SortableLocatedFootprint.underBinder
    (factor : SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth (depth + 1) budget before after)
    (pack : BinderPack n input before outside) :
    ∃ newOutside, BinderPack n input after newOutside ∧
      Nonempty (SortableLocatedFootprint (env := env) root boundary registry Γ locals σ argument baseDepth depth budget outside newOutside) := by
  induction factor generalizing input outside with
  | nil => cases pack; exact ⟨[], .nil, ⟨.nil⟩⟩
  | keep index need tail ih =>
    cases index with
    | zero =>
      cases pack with
      | «local» _ bound rest =>
        obtain ⟨newOutside, normal, factor⟩ := ih rest
        exact ⟨newOutside, by simpa only [insertIndex_zero] using BinderPack.local need bound normal,
          factor⟩
    | succ index =>
      cases pack with
      | external _ _ rest =>
        obtain ⟨newOutside, normal, ⟨factor⟩⟩ := ih rest
        exact ⟨(insertIndex depth index, need) :: newOutside,
          by simpa only [insertIndex_succ] using BinderPack.external _ need normal,
          ⟨SortableLocatedFootprint.keep index need factor⟩⟩
  | cut origin payload bounded tail ih =>
    rw [shiftFootprint_succ] at pack
    obtain ⟨rest, normal, he⟩ := BinderPack.strip_external pack
    obtain ⟨newOutside, normal', ⟨factor⟩⟩ := ih normal
    subst outside
    exact ⟨(depth, _) :: newOutside, .external depth _ normal',
      ⟨SortableLocatedFootprint.cut origin payload bounded factor⟩⟩


end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
