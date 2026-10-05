import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceReflection

/-! Finite resource accounting for inverse substitution. A cut records the
actual argument observation it removes; all surrounding variable leaves are
retained. Passing under a binder preserves its exact consumed input. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

def insertIndex (depth index : Nat) : Nat := if index < depth then index else index + 1

@[simp] theorem insertIndex_zero (depth : Nat) : insertIndex (depth + 1) 0 = 0 := by
  simp [insertIndex]

@[simp] theorem insertIndex_succ (depth index : Nat) :
    insertIndex (depth + 1) (index + 1) = insertIndex depth index + 1 := by
  simp only [insertIndex, Nat.add_lt_add_iff_right]
  split <;> rfl

def shiftFootprint (depth : Nat) (footprint : Footprint) : Footprint :=
  footprint.map fun (index, need) => (index + depth, need)

theorem shiftFootprint_sourceLift (depth : Nat) (footprint : Footprint) :
    shiftFootprint depth footprint = footprint.sourceLift (.skipN .refl depth) := by
  apply List.map_congr_left
  intro entry member
  simp [Lift.liftVar_skipN, Lift.liftVar, Nat.add_comm]

theorem shiftFootprint_succ (depth : Nat) (footprint : Footprint) :
    shiftFootprint (depth + 1) footprint =
      (shiftFootprint depth footprint).sourceLift (.skip .refl) := by
  simp only [shiftFootprint, Footprint.sourceLift, List.map_map]
  rfl

inductive InstFootprint (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (argument : VExpr)
    (depth : Nat) : Footprint → Footprint → Type where
  | nil : InstFootprint env U registry Γ locals σ argument depth [] []
  | keep (index : Nat) (need : Need)
      (tail : InstFootprint env U registry Γ locals σ argument depth before after) :
      InstFootprint env U registry Γ locals σ argument depth
        ((index, need) :: before) ((insertIndex depth index, need) :: after)
  | cut {demand : Profile n} {argumentFootprint : Footprint}
      (observation : Obs env U registry Γ locals σ argument demand argumentFootprint)
      (tail : InstFootprint env U registry Γ locals σ argument depth before after) :
      InstFootprint env U registry Γ locals σ argument depth
        (shiftFootprint depth argumentFootprint ++ before) ((depth, ⟨n, demand⟩) :: after)

noncomputable def InstFootprint.append
    (first : InstFootprint env U registry Γ locals σ argument depth before₁ after₁)
    (second : InstFootprint env U registry Γ locals σ argument depth before₂ after₂) :
    InstFootprint env U registry Γ locals σ argument depth
      (before₁ ++ before₂) (after₁ ++ after₂) := by
  induction first with
  | nil => exact second
  | keep index need tail ih => exact .keep index need ih
  | cut observation tail ih =>
    simpa only [List.append_assoc, List.cons_append] using InstFootprint.cut observation ih

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

theorem InstFootprint.underBinder
    (factor : InstFootprint env U registry Γ locals σ argument (depth + 1) before after)
    (pack : BinderPack n input before outside) :
    ∃ newOutside, BinderPack n input after newOutside ∧
      Nonempty (InstFootprint env U registry Γ locals σ argument depth outside newOutside) := by
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
          ⟨InstFootprint.keep index need factor⟩⟩
  | cut observation tail ih =>
    rw [shiftFootprint_succ] at pack
    obtain ⟨rest, normal, he⟩ := BinderPack.strip_external pack
    obtain ⟨newOutside, normal', ⟨factor⟩⟩ := ih normal
    subst outside
    exact ⟨(depth, _) :: newOutside, .external depth _ normal',
      ⟨InstFootprint.cut observation factor⟩⟩

end Lean4Lean.AnchoredSource.Adapted
