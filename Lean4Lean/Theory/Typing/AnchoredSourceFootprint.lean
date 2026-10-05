import Lean4Lean.Theory.Typing.AnchoredSourceObservation

/-! Source renaming changes only lookup indices. Target demands and their
grades are retained, including every local leaf packaged by a binder. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

def Footprint.sourceLift (ρ : Lift) (required : Footprint) : Footprint :=
  required.map fun (i, need) => (ρ.liftVar i, need)

theorem Footprint.sourceLift_append (ρ : Lift) (left right : Footprint) :
    (left ++ right).sourceLift ρ = left.sourceLift ρ ++ right.sourceLift ρ :=
  List.map_append

/-- Renaming the external source context fixes the freshly bound variable. -/
theorem BinderPack.sourceLift {input : Profile n} {required outside : Footprint}
    (h : BinderPack n input required outside) (ρ : Lift) :
    BinderPack n input (required.sourceLift ρ.cons) (outside.sourceLift ρ) := by
  induction h with
  | nil => exact .nil
  | «local» need bound rest ih => exact .«local» need bound ih
  | external i need rest ih => exact .external (ρ.liftVar i) need ih

/-- A packed renamed footprint has a unique original pattern of local and
external entries. The existing demand and every grade bound are retained. -/
theorem BinderPack.sourceLift_inv {input : Profile n} {required outside' : Footprint}
    {ρ : Lift} (h : BinderPack n input (required.sourceLift ρ.cons) outside') :
    ∃ outside, BinderPack n input required outside ∧ outside' = outside.sourceLift ρ := by
  induction required generalizing input outside' with
  | nil =>
    cases h
    exact ⟨[], .nil, rfl⟩
  | cons entry rest ih =>
    rcases entry with ⟨i, need⟩
    cases i with
    | zero =>
      change BinderPack n input ((0, need) :: Footprint.sourceLift ρ.cons rest) outside' at h
      cases h with
      | «local» _ bound tail =>
        obtain ⟨outside, normal, rfl⟩ := ih tail
        exact ⟨outside, .«local» need bound normal, rfl⟩
    | succ i =>
      change BinderPack n input ((ρ.liftVar i + 1, need) :: Footprint.sourceLift ρ.cons rest) outside' at h
      cases h with
      | external _ _ tail =>
        obtain ⟨outside, normal, rfl⟩ := ih tail
        exact ⟨(i, need) :: outside, .external i need normal, rfl⟩

end Lean4Lean.AnchoredSource
