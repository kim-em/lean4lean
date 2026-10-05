import Lean4Lean.Theory.Typing.AnchoredAdmission
import Lean4Lean.Theory.Typing.AnchoredMixedTransport

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

/-- Argument grades may differ because every stored Pi row consumes one
grade. A whole family demand bounds this finite list strictly below its grade. -/
structure FamilyKey where
  rank : Nat
  key : Key rank
  support : Profile rank

def FamilyKey.request (key : FamilyKey) : DataRequest (Profile key.rank) :=
  ⟨key.key, key.support⟩

def FamilyKey.bound (keys : List FamilyKey) : Nat :=
  (keys.map (·.rank)).foldr max 0 + 1

theorem FamilyKey.lt_bound {key : FamilyKey} {keys : List FamilyKey}
    (member : key ∈ keys) : key.rank < FamilyKey.bound keys := by
  suffices key.rank ≤ (keys.map (·.rank)).foldr max 0 by
    simp only [FamilyKey.bound]; omega
  induction keys with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simp only [List.map_cons, List.foldr_cons]; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

/-- The binary data-code clause retains actual per-position admissions;
parameters and indices occupy their exact declaration positions. -/
inductive FamilyArguments (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) : List FamilyKey → List VExpr → List VExpr → Prop where
  | nil : FamilyArguments env U registry target [] [] []
  | cons : RankedData.RequestAdmission env U (relations env U registry key.rank)
      target key.request x y →
      FamilyArguments env U registry target keys xs ys →
      FamilyArguments env U registry target (key :: keys) (x :: xs) (y :: ys)

end Lean4Lean.AnchoredSemantics
