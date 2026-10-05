import Lean4Lean.Theory.Typing.AnchoredFamilyArgumentGrades
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceObservation

/-! Literal family requests can be raised to the constructor arguments'
common rank without turning the result certificate into a padded atom.
Both input and fixed support are raised; every source leaf is retained. -/
namespace Lean4Lean.AnchoredProfiles
open AnchoredSource
set_option backward.isDefEq.respectTransparency false

def FamilyData.raise (N : Nat) (bound : n ≤ N) (family : FamilyData (Profile n)) :
    FamilyData (Profile N) := family.map id (raiseProfile N bound)

theorem FamilyData.raise_self (family : FamilyData (Profile n)) :
    family.raise n (Nat.le_refl n) = family := by
  unfold raise
  rw [show raiseProfile n (Nat.le_refl n) = id from funext (fun p => raiseProfile_self p)]
  exact FamilyData.map_id family

theorem FamilyData.raise_step {n N : Nat} (family : FamilyData (Profile n)) (bound : n ≤ N) :
    family.raise (N + 1) (Nat.le_trans bound (Nat.le_succ N)) =
      (family.raise N bound).map id Profile.pad := by
  simp only [raise, FamilyData.map_map, Function.comp_def, id_eq]
  congr 1
  funext profile
  exact raiseProfile_step bound profile

end Lean4Lean.AnchoredProfiles

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

noncomputable def CodeCert.raiseFamily
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {seed : Subst} {expression : VExpr}
    {family : FamilyData (Profile n)} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals seed expression
      (Profile.singleton (n := n + 1) (.family family)) footprint)
    (N : Nat) (bound : n ≤ N) :
    CodeCert env U registry target locals seed expression
      (Profile.singleton (n := N + 1) (.family (family.raise N bound))) footprint := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    simpa only [FamilyData.raise_self] using certificate
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      simpa only [FamilyData.raise_self] using certificate
    · have low : n ≤ N := by omega
      rw [FamilyData.raise_step family low]
      exact .familyPad (ih low)

end Lean4Lean.AnchoredSource.Adapted
