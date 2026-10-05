import Lean4Lean.Theory.Typing.AnchoredAtomAction
import Lean4Lean.Theory.Typing.AnchoredFunctionGradeView

/-! A finite action can be padded to the actual rank of a returned query. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles AnchoredSource
set_option backward.isDefEq.respectTransparency false

noncomputable def AtomAction.raise {n N : Nat} {a b : Atom n}
    (bound : n ≤ N) (action : AtomAction env U registry Γ a b) :
    AtomAction env U registry Γ (raiseAtom N bound a) (raiseAtom N bound b) := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    exact action
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      simpa only [raiseAtom_self] using action
    · have previous : n ≤ N := by omega
      simpa only [raiseAtom_step previous] using AtomAction.pad (ih previous)

end Lean4Lean.AnchoredSemantics
