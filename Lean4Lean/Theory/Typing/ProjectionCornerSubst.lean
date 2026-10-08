import Lean4Lean.Theory.Typing.NativeSingletonTyping
import Lean4Lean.Theory.Typing.LevelEquiv

/-! # Lifting a lifted substitution -/

namespace Lean4Lean
namespace VExpr

theorem Subst.lift_liftN (σ : Subst) : ∀ i, σ.lift.liftN i = σ.liftN (i + 1)
  | 0 => rfl
  | i + 1 => by
    show (σ.lift.liftN i).lift = (σ.liftN (i + 1)).lift
    rw [Subst.lift_liftN σ i]

end VExpr
end Lean4Lean
