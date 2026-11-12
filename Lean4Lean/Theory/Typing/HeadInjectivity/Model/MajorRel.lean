import Lean4Lean.Theory.Typing.HeadInjectivity.Model.SpineVal
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.RigidRel

/-! # A Pi telescope split at its last domain

`wrapForalls_last`, used to isolate the major premise of a recursor type. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

/-- A Pi telescope split at its last domain. -/
theorem wrapForalls_last {ds : List VExpr} {R : VExpr} {n : Nat} (hn : ds.length = n + 1) :
    VExpr.wrapForalls ds R = .wrapForalls (ds.take n ++ [ds[n]'(by omega)]) R := by
  congr 1
  rw [← List.take_succ_eq_append_getElem (by omega), ← hn, List.take_length]

end Model
end VEnv
end Lean4Lean
