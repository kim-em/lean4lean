import Lean4Lean.Theory.Typing.HeadInjectivity.Model.SpineVal

/-! # Key classes of a spine

`keys_cls_self`: the key classes of the observations of a spine contain the spine's
arguments. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-- The key classes of a spine contain the arguments. -/
theorem keys_cls_self {σ : VExpr.Subst} {S : ObSets} : ∀ {keys : List Key} {args : List VExpr},
    List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Δ k.1 (a.subst σ) ∧
      ∀ x ∈ k.2.2, ∃ x', Obs' σ S a x' ∧ x' ≼ x) keys args →
    List.Forall₂ (fun (k : Key) b => k.2.1 b) keys (args.map (·.subst σ))
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (by rw [h.1]; exact ElCls.self) (keys_cls_self t)

end Model
end VEnv
end Lean4Lean
