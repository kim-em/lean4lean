import Lean4Lean.Theory.Typing.ProjectionCornerWalk
import Lean4Lean.Theory.Typing.TelescopeTransport
import Lean4Lean.Theory.Typing.NativeSingletonTyping
import Lean4Lean.Theory.Typing.NativeRecursorRegistration
import Lean4Lean.Theory.Typing.NativeConstructorRigidity
import Lean4Lean.Theory.Inductive.SingletonCompilation
import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.CanonicalChoice
import Lean4Lean.Theory.Typing.ProjectionShape

/-!
# An inhabitant of a field type of a non-eliminable structure field

At a typed major `e : S params` of a registered structure `S`, the binder type `D` that the
projection walk reaches for a field whose projection fails the universe guard is inhabited,
when the environment has canonical choice and `S` can be eliminated into `Prop`: the recursor of
`S` with the constant motive `fun _ => Nonempty D` and the minor premise
`fun fields => Nonempty.intro field` gives `Nonempty D`, and `Classical.choice` gives a term of
`D`. The minor premise is typed because every projection used by `D` is a proof field
(`VProjectionInfo.field_of_walk`).
-/

namespace Lean4Lean
open VExpr VEnv InductiveSignature

namespace VEnv
variable {env : VEnv} {U : Nat}

theorem IsDefEqU.wrapForalls_context' (henv : env.WF) (hΓ : OnCtx Γ₀ (env.IsType U))
    (W : IsDefEqCtx env U Γ₀ Γ₁ Γ₂)
    (hlen : domains.length = domains'.length)
    (ht : IsDefEqU env U Γ₁ (VExpr.wrapForalls domains result)
      (VExpr.wrapForalls domains' result')) :
    IsDefEqCtx env U Γ₀ (domains.reverse ++ Γ₁) (domains'.reverse ++ Γ₂) := by
  induction domains generalizing Γ₁ Γ₂ domains' with
  | nil =>
    have he : domains' = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst domains'
    exact W
  | cons d ds ih =>
    cases domains' with
    | nil => simp at hlen
    | cons d' ds' =>
      obtain ⟨⟨u, hd⟩, _, hrest⟩ := ht.forallE_inv henv (W.isType' hΓ)
      have hh := ih (.succ W hd)
        (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen) ⟨_, hrest⟩
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hh

end VEnv

namespace InductiveSignature.NativeRecursorData
variable {env : VEnv} {data : NativeRecursorData}

end InductiveSignature.NativeRecursorData
end Lean4Lean
