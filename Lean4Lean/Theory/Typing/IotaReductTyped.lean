import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.RecursorLemmas

/-! # The reducts of the registered ι rules are typed

`IsDefEq.pat` carries the typing of the reduct as a premise. `VEnv.WF.iotaReductTyped` is the
theorem that makes the premise available: in a well-formed environment and a well-formed
context, the reduct of a typed instance of a registered ι rule is typed at the redex's type. -/

namespace Lean4Lean.VEnv

/-- **The reducts of the registered ι rules are typed.** -/
theorem WF.iotaReductTyped {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {p : Pattern} {r : p.RHS × p.Check} {e A : VExpr} {m1 m2}
    (hpat : env.pats p r) (hm : p.Matches e m1 m2) (hty : env.HasType U Γ e A) :
    env.HasType U Γ (r.1.apply m1 m2) A := sorry

end Lean4Lean.VEnv
