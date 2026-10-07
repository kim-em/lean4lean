import Lean4Lean.Theory.Typing.Countermodel.Derivation

/-!
# From non-derivability in the smaller context to failure of strengthening

`VEnv.Strengthening` is the definition of branch `agent/verify-inductives-e3`
(`Theory/Typing/UniqueTyping.lean`), restated here: it is the inverse
direction of `IsDefEqU.weakN_iff`.
-/

namespace Lean4Lean

/-- Context strengthening for definitional equality (as on branch e3). -/
def VEnv.Strengthening (env : VEnv) : Prop :=
  ∀ ⦃U n k Γ Γ' e1 e2⦄, Ctx.LiftN n k Γ Γ' → OnCtx Γ' (env.IsType U) →
    env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) → env.IsDefEqU U Γ e1 e2

namespace Countermodel

/-- Strengthening would identify the two endpoints in the smaller context. -/
theorem strengthening_forces (h : envCM.Strengthening) : envCM.IsDefEqU 0 ctxS SI SJ :=
  h ctx_lift ctxL_wf ⟨_, larger_defeq⟩

/-- The refutation, given non-derivability of `SI ≡ SJ` in the smaller context. -/
theorem strengthening_fails_of_separated (hsep : ¬ envCM.IsDefEqU 0 ctxS SI SJ) :
    ∃ env : VEnv, VEnv.WF env ∧ ¬ env.Strengthening :=
  ⟨envCM, envCM_wf, fun h => hsep (strengthening_forces h)⟩

end Countermodel
end Lean4Lean
