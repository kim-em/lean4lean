import Lean4Lean.Theory.Typing.CaseMotive

/-! Recover the target universe from the motive supplied to a generated case
application. Only motive binders actually used by the application matter. -/

set_option maxHeartbeats 1000000

namespace Lean4Lean.InductiveSignature

end Lean4Lean.InductiveSignature

namespace Lean4Lean.VEnv
variable {env : VEnv} {U : Nat}
open VExpr InductiveSignature InductiveSignature.CaseSchema

/-- Equal telescope types ending in sorts have the same final universe,
even when their domain lists have not been identified in advance. -/
theorem IsDefEqU.wrapForalls_sort_level (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEqU U Γ (wrapForalls ds₁ (.sort u)) (wrapForalls ds₂ (.sort v))) :
    u ≈ v := by
  induction ds₁ generalizing Γ ds₂ with
  | nil =>
    cases ds₂ with
    | nil => exact H.sort_inv henv hΓ
    | cons d ds => exact False.elim (IsDefEqU.sort_forallE_inv henv hΓ H)
  | cons d ds ih =>
    cases ds₂ with
    | nil => exact False.elim (IsDefEqU.sort_forallE_inv henv hΓ H.symm)
    | cons d' ds' =>
      obtain ⟨⟨_, hd⟩, _, hb⟩ := H.forallE_inv henv hΓ
      have hctx : OnCtx (d :: Γ) (env.IsType U) := ⟨hΓ, _, hd.hasType.1⟩
      exact ih hctx ⟨_, hb⟩

end Lean4Lean.VEnv
