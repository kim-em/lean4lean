import Lean4Lean.Theory.Typing.AnchoredSourceFuture

/-! The right-realized eta expression is converted back to the actual
left-realized caller Pi by the original domain and codomain formation. -/
namespace Lean4Lean.VEnv
open VExpr

theorem IsDefEq.eta_subst_right
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B)) :
    env.IsDefEq U target ((VExpr.lam A (.app f.lift (.bvar 0))).subst τ)
      (f.subst τ) ((VExpr.forallE A B).subst σ) := by
  have piTyped := IsDefEq.forallEDF formedA formedB
  have piEq := piTyped.substDF henv substitutions.wf hTarget substitutions
  have etaRight := (IsDefEq.eta functionTyped).subst henv
    (substitutions.right henv hTarget) hTarget
  exact .defeqDF piEq.symm etaRight

end Lean4Lean.VEnv
