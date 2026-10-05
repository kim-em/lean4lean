import Lean4Lean.Theory.Typing.Strong

/-! Raw substitution for a sparse declaration template uses the retained
instantiated source judgment, not a typing judgment for its partial capture
map. In particular, the map may assign untypable expressions to slots absent
from the displayed judgment. This does not construct or thin an original
proof: the instantiated judgment must come from the retained actual original.
-/
namespace Lean4Lean.VEnv
open VExpr VEnv

/-- Substitute through a syntactic declaration display. No `Ctx.SubstEq`
premise is imposed on `capture`: all raw typing is supplied by the actual
instantiated source proof, and only that source context is substituted. -/
theorem IsDefEq.substDF_throughDisplay
    {env : VEnv} {U : Nat} {source target : List VExpr}
    {capture left right : VExpr.Subst} {e e' type actual actual' actualType : VExpr}
    (ordered : env.Ordered)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (original : env.IsDefEq U source actual actual' actualType)
    (leftDisplay : actual = e.subst capture)
    (rightDisplay : actual' = e'.subst capture)
    (typeDisplay : actualType = type.subst capture) :
    env.IsDefEq U target (e.subst (capture.comp left))
      (e'.subst (capture.comp right)) (type.subst (capture.comp left)) := by
  have result := original.substDF ordered substitutions.wf formed substitutions
  simpa only [leftDisplay, rightDisplay, typeDisplay, VExpr.subst_subst] using result

/-- The same invariant extends under a real source binder. Its domain is the
instantiated declaration domain, so no typing of omitted declaration slots
is needed to extend the actual paired source substitution. -/
theorem IsDefEq.substDF_throughDisplay_cons
    {env : VEnv} {U : Nat} {source target : List VExpr}
    {capture left right : VExpr.Subst} {A e e' type actual actual' actualType x y : VExpr}
    {level : VLevel}
    (ordered : env.Ordered)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (domain : env.HasType U source (A.subst capture) (.sort level))
    (arguments : env.IsDefEq U target x y ((A.subst capture).subst left))
    (original : env.IsDefEq U (A.subst capture :: source) actual actual' actualType)
    (leftDisplay : actual = e.subst capture.lift)
    (rightDisplay : actual' = e'.subst capture.lift)
    (typeDisplay : actualType = type.subst capture.lift) :
    env.IsDefEq U target (e.subst (capture.lift.comp (left.cons x)))
      (e'.subst (capture.lift.comp (right.cons y)))
      (type.subst (capture.lift.comp (left.cons x))) := by
  exact original.substDF_throughDisplay ordered formed
    (.cons substitutions domain arguments) leftDisplay rightDisplay typeDisplay

end Lean4Lean.VEnv
