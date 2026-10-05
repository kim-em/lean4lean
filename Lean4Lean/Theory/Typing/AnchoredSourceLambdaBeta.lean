import Lean4Lean.Theory.Typing.AnchoredSourceLambdaBehavior
import Lean4Lean.Theory.Typing.AnchoredSourceFuture

/-! The original lambda premises supply the precise raw beta equalities used
to expand the three interpreted body outputs. Annotations may differ. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem lambda_beta_outputs
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {left right : Subst}
    {A A' B body other x y : VExpr} {output : Atom n} {support : Profile n}
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (leftBody : env.HasType U (A :: source) body B)
    (rightBody : env.HasType U (A' :: source) other B)
    (arguments : env.IsDefEq U target x y (A.subst left))
    (leftOutput : Related env U registry target (body.subst (left.cons x))
      (body.subst (left.cons y)) (B.subst (left.cons x)) (.singleton output) support)
    (rightOutput : Related env U registry target (other.subst (right.cons x))
      (other.subst (right.cons y)) (B.subst (left.cons x)) (.singleton output) support)
    (crossOutput : Related env U registry target (body.subst (left.cons x))
      (other.subst (right.cons x)) (B.subst (left.cons x)) (.singleton output) support) :
    Related env U registry target (.app ((VExpr.lam A body).subst left) x)
      (.app ((VExpr.lam A body).subst left) y) (B.subst (left.cons x))
      (.singleton output) support ∧
    Related env U registry target (.app ((VExpr.lam A' other).subst right) x)
      (.app ((VExpr.lam A' other).subst right) y) (B.subst (left.cons x))
      (.singleton output) support ∧
    Related env U registry target (.app ((VExpr.lam A body).subst left) x)
      (.app ((VExpr.lam A' other).subst right) x) (B.subst (left.cons x))
      (.singleton output) support := by
  have sourceWF := substitutions.wf
  have targetA := domains.hasType.1.subst henv substitutions.left hTarget
  have leftContext : OnCtx (A.subst left :: target) (env.IsType U) := ⟨hTarget, _, targetA⟩
  have rightSubstitution := substitutions.right henv hTarget
  have targetA' := domains.hasType.2.subst henv rightSubstitution hTarget
  have rightContext : OnCtx (A'.subst right :: target) (env.IsType U) := ⟨hTarget, _, targetA'⟩
  have leftBody' := leftBody.subst henv
    (substitutions.left.lift henv domains.hasType.1) leftContext
  have rightBody' := rightBody.subst henv
    (rightSubstitution.lift henv domains.hasType.2) rightContext
  have domainEq := domains.substDF henv sourceWF hTarget substitutions
  have rightX := IsDefEq.defeqDF domainEq arguments.hasType.1
  have rightY := IsDefEq.defeqDF domainEq arguments.hasType.2
  have sourceContext : OnCtx (A :: source) (env.IsType U) := ⟨sourceWF, _, domains.hasType.1⟩
  have pairXY : Ctx.SubstEq env U target (left.cons x) (left.cons y) (A :: source) :=
    .cons substitutions.left domains.hasType.1 arguments
  have pairRX : Ctx.SubstEq env U target (left.cons x) (right.cons x) (A :: source) :=
    .cons substitutions domains.hasType.1 arguments.hasType.1
  have pairRY : Ctx.SubstEq env U target (left.cons x) (right.cons y) (A :: source) :=
    .cons substitutions domains.hasType.1 arguments
  have bodyXY := codomain.substDF henv sourceContext hTarget pairXY
  have bodyRX := codomain.substDF henv sourceContext hTarget pairRX
  have bodyRY := codomain.substDF henv sourceContext hTarget pairRY
  simp only [subst_sort] at domainEq bodyXY bodyRX bodyRY
  have lx := IsDefEq.beta leftBody' arguments.hasType.1
  have ly := IsDefEq.beta leftBody' arguments.hasType.2
  have rx := IsDefEq.beta rightBody' rightX
  have ry := IsDefEq.beta rightBody' rightY
  simp only [inst_lift_cons] at lx ly rx ry
  have ly := IsDefEq.defeqDF bodyXY.symm ly
  have rx := IsDefEq.defeqDF bodyRX.symm rx
  have ry := IsDefEq.defeqDF bodyRY.symm ry
  have betaLeftX : HeadBeta (.app ((VExpr.lam A body).subst left) x)
      (body.subst (left.cons x)) := by
    simpa only [mkApps, List.foldl_cons, List.foldl_nil, subst, inst_lift_cons] using
      (HeadBeta.contract (A := A.subst left) (body := body.subst left.lift)
        (argument := x) (trailing := []))
  have betaLeftY : HeadBeta (.app ((VExpr.lam A body).subst left) y)
      (body.subst (left.cons y)) := by
    simpa only [mkApps, List.foldl_cons, List.foldl_nil, subst, inst_lift_cons] using
      (HeadBeta.contract (A := A.subst left) (body := body.subst left.lift)
        (argument := y) (trailing := []))
  have betaRightX : HeadBeta (.app ((VExpr.lam A' other).subst right) x)
      (other.subst (right.cons x)) := by
    simpa only [mkApps, List.foldl_cons, List.foldl_nil, subst, inst_lift_cons] using
      (HeadBeta.contract (A := A'.subst right) (body := other.subst right.lift)
        (argument := x) (trailing := []))
  have betaRightY : HeadBeta (.app ((VExpr.lam A' other).subst right) y)
      (other.subst (right.cons y)) := by
    simpa only [mkApps, List.foldl_cons, List.foldl_nil, subst, inst_lift_cons] using
      (HeadBeta.contract (A := A'.subst right) (body := other.subst right.lift)
        (argument := y) (trailing := []))
  exact ⟨Related.headBeta henv betaLeftX betaLeftY lx ly leftOutput,
    Related.headBeta henv betaRightX betaRightY rx ry rightOutput,
    Related.headBeta henv betaLeftX betaRightX lx rx crossOutput⟩

end Lean4Lean.AnchoredSource
