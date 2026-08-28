import Lean4Lean.Verify.Inductive.Nested.EquationRestoration
import Lean4Lean.Verify.Inductive.Nested.Replacement

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Semantic interpretation of one exact concrete replacement hit.  The
production callback equality is only an index; the two translations and the
abstract callback equality are independent proof data.  Later nested-family,
constructor, and recursor cases construct this object from their retained
provenance witnesses. -/
structure RestoredNodeInterpretation
    (concreteReplace : Expr → Option Expr)
    (abstractReplace : VExpr → Option VExpr)
    (sourceEnv targetEnv : VEnv) (Us : List Name)
    (sourceContext targetContext : VLCtx)
    {input output : Expr} {source target : VExpr}
    (Hhit : concreteReplace input = some output) : Prop where
  sourceTranslation :
    TrExprS sourceEnv Us sourceContext input source
  targetTranslation :
    TrExprS targetEnv Us targetContext output target
  abstractHit : abstractReplace source = some target

/-- Structural alignment of a concrete replacement trace with its abstract
counterpart.  Every hit must be justified by an exact node interpretation;
all other constructors recurse in lockstep.  The generated equations use only
this common kernel-expression fragment, so erased metadata, lets, literals,
and projections are deliberately not admitted as unexplained alignment cases.
-/
inductive ExprRestorationAlignment
    (concreteReplace : Expr → Option Expr)
    (abstractReplace : VExpr → Option VExpr) :
    {input output : Expr} → {source target : VExpr} →
    ExprReplacement concreteReplace input output →
    VExprRestoration abstractReplace source target → Prop
  | hit
      (H : RestoredNodeInterpretation concreteReplace abstractReplace
        sourceEnv targetEnv Us sourceContext targetContext Hhit) :
      ExprRestorationAlignment concreteReplace abstractReplace
        (ExprReplacement.hit Hhit) (.hit H.abstractHit)
  | bvar (hconcrete : concreteReplace (.bvar i) = none)
      (habstract : abstractReplace (.bvar i) = none) :
      ExprRestorationAlignment concreteReplace abstractReplace
        (.bvar hconcrete) (.bvar habstract)
  | sort (hconcrete : concreteReplace (.sort level) = none)
      (habstract : abstractReplace (.sort u) = none) :
      ExprRestorationAlignment concreteReplace abstractReplace
        (.sort hconcrete) (.sort habstract)
  | const (hconcrete : concreteReplace (.const name levels) = none)
      (habstract : abstractReplace (.const name abstractLevels) = none) :
      ExprRestorationAlignment concreteReplace abstractReplace
        (.const hconcrete) (.const habstract)
  | app (hconcrete : concreteReplace (.app fn arg) = none)
      (habstract : abstractReplace (.app sourceFn sourceArg) = none)
      (hfn : ExprRestorationAlignment concreteReplace abstractReplace
        concreteFn abstractFn)
      (harg : ExprRestorationAlignment concreteReplace abstractReplace
        concreteArg abstractArg) :
      ExprRestorationAlignment concreteReplace abstractReplace
        (.app hconcrete concreteFn concreteArg)
        (.app habstract abstractFn abstractArg)
  | lam
      (hconcrete : concreteReplace (.lam name domain body bi) = none)
      (habstract : abstractReplace (.lam sourceDomain sourceBody) = none)
      (hdomain : ExprRestorationAlignment concreteReplace abstractReplace
        concreteDomain abstractDomain)
      (hbody : ExprRestorationAlignment concreteReplace abstractReplace
        concreteBody abstractBody) :
      ExprRestorationAlignment concreteReplace abstractReplace
        (.lam hconcrete concreteDomain concreteBody)
        (.lam habstract abstractDomain abstractBody)
  | forallE
      (hconcrete : concreteReplace (.forallE name domain body bi) = none)
      (habstract : abstractReplace (.forallE sourceDomain sourceBody) = none)
      (hdomain : ExprRestorationAlignment concreteReplace abstractReplace
        concreteDomain abstractDomain)
      (hbody : ExprRestorationAlignment concreteReplace abstractReplace
        concreteBody abstractBody) :
      ExprRestorationAlignment concreteReplace abstractReplace
        (.forallE hconcrete concreteDomain concreteBody)
        (.forallE habstract abstractDomain abstractBody)

/-- An abstract restoration interpreting one exact executable replacement
trace.  The executable trace fixes which concrete expressions are related but
does not supply any semantic field: both endpoint translations and the
structural abstract restoration must be proved independently. -/
structure RestoredExprTranslation
    (concreteReplace : Expr → Option Expr)
    (abstractReplace : VExpr → Option VExpr)
    (sourceEnv targetEnv : VEnv) (Us : List Name)
    (sourceContext targetContext : VLCtx)
    {input output : Expr} {source target : VExpr}
    (Hreplace : ExprReplacement concreteReplace input output) : Prop where
  sourceTranslation :
    TrExprS sourceEnv Us sourceContext input source
  targetTranslation :
    TrExprS targetEnv Us targetContext output target
  abstractRestoration : VExprRestoration abstractReplace source target
  alignment : ExprRestorationAlignment concreteReplace abstractReplace
    Hreplace abstractRestoration

/-- A pointwise node interpretation is the atomic case of structural
expression restoration. -/
theorem RestoredNodeInterpretation.toExprTranslation
    {input output : Expr} {source target : VExpr}
    {Hhit : concreteReplace input = some output}
    (H : RestoredNodeInterpretation concreteReplace abstractReplace
      sourceEnv targetEnv Us sourceContext targetContext
      (input := input) (output := output) (source := source)
      (target := target) Hhit) :
    RestoredExprTranslation concreteReplace abstractReplace
      sourceEnv targetEnv Us sourceContext targetContext
      (input := input) (output := output) (source := source)
      (target := target) (ExprReplacement.hit Hhit) where
  sourceTranslation := H.sourceTranslation
  targetTranslation := H.targetTranslation
  abstractRestoration := .hit H.abstractHit
  alignment := .hit H

/-- The executable trace index can be changed propositionally without
changing its independent semantic interpretation. -/
theorem RestoredExprTranslation.reindex
    {input output : Expr} {source target : VExpr}
    {Hreplace Hreplace' : ExprReplacement concreteReplace input output}
    (H : RestoredExprTranslation concreteReplace abstractReplace
      sourceEnv targetEnv Us sourceContext targetContext
      (source := source) (target := target) Hreplace)
    (h : Hreplace = Hreplace') :
    RestoredExprTranslation concreteReplace abstractReplace
      sourceEnv targetEnv Us sourceContext targetContext
      (source := source) (target := target) Hreplace' := by
  cases h
  exact H

end VerifyInductive
end Lean4Lean
