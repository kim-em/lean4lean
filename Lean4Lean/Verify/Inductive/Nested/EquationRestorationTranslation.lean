import Lean4Lean.Verify.Inductive.Nested.EquationRestoration
import Lean4Lean.Verify.Typing.CheckedProjectionExpr
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
    (abstractReplace : VExpr → VExpr → Prop)
    (sourceEnv targetEnv : VEnv) (Us : List Name)
    (sourceContext targetContext : VLCtx)
    {input output : Expr} {source target : VExpr}
    (Hhit : concreteReplace input = some output) : Prop where
  sourceTranslation :
    CheckedTrExprS sourceEnv Us sourceContext input source
  targetTranslation :
    CheckedTrExprS targetEnv Us targetContext output target
  abstractHit : abstractReplace source target

/-- Structural alignment of a concrete replacement trace with its abstract
counterpart.  Every hit must be justified by an exact node interpretation;
all other constructors recurse in lockstep.  The generated equations use only
this common kernel-expression fragment, so erased metadata, lets, literals,
and projections are deliberately not admitted as unexplained alignment cases.
-/
inductive ExprRestorationAlignment
    (concreteReplace : Expr → Option Expr)
    (abstractReplace : VExpr → VExpr → Prop)
    (sourceEnv targetEnv : VEnv) (Us : List Name) :
    (sourceContext targetContext : VLCtx) →
    {input output : Expr} → {source target : VExpr} →
    ExprReplacement concreteReplace input output →
    VExprRestoration abstractReplace source target → Prop
  | hit
      (H : RestoredNodeInterpretation concreteReplace abstractReplace
        sourceEnv targetEnv Us sourceContext targetContext Hhit) :
      ExprRestorationAlignment concreteReplace abstractReplace sourceEnv
        targetEnv Us sourceContext targetContext
        (ExprReplacement.hit Hhit) (.hit H.abstractHit)
  | bvar (hconcrete : concreteReplace (.bvar i) = none) :
      ExprRestorationAlignment concreteReplace abstractReplace sourceEnv
        targetEnv Us sourceContext targetContext
        (.bvar hconcrete) (.bvar)
  | fvar (hconcrete : concreteReplace (.fvar fvarId) = none) :
      ExprRestorationAlignment concreteReplace abstractReplace sourceEnv
        targetEnv Us sourceContext targetContext
        (.fvar hconcrete) (.leaf)
  | sort (hconcrete : concreteReplace (.sort level) = none) :
      ExprRestorationAlignment concreteReplace abstractReplace sourceEnv
        targetEnv Us sourceContext targetContext
        (.sort hconcrete) (.sort)
  | const (hconcrete : concreteReplace (.const name levels) = none) :
      ExprRestorationAlignment concreteReplace abstractReplace sourceEnv
        targetEnv Us sourceContext targetContext
        (.const hconcrete) (.const)
  | lit (hconcrete : concreteReplace (.lit literal) = none) :
      ExprRestorationAlignment concreteReplace abstractReplace sourceEnv
        targetEnv Us sourceContext targetContext
        (.lit hconcrete) (.leaf)
  | app (hconcrete : concreteReplace (.app fn arg) = none)
      (hfn : ExprRestorationAlignment concreteReplace abstractReplace
        sourceEnv targetEnv Us sourceContext targetContext
        (source := sourceFn) (target := targetFn)
        concreteFn abstractFn)
      (harg : ExprRestorationAlignment concreteReplace abstractReplace
        sourceEnv targetEnv Us sourceContext targetContext
        (source := sourceArg) (target := targetArg)
        concreteArg abstractArg) :
      ExprRestorationAlignment concreteReplace abstractReplace sourceEnv
        targetEnv Us sourceContext targetContext
        (.app hconcrete concreteFn concreteArg)
        (.app abstractFn abstractArg)
  | lam
      (hconcrete : concreteReplace (.lam name domain body bi) = none)
      (hdomain : ExprRestorationAlignment concreteReplace abstractReplace
        sourceEnv targetEnv Us sourceContext targetContext
        (source := sourceDomain) (target := targetDomain)
        concreteDomain abstractDomain)
      (hbody : ExprRestorationAlignment concreteReplace abstractReplace
        sourceEnv targetEnv Us
          ((none, .vlam sourceDomain) :: sourceContext)
          ((none, .vlam targetDomain) :: targetContext)
        (source := sourceBody) (target := targetBody)
        concreteBody abstractBody) :
      ExprRestorationAlignment concreteReplace abstractReplace sourceEnv
        targetEnv Us sourceContext targetContext
        (.lam hconcrete concreteDomain concreteBody)
        (.lam abstractDomain abstractBody)
  | forallE
      (hconcrete : concreteReplace (.forallE name domain body bi) = none)
      (hdomain : ExprRestorationAlignment concreteReplace abstractReplace
        sourceEnv targetEnv Us sourceContext targetContext
        (source := sourceDomain) (target := targetDomain)
        concreteDomain abstractDomain)
      (hbody : ExprRestorationAlignment concreteReplace abstractReplace
        sourceEnv targetEnv Us
          ((none, .vlam sourceDomain) :: sourceContext)
          ((none, .vlam targetDomain) :: targetContext)
        (source := sourceBody) (target := targetBody)
        concreteBody abstractBody) :
      ExprRestorationAlignment concreteReplace abstractReplace sourceEnv
        targetEnv Us sourceContext targetContext
        (.forallE hconcrete concreteDomain concreteBody)
        (.forallE abstractDomain abstractBody)
  | mdata
      (hconcrete : concreteReplace (.mdata data body) = none)
      (hbody : ExprRestorationAlignment concreteReplace abstractReplace
        sourceEnv targetEnv Us sourceContext targetContext
        (source := sourceBody) (target := targetBody)
        concreteBody abstractBody) :
      ExprRestorationAlignment concreteReplace abstractReplace sourceEnv
        targetEnv Us sourceContext targetContext
        (.mdata hconcrete concreteBody) abstractBody
  | letE
      (hconcrete : concreteReplace
        (.letE name type value body nondep) = none)
      (htype : ExprRestorationAlignment concreteReplace abstractReplace
        sourceEnv targetEnv Us sourceContext targetContext
        (source := sourceType) (target := targetType)
        concreteType abstractType)
      (hvalue : ExprRestorationAlignment concreteReplace abstractReplace
        sourceEnv targetEnv Us sourceContext targetContext
        (source := sourceValue) (target := targetValue)
        concreteValue abstractValue)
      (hbody : ExprRestorationAlignment concreteReplace abstractReplace
        sourceEnv targetEnv Us
          ((none, .vlet sourceType sourceValue) :: sourceContext)
          ((none, .vlet targetType targetValue) :: targetContext)
        (source := sourceBody) (target := targetBody)
        concreteBody abstractBody) :
      ExprRestorationAlignment concreteReplace abstractReplace sourceEnv
        targetEnv Us sourceContext targetContext
        (.letE hconcrete concreteType concreteValue concreteBody) abstractBody
  | proj
      (hconcrete : concreteReplace (.proj structName index major) = none)
      (sourceMajorTranslation : CheckedTrExprS sourceEnv Us sourceContext
        major sourceMajor)
      (sourceProjection : CheckedTrProj sourceEnv Us.length
        sourceContext.toCtx structName index sourceMajor sourceTarget)
      (targetMajorTranslation : CheckedTrExprS targetEnv Us targetContext
        restoredMajor targetMajor)
      (targetProjection : CheckedTrProj targetEnv Us.length
        targetContext.toCtx structName index targetMajor targetTarget)
      (hmajor : ExprRestorationAlignment concreteReplace abstractReplace
        sourceEnv targetEnv Us sourceContext targetContext
        (source := sourceMajor) (target := targetMajor)
        concreteMajor abstractMajor) :
      ExprRestorationAlignment concreteReplace abstractReplace sourceEnv
        targetEnv Us sourceContext targetContext
        (.proj hconcrete concreteMajor)
        (.projection sourceProjection.supportExpansion
          targetProjection.supportExpansion
          sourceProjection.target_bvarHead?_eq_none abstractMajor)

/-- An abstract restoration interpreting one exact executable replacement
trace.  The executable trace fixes which concrete expressions are related but
does not supply any semantic field: both endpoint translations and the
structural abstract restoration must be proved independently. -/
structure RestoredExprTranslation
    (concreteReplace : Expr → Option Expr)
    (abstractReplace : VExpr → VExpr → Prop)
    (sourceEnv targetEnv : VEnv) (Us : List Name)
    (sourceContext targetContext : VLCtx)
    {input output : Expr} {source target : VExpr}
    (Hreplace : ExprReplacement concreteReplace input output) : Prop where
  sourceTranslation :
    CheckedTrExprS sourceEnv Us sourceContext input source
  targetTranslation :
    CheckedTrExprS targetEnv Us targetContext output target
  abstractRestoration : VExprRestoration abstractReplace source target
  alignment : ExprRestorationAlignment concreteReplace abstractReplace
    sourceEnv targetEnv Us sourceContext targetContext Hreplace
      abstractRestoration

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
