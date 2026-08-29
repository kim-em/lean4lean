import Lean4Lean.Verify.Inductive.Nested.EquationRestorationTranslation
import Lean4Lean.Verify.Typing.CheckedProjectionExpr

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The three production branches which can stop `restoreNestedNode` before
structural traversal.  Family and constructor cases retain the exact map
lookup which classified the hit; the callback equation fixes the complete
replacement expression. -/
inductive NestedRestoreHitProvenance
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (params : Array Expr) (auxRec : NameMap Name) :
    Expr → Expr → Prop
  | recursor (hfind : auxRec.find? oldName = some newName) :
      NestedRestoreHitProvenance result env params auxRec
        (.const oldName levels) (.const newName levels)
  | family
      (hfind : result.aux2nested.find? familyName = some nested)
      (hhead : input.getAppFn = .const familyName levels)
      (hhit : result.restoreNestedNode env params auxRec input = some output) :
      NestedRestoreHitProvenance result env params auxRec input output
  | constructor
      (hfind : result.getNestedIfAuxCtor env constructorName =
        some (nested, auxiliaryFamily))
      (hhead : input.getAppFn = .const constructorName levels)
      (hhit : result.restoreNestedNode env params auxRec input = some output) :
      NestedRestoreHitProvenance result env params auxRec input output

theorem NestedRestoreHitProvenance.concreteHit
    (H : NestedRestoreHitProvenance result env params auxRec input output) :
    result.restoreNestedNode env params auxRec input = some output := by
  cases H with
  | recursor hfind =>
      exact restoreNestedNode_recursor result env params auxRec _ _ _ hfind
  | family _ _ hhit | constructor _ _ hhit => exact hhit

/-- Every successful executable restoration callback is classified by the
same three branches which implement `restoreNestedNode`.  In particular,
hit provenance is reconstructed from the actual callback result rather than
being supplied by a declaration-boundary proof package. -/
theorem NestedRestoreHitProvenance.ofConcreteHit
    (hhit : result.restoreNestedNode env params auxRec input = some output) :
    NestedRestoreHitProvenance result env params auxRec input output := by
  by_cases hrec : ∃ oldName levels newName,
      input = .const oldName levels ∧ auxRec.find? oldName = some newName
  · rcases hrec with ⟨oldName, levels, newName, rfl, hfind⟩
    have houtput : output = .const newName levels := by
      simpa [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode,
        hfind] using hhit.symm
    subst output
    exact .recursor hfind
  · have hrecNone : ∀ oldName levels,
        input = .const oldName levels → auxRec.find? oldName = none := by
      intro oldName levels hinput
      cases hfind : auxRec.find? oldName with
      | none => rfl
      | some newName =>
          exact False.elim (hrec ⟨oldName, levels, newName, hinput, hfind⟩)
    generalize hhead : input.getAppFn = head
    cases head <;> try {
        exfalso
        cases input <;>
          simp_all [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode] }
    case const familyName familyLevels =>
      cases hfamily : result.aux2nested.find? familyName with
      | some nested => exact .family hfamily hhead hhit
      | none =>
          cases hconstructor : result.getNestedIfAuxCtor env familyName with
          | some constructorData =>
              rcases constructorData with ⟨nested, auxiliaryFamily⟩
              exact .constructor hconstructor hhead hhit
          | none =>
              exfalso
              cases input <;>
                simp_all [
                  Lean4Lean.ElimNestedInductive.Result.restoreNestedNode]

/-- A restoration hit interpreted at the local contexts in which it actually
occurs.  Recursive traversal changes these contexts below binders, so they
must not be fixed by a root-level finite plan.  Every witness is derived from
the concrete callback result and the checked translations of its two literal
endpoints. -/
def ContextualNestedRestoreHit
    (result : Lean4Lean.ElimNestedInductive.Result)
    (prodEnv : Environment) (params : Array Expr) (auxRec : NameMap Name)
    (sourceEnv targetEnv : VEnv) (Us : List Name)
    (source target : VExpr) : Prop :=
  ∃ sourceContext targetContext input output,
    NestedRestoreHitProvenance result prodEnv params auxRec input output ∧
      CheckedTrExprS sourceEnv Us sourceContext input source ∧
      CheckedTrExprS targetEnv Us targetContext output target

/-- A context-indexed semantic trace of one exact executable restoration.
Unlike the former root-context node list, the binder constructors change the
two local contexts in their indices.  Variable and let cases retain their
actual checked translations, so the trace does not assume that independently
restored contexts are syntactically identical. -/
inductive ContextualExprRestoration
    (result : Lean4Lean.ElimNestedInductive.Result)
    (prodEnv : Environment) (params : Array Expr) (auxRec : NameMap Name)
    (sourceEnv targetEnv : VEnv) (Us : List Name) :
    (sourceContext targetContext : VLCtx) →
    {input output : Expr} → {source target : VExpr} →
    ExprReplacement (result.restoreNestedNode prodEnv params auxRec)
      input output → Prop
  | hit
      (Hsource : CheckedTrExprS sourceEnv Us sourceContext input source)
      (Htarget : CheckedTrExprS targetEnv Us targetContext output target) :
      ContextualExprRestoration result prodEnv params auxRec sourceEnv
        targetEnv Us sourceContext targetContext
        (.hit hhit)
  | bvar
      (Hsource : CheckedTrExprS sourceEnv Us sourceContext (.bvar index)
        source)
      (Htarget : CheckedTrExprS targetEnv Us targetContext (.bvar index)
        target) :
      ContextualExprRestoration result prodEnv params auxRec sourceEnv
        targetEnv Us sourceContext targetContext (.bvar hnone)
  | fvar
      (Hsource : CheckedTrExprS sourceEnv Us sourceContext (.fvar fvarId)
        source)
      (Htarget : CheckedTrExprS targetEnv Us targetContext (.fvar fvarId)
        target) :
      ContextualExprRestoration result prodEnv params auxRec sourceEnv
        targetEnv Us sourceContext targetContext (.fvar hnone)
  | sort
      (Hsource : CheckedTrExprS sourceEnv Us sourceContext (.sort level)
        source)
      (Htarget : CheckedTrExprS targetEnv Us targetContext (.sort level)
        target) :
      ContextualExprRestoration result prodEnv params auxRec sourceEnv
        targetEnv Us sourceContext targetContext (.sort hnone)
  | const
      (Hsource : CheckedTrExprS sourceEnv Us sourceContext
        (.const name levels) source)
      (Htarget : CheckedTrExprS targetEnv Us targetContext
        (.const name levels) target) :
      ContextualExprRestoration result prodEnv params auxRec sourceEnv
        targetEnv Us sourceContext targetContext (.const hnone)
  | app
      (Hfn : ContextualExprRestoration result prodEnv params auxRec sourceEnv
        targetEnv Us sourceContext targetContext
        (source := sourceFn) (target := targetFn) fnTrace)
      (Harg : ContextualExprRestoration result prodEnv params auxRec sourceEnv
        targetEnv Us sourceContext targetContext
        (source := sourceArg) (target := targetArg) argTrace) :
      ContextualExprRestoration result prodEnv params auxRec sourceEnv
        targetEnv Us sourceContext targetContext
        (source := .app sourceFn sourceArg) (target := .app targetFn targetArg)
        (.app hnone fnTrace argTrace)
  | lam
      (Hdomain : ContextualExprRestoration result prodEnv params auxRec
        sourceEnv targetEnv Us sourceContext targetContext
        (source := sourceDomain) (target := targetDomain) domainTrace)
      (Hbody : ContextualExprRestoration result prodEnv params auxRec
        sourceEnv targetEnv Us
        ((none, .vlam sourceDomain) :: sourceContext)
        ((none, .vlam targetDomain) :: targetContext)
        (source := sourceBody) (target := targetBody) bodyTrace) :
      ContextualExprRestoration result prodEnv params auxRec sourceEnv
        targetEnv Us sourceContext targetContext
        (source := .lam sourceDomain sourceBody)
        (target := .lam targetDomain targetBody)
        (.lam hnone domainTrace bodyTrace)
  | forallE
      (Hdomain : ContextualExprRestoration result prodEnv params auxRec
        sourceEnv targetEnv Us sourceContext targetContext
        (source := sourceDomain) (target := targetDomain) domainTrace)
      (Hbody : ContextualExprRestoration result prodEnv params auxRec
        sourceEnv targetEnv Us
        ((none, .vlam sourceDomain) :: sourceContext)
        ((none, .vlam targetDomain) :: targetContext)
        (source := sourceBody) (target := targetBody) bodyTrace) :
      ContextualExprRestoration result prodEnv params auxRec sourceEnv
        targetEnv Us sourceContext targetContext
        (source := .forallE sourceDomain sourceBody)
        (target := .forallE targetDomain targetBody)
        (.forallE hnone domainTrace bodyTrace)
  | letE
      (Htype : ContextualExprRestoration result prodEnv params auxRec
        sourceEnv targetEnv Us sourceContext targetContext
        (source := sourceType) (target := targetType) typeTrace)
      (Hvalue : ContextualExprRestoration result prodEnv params auxRec
        sourceEnv targetEnv Us sourceContext targetContext
        (source := sourceValue) (target := targetValue) valueTrace)
      (Hbody : ContextualExprRestoration result prodEnv params auxRec
        sourceEnv targetEnv Us
        ((none, .vlet sourceType sourceValue) :: sourceContext)
        ((none, .vlet targetType targetValue) :: targetContext)
        (source := sourceBody) (target := targetBody) bodyTrace) :
      ContextualExprRestoration result prodEnv params auxRec sourceEnv
        targetEnv Us sourceContext targetContext
        (source := sourceBody) (target := targetBody)
        (.letE hnone typeTrace valueTrace bodyTrace)
  | lit
      (Hsource : CheckedTrExprS sourceEnv Us sourceContext (.lit literal)
        source)
      (Htarget : CheckedTrExprS targetEnv Us targetContext (.lit literal)
        target) :
      ContextualExprRestoration result prodEnv params auxRec sourceEnv
        targetEnv Us sourceContext targetContext (.lit hnone)
  | mdata
      (Hbody : ContextualExprRestoration result prodEnv params auxRec sourceEnv
        targetEnv Us sourceContext targetContext
        (source := source) (target := target) bodyTrace) :
      ContextualExprRestoration result prodEnv params auxRec sourceEnv
        targetEnv Us sourceContext targetContext
        (source := source) (target := target) (.mdata hnone bodyTrace)
  | proj
      (HsourceProjection : CheckedTrProj sourceEnv Us.length
        sourceContext.toCtx structName index sourceMajor source)
      (HtargetProjection : CheckedTrProj targetEnv Us.length
        targetContext.toCtx structName index targetMajor target)
      (Hmajor : ContextualExprRestoration result prodEnv params auxRec
        sourceEnv targetEnv Us sourceContext targetContext
        (source := sourceMajor) (target := targetMajor) majorTrace) :
      ContextualExprRestoration result prodEnv params auxRec sourceEnv
        targetEnv Us sourceContext targetContext
        (source := source) (target := target) (.proj hnone majorTrace)

/-- The context-indexed trace is constructed from the concrete replacement
and its certified endpoint translations, with no semantic callback. -/
theorem ExprReplacement.contextualTrace
    (Hreplace : ExprReplacement
      (result.restoreNestedNode prodEnv params auxRec) input output)
    (Hsource : CheckedTrExprS sourceEnv Us sourceContext input source)
    (Htarget : CheckedTrExprS targetEnv Us targetContext output target) :
    ContextualExprRestoration result prodEnv params auxRec sourceEnv targetEnv
      Us sourceContext targetContext (source := source) (target := target)
        Hreplace := by
  induction Hreplace generalizing sourceContext targetContext source target with
  | hit hhit => exact .hit (hhit := hhit) Hsource Htarget
  | bvar hnone => exact .bvar (hnone := hnone) Hsource Htarget
  | fvar hnone => exact .fvar (hnone := hnone) Hsource Htarget
  | mvar hnone => cases Hsource
  | sort hnone => exact .sort (hnone := hnone) Hsource Htarget
  | const hnone => exact .const (hnone := hnone) Hsource Htarget
  | lit hnone => exact .lit (hnone := hnone) Hsource Htarget
  | app hnone Hfn Harg ihFn ihArg =>
      cases Hsource with
      | app _ _ HsourceFn HsourceArg =>
        cases Htarget with
        | app _ _ HtargetFn HtargetArg =>
          exact .app (hnone := hnone) (ihFn HsourceFn HtargetFn)
            (ihArg HsourceArg HtargetArg)
  | lam hnone Hdomain Hbody ihDomain ihBody =>
      cases Hsource with
      | lam _ HsourceDomain HsourceBody =>
        cases Htarget with
        | lam _ HtargetDomain HtargetBody =>
          exact .lam (hnone := hnone)
            (ihDomain HsourceDomain HtargetDomain)
            (ihBody HsourceBody HtargetBody)
  | forallE hnone Hdomain Hbody ihDomain ihBody =>
      cases Hsource with
      | forallE _ _ HsourceDomain HsourceBody =>
        cases Htarget with
        | forallE _ _ HtargetDomain HtargetBody =>
          exact .forallE (hnone := hnone)
            (ihDomain HsourceDomain HtargetDomain)
            (ihBody HsourceBody HtargetBody)
  | letE hnone Htype Hvalue Hbody ihType ihValue ihBody =>
      cases Hsource with
      | letE _ HsourceType HsourceValue HsourceBody =>
        cases Htarget with
        | letE _ HtargetType HtargetValue HtargetBody =>
          exact .letE (hnone := hnone) (ihType HsourceType HtargetType)
            (ihValue HsourceValue HtargetValue)
            (ihBody HsourceBody HtargetBody)
  | mdata hnone Hbody ihBody =>
      cases Hsource with
      | mdata HsourceBody =>
        cases Htarget with
        | mdata HtargetBody =>
          exact ContextualExprRestoration.mdata (hnone := hnone)
            (ihBody HsourceBody HtargetBody)
  | proj hnone Hmajor ihMajor =>
      cases Hsource with
      | proj HsourceMajor HsourceProjection =>
        cases Htarget with
        | proj HtargetMajor HtargetProjection =>
          exact .proj (hnone := hnone) HsourceProjection HtargetProjection
            (ihMajor HsourceMajor HtargetMajor)

/-- One semantically interpreted production hit.  Its abstract endpoints are
not inferred from executable syntax: both must translate independently in the
environments relevant before and after restoration. -/
structure NestedRestoredNode
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (params : Array Expr) (auxRec : NameMap Name)
    (sourceEnv targetEnv : VEnv) (Us : List Name)
    (sourceContext targetContext : VLCtx) where
  input : Expr
  output : Expr
  source : VExpr
  target : VExpr
  provenance : NestedRestoreHitProvenance result env params auxRec input output
  sourceTranslation :
    CheckedTrExprS sourceEnv Us sourceContext input source
  targetTranslation :
    CheckedTrExprS targetEnv Us targetContext output target

/-- A finite semantic plan for the exact production hits in one restored
equation.  Functionality prevents the abstract replacement operation from
choosing different targets for the same independently translated source. -/
structure NestedRestorationPlan
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (params : Array Expr) (auxRec : NameMap Name)
    (sourceEnv targetEnv : VEnv) (Us : List Name)
    (sourceContext targetContext : VLCtx) where
  nodes : List (NestedRestoredNode result env params auxRec sourceEnv targetEnv
    Us sourceContext targetContext)

/-- Relational interpretation of the finite plan.  Literal membership keeps
each occurrence's independently checked target; no global syntactic
functionality property is required or assumed. -/
def NestedRestorationPlan.Relates
    (H : NestedRestorationPlan result env params auxRec sourceEnv targetEnv
      Us sourceContext targetContext) (source target : VExpr) : Prop :=
  ∃ node ∈ H.nodes, node.source = source ∧ node.target = target

theorem NestedRestorationPlan.restoreNode_of_mem
    (H : NestedRestorationPlan result env params auxRec sourceEnv targetEnv
      Us sourceContext targetContext) (node) (hnode : node ∈ H.nodes) :
    H.Relates node.source node.target :=
  ⟨node, hnode, rfl, rfl⟩

/-- Membership in a concrete provenance plan supplies the exact atomic hit
required by structural expression-restoration alignment. -/
theorem NestedRestorationPlan.interpret
    (H : NestedRestorationPlan result env params auxRec sourceEnv targetEnv
      Us sourceContext targetContext) (node) (hnode : node ∈ H.nodes) :
    RestoredNodeInterpretation
      (result.restoreNestedNode env params auxRec) H.Relates
      sourceEnv targetEnv Us sourceContext targetContext
      (source := node.source) (target := node.target)
      node.provenance.concreteHit where
  sourceTranslation := node.sourceTranslation
  targetTranslation := node.targetTranslation
  abstractHit := H.restoreNode_of_mem node hnode

end VerifyInductive
end Lean4Lean
