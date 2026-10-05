import Lean4Lean.Theory.Typing.AnchoredOriginalFactorCut
import Lean4Lean.Theory.Typing.AnchoredNativePrefixFits

/-! Context provenance for actual inverse-substitution locations. The
argument side keeps its ORIGINAL view and an explicit source weakening;
only raw soundness is weakened, never a recursively interpreted smaller
argument proof. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

private def viewExpression (_ : TypingView env U source expression type) : VExpr := expression

def Located.binderPrefix
    {root : TypingView env U rootSource rootExpression rootType}
    {selected : TypingView env U context expression type}
    (location : Located root selected) : List VExpr :=
  match location with
  | .here => []
  | .appFunction parent => parent.binderPrefix
  | .appArgument parent => parent.binderPrefix
  | .lamDomain parent => parent.binderPrefix
  | .lamBody (domain := domain) parent => viewExpression domain :: parent.binderPrefix
  | .piDomain parent => parent.binderPrefix
  | .piBody (domain := domain) parent => viewExpression domain :: parent.binderPrefix

theorem Located.context_eq
    {root : TypingView env U rootSource rootExpression rootType}
    {selected : TypingView env U context expression type}
    (location : Located root selected) : context = location.binderPrefix ++ rootSource := by
  induction location with
  | here => rfl
  | appFunction _ ih | appArgument _ ih | lamDomain _ ih | piDomain _ ih => exact ih
  | lamBody _ ih | piBody _ ih => simpa only [binderPrefix, viewExpression, List.cons_append] using congrArg (List.cons _) ih

/-- `baseDepth` belongs to the root call. Binder traversal changes the
location prefix; removing a BinderPack layer changes the ledger depth but
must leave this absolute origin-depth equation intact. -/
structure ContextualCutOrigin (root : TypingView env U source e A)
    (argument : VExpr) (baseDepth : Nat := 0) extends CutOrigin root argument where
  depth_eq : depth = baseDepth + location.binderPrefix.length

/-- A display keeps the original derivation at its original source context.
The caller's common context and expression are reached only by the retained
prefix weakening. The assigned type is deliberately not identified with
that of another display of the same expression. -/
structure SourceWeakeningDisplay (env : VEnv) (U : Nat)
    (context : List VExpr) (expression : VExpr) where
  source : List VExpr
  term : VExpr
  type : VExpr
  original : TypingView env U source term type
  binders : List VExpr
  context_eq : context = binders ++ source
  expression_eq : expression = term.lift' (.skipN .refl binders.length)

def SourceWeakeningDisplay.displayedType
    (display : SourceWeakeningDisplay env U context expression) : VExpr :=
  display.type.lift' (.skipN .refl display.binders.length)

/-- Raw weakening is permitted for soundness. The closure still stores and
charges `display.original`; this theorem is not a new recursive argument. -/
theorem SourceWeakeningDisplay.sound (henv : env.Ordered)
    (display : SourceWeakeningDisplay env U context expression) :
    env.IsDefEqStrong U context expression expression display.displayedType := by
  rcases display with ⟨source, term, type, original, binders, rfl, rfl⟩
  simpa only [displayedType, ← lift'_consN_skipN, Lift.consN] using
    original.original.weakN henv (Ctx.LiftN.zero binders)

/-- Realization of the common displayed expression uses the restriction of
the caller's substitution to the ORIGINAL source context. -/
theorem SourceWeakeningDisplay.realize
    (display : SourceWeakeningDisplay env U context expression) (σ : Subst) :
    expression.subst σ = display.term.subst
      (Subst.lift_l (.skipN .refl display.binders.length) σ) := by
  exact (congrArg (fun e => e.subst σ) display.expression_eq).trans subst_lift'

theorem SourceWeakeningDisplay.originalSubstitution
    (display : SourceWeakeningDisplay env U context expression)
    (raw : Ctx.SubstEq env U target σ τ context) :
    Ctx.SubstEq env U target
      (Subst.lift_l (.skipN .refl display.binders.length) σ)
      (Subst.lift_l (.skipN .refl display.binders.length) τ) display.source := by
  have prefixed : Ctx.SubstEq env U target σ τ (display.binders ++ display.source) :=
    display.context_eq ▸ raw
  exact Ctx.SubstEq.nativePrefix prefixed

def SourceWeakeningDisplay.cost
    (display : SourceWeakeningDisplay env U context expression) (environment : List Closure) : Nat :=
  (Closure.close display.original.origin environment).cost

def SourceWeakeningDisplay.self {assigned : VExpr} (view : TypingView env U context expression assigned) :
    SourceWeakeningDisplay env U context expression where
  source := context
  term := expression
  type := assigned
  original := view
  binders := []
  context_eq := rfl
  expression_eq := by simp

/-- The argument's ORIGINAL view aligns with the actual cut at the common
context. No source reflection or equality of assigned types is assumed. -/
def ContextualCutOrigin.argumentDisplay
    {root : TypingView env U source e A}
    (cut : ContextualCutOrigin root argument)
    (argumentView : TypingView env U source argument argumentType) :
    SourceWeakeningDisplay env U cut.context cut.expression where
  source := source
  term := argument
  type := argumentType
  original := argumentView
  binders := cut.location.binderPrefix
  context_eq := cut.location.context_eq
  expression_eq := by
    simpa only [cut.depth_eq, Nat.zero_add] using cut.expression_eq

/-- Both actual typings are displayed in the SAME source context at the
SAME literal expression, while their original assigned types remain distinct. -/
theorem ContextualCutOrigin.comparisonSound
    (henv : env.Ordered) {root : TypingView env U source e A}
    (cut : ContextualCutOrigin root argument)
    (argumentView : TypingView env U source argument argumentType) :
    env.IsDefEqStrong U cut.context cut.expression cut.expression cut.type ∧
    env.IsDefEqStrong U cut.context cut.expression cut.expression
      (argumentType.lift' (.skipN .refl cut.location.binderPrefix.length)) :=
  ⟨cut.toCutOrigin.original, (cut.argumentDisplay argumentView).sound henv⟩

/-- The actual cut/argument comparison charges the TWO ORIGINAL views.
The cut side retains the actual path environment, including every ORIGINAL
binder-domain formation. The argument side keeps its base captured environment;
its explicit source weakening never becomes a newly synthesized original proof. -/
theorem ContextualCutOrigin.app_comparison_schedule
    (domainWF : u.WF U) (bodyWF : v.WF U)
    (domain : TypingView env U source A (.sort u))
    (codomain : TypingView env U (A :: source) B (.sort v))
    (function : TypingView env U source f (.forallE A B))
    (argumentView : TypingView env U source argument A)
    (result : TypingView env U source (B.inst argument) (.sort v))
    (cut : ContextualCutOrigin result argument) (environment : List Closure) :
    schedule .coherence
      ((SourceWeakeningDisplay.self cut.view).cost (cut.location.environment environment) +
        (cut.argumentDisplay argumentView).cost environment) <
      schedule .fundamental
        ((Closure.close (TypingView.app domainWF bodyWF domain codomain function argumentView result).origin
          environment).cost) :=
  app_cut_schedule domainWF bodyWF domain codomain function argumentView result cut.toCutOrigin environment

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
