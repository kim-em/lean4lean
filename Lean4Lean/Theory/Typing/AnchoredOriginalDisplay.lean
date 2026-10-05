import Lean4Lean.Theory.Typing.AnchoredOriginalQueryCompatibility

/-! Delayed source weakening of an original endpoint closure. The displayed
expression and type may live under extra binders, while recursive calls keep
the original endpoint and its captured context. Raw weakening is used only
for soundness; it is never reified as a new original derivation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

/-- A display is backed by an actual original occurrence and its captured
formation spine. Raw typing alone cannot manufacture this provenance. -/
structure EndpointProvenance
    (context : ContextDerivation env U source)
    (node : EndpointState env U source expression type) where
  rootSource : List VExpr
  rootExpression : VExpr
  rootType : VExpr
  root : EndpointRef env U rootSource rootExpression rootType
  initial : ContextDerivation env U rootSource
  location : Located root node
  context_eq : context = location.contextDerivation initial

noncomputable def EndpointProvenance.ofLocation
    {rootSource : List VExpr} {rootExpression rootType : VExpr}
    {root : EndpointRef env U rootSource rootExpression rootType}
    {node : EndpointState env U source expression type}
    (location : Located root node) (initial : ContextDerivation env U rootSource) :
    EndpointProvenance (location.contextDerivation initial) node :=
  ⟨rootSource, rootExpression, rootType, root, initial, location, rfl⟩

structure EndpointDisplay (env : VEnv) (U : Nat)
    (displayedContext : List VExpr) (expression type : VExpr) where
  source : List VExpr
  sourceExpression : VExpr
  sourceType : VExpr
  context : ContextDerivation env U source
  node : EndpointState env U source sourceExpression sourceType
  provenance : EndpointProvenance context node
  map : Lift
  insertion : Ctx.Lift' map source displayedContext
  expression_eq : expression = sourceExpression.lift' map
  type_eq : type = sourceType.lift' map

def EndpointDisplay.cost (display : EndpointDisplay env U Γ e A) : Nat :=
  (Closure.close display.node.origin display.context.closures).cost

theorem EndpointDisplay.sound (henv : env.Ordered)
    (display : EndpointDisplay env U Γ e A) :
    env.HasType U Γ e A := by
  simpa only [HasType, ← display.expression_eq, ← display.type_eq] using
    display.node.sound.defeq.weak' henv display.insertion

def EndpointDisplay.identity (context : ContextDerivation env U Γ)
    (node : EndpointState env U Γ e A) (provenance : EndpointProvenance context node) :
    EndpointDisplay env U Γ e A :=
  ⟨Γ, e, A, context, node, provenance, .refl, .refl, by simp, by simp⟩

/-- Composing a display never changes the original closure or its cost. -/
def EndpointDisplay.weaken (display : EndpointDisplay env U Γ e A)
    (insertion : Ctx.Lift' ρ Γ Δ) :
    EndpointDisplay env U Δ (e.lift' ρ) (A.lift' ρ) where
  source := display.source
  sourceExpression := display.sourceExpression
  sourceType := display.sourceType
  context := display.context
  node := display.node
  provenance := display.provenance
  map := .comp display.map ρ
  insertion := display.insertion.comp insertion
  expression_eq := by simpa only [lift'_comp] using congrArg (·.lift' ρ) display.expression_eq
  type_eq := by simpa only [lift'_comp] using congrArg (·.lift' ρ) display.type_eq

theorem EndpointDisplay.weaken_cost
    (display : EndpointDisplay env U Γ e A)
    (insertion : Ctx.Lift' ρ Γ Δ) :
    (display.weaken insertion).cost = display.cost := rfl

/-- The cut endpoint keeps the exact context reconstructed along its own
original path, including each binder's original domain formation. -/
noncomputable def CutOriginAt.sourceDisplay
    {root : EndpointRef env U source rootExpression rootType}
    (cut : CutOriginAt root boundary argument baseDepth)
    (context : ContextDerivation env U source) :
    EndpointDisplay env U cut.context cut.expression cut.type :=
  .identity (cut.location.contextDerivation context) cut.view (.ofLocation cut.location context)

theorem CutOriginAt.sourceDisplay_cost
    {root : EndpointRef env U source rootExpression rootType}
    (cut : CutOriginAt root boundary argument baseDepth)
    (context : ContextDerivation env U source) :
    (cut.sourceDisplay context).cost =
      (Closure.close cut.view.origin (cut.location.environment context.closures)).cost := by
  change (Closure.close cut.view.origin (cut.location.contextDerivation context).closures).cost = _
  rw [cut.location.contextDerivation_closures]

/-- The original argument displayed at an actual whole cut. The assigned
type of the cut need not be a weakening; only the comparison's destination
is constructed this way. -/
def CutOriginAt.argumentDisplay
    {root : EndpointRef env U source rootExpression rootType}
    (cut : CutOriginAt root boundary argument 0)
    (context : ContextDerivation env U (boundary ++ source))
    (node : EndpointState env U (boundary ++ source) argument argumentType)
    (provenance : EndpointProvenance context node) :
    EndpointDisplay env U cut.context cut.expression
      (argumentType.lift' (.skipN .refl cut.depth)) where
  source := boundary ++ source
  sourceExpression := argument
  sourceType := argumentType
  context := context
  node := node
  provenance := provenance
  map := .skipN .refl cut.depth
  insertion := by
    rw [cut.context_eq, cut.depth_eq, Nat.zero_add]
    exact Ctx.liftN_iff_lift'.mp (.zero cut.innerPrefix)
  expression_eq := cut.expression_eq
  type_eq := rfl

theorem CutOriginAt.argumentDisplay_cost
    {root : EndpointRef env U source rootExpression rootType}
    (cut : CutOriginAt root boundary argument 0)
    (context : ContextDerivation env U (boundary ++ source))
    (node : EndpointState env U (boundary ++ source) argument argumentType)
    (provenance : EndpointProvenance context node) :
    (cut.argumentDisplay context node provenance).cost =
      (Closure.close node.origin context.closures).cost := rfl

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
