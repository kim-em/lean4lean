import Lean4Lean.Theory.Typing.AnchoredOriginalRichOccurrenceTraversal

/-! The finite native query graph carries actual semantic source frames.
Every native child is visited, including projection metadata beneath fresh
binders. Legacy observers are retained whole at the frontier: this graph does
not claim to factor their internal unindexed syntax. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Both realizations have the exact original root substitution as their tail.
This is a source equality, retained before any semantic alignment is made. -/
structure RichSourceTail
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context expression assigned}
    (location : Located root node) (σ τ rootLeft rootRight : Subst) : Prop where
  left : Subst.lift_l (.skipN .refl location.binderPrefix.length) σ = rootLeft
  right : Subst.lift_l (.skipN .refl location.binderPrefix.length) τ = rootRight

theorem RichSourceTail.at
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context expression assigned}
    {child : EndpointState sourceEnv U childContext childExpression childAssigned}
    {location : Located root node} {childLocation : Located root child}
    (tail : RichSourceTail location σ τ rootLeft rootRight)
    (depth : childLocation.binderPrefix.length = location.binderPrefix.length) :
    RichSourceTail childLocation σ τ rootLeft rootRight := by
  constructor
  · simpa only [depth] using tail.left
  · simpa only [depth] using tail.right

theorem RichSourceTail.route
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {first : EndpointState sourceEnv U context expression assigned}
    {last : EndpointState sourceEnv U context expression natural}
    {location : Located root first}
    (tail : RichSourceTail location σ τ rootLeft rootRight)
    (route : PrefixRoute sourceEnv U context expression first last) :
    RichSourceTail (route.locate location) σ τ rootLeft rootRight := by
  constructor
  · simpa only [route.locate_binderPrefix] using tail.left
  · simpa only [route.locate_binderPrefix] using tail.right

theorem RichSourceTail.push
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context expression assigned}
    {child : EndpointState sourceEnv U childContext childExpression childAssigned}
    {location : Located root node} {childLocation : Located root child}
    (tail : RichSourceTail location σ τ rootLeft rootRight)
    (depth : childLocation.binderPrefix.length = location.binderPrefix.length + 1)
    (left right : VExpr) :
    RichSourceTail childLocation (σ.cons left) (τ.cons right) rootLeft rootRight := by
  constructor
  · rw [depth]; exact capture_tail_cons _ _ _ _ tail.left
  · rw [depth]; exact capture_tail_cons _ _ _ _ tail.right

structure RichQueryOccurrence
    (root : EndpointRef sourceEnv U source rootExpression rootType)
    (initialContext : ContextDerivation sourceEnv U source)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (ordered : sourceEnv.Ordered) (initialEnvironment : List Closure) (rootLeft rootRight : Subst) where
  context : List VExpr
  expression : VExpr
  assigned : VExpr
  node : EndpointState sourceEnv U context expression assigned
  location : Located root node
  locals : List Nat
  left : Subst
  right : Subst
  available : Valuation
  occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals left right available
    ordered initialEnvironment
  sourceTail : RichSourceTail location left right rootLeft rootRight
  closed : available.AtomClosed
  rank : Nat
  profile : Profile rank
  footprint : Footprint
  query : RichObs sourceEnv env U registry target node locals left profile footprint
  resources : footprint.Available available
  metadata : Bool

noncomputable def RichQueryOccurrence.ofQuery
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {context : List VExpr} {expression assigned : VExpr}
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {n : Nat} {profile : Profile n} {footprint : Footprint}
    {node : EndpointState sourceEnv U context expression assigned}
    {location : Located root node}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (closed : available.AtomClosed)
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (resources : footprint.Available available) (metadata : Bool)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight) :
    RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight :=
  ⟨context, expression, assigned, node, location, locals, σ, τ, available, occurrence, sourceTail, closed,
    _, profile, footprint, query, resources, metadata⟩

theorem RichQueryOccurrence.cost_le
    (entry : RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight) :
    (Closure.close (entry.node.dependencyOrigin ordered)
      (entry.occurrence.frame.dependencyEnvironment ordered)).cost ≤
      (Closure.close (root.dependencyOrigin ordered) initialEnvironment).cost :=
  entry.occurrence.cost_le

/-- Newly required earlier-slot queries are discovered in this actual output
certificate, not manufactured from its target support profile. -/
noncomputable def RichQueryOccurrence.assignedQuery
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (entry : RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight)
    (value : RichBinderValue sourceEnv env U registry target entry.node entry.locals entry.left entry.right
      entry.available entry.profile) :
    RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight :=
  .ofQuery entry.occurrence.assignedFormation entry.closed (.code value.certificate)
    value.resources true (entry.sourceTail.at rfl)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
