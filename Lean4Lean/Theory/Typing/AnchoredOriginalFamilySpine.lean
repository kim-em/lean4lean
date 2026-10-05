import Lean4Lean.Theory.Typing.AnchoredOriginalTypeFormation
import Lean4Lean.Theory.Typing.AnchoredOriginalEndpointFactor

/-! Ordered source arguments recovered from an actual original family-type
formation. Each argument keeps its own assigned type and an actual endpoint
path. These views do not identify that type with a declaration telescope
entry, and they do not depend on an observation query.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

/-- One original spine argument, with its assigned type kept intact. -/
structure SpineArgument (root : EndpointRef env U source expression type)
    (context : List VExpr) (binderTypes : List VExpr) (argument : VExpr) where
  type : VExpr
  node : EndpointState env U context argument type
  location : Located root node
  prefix_eq : location.binderPrefix = binderTypes

/-- An ordered finite list of actual argument origins. -/
inductive SpineArguments (root : EndpointRef env U source expression type)
    (context : List VExpr) (binderTypes : List VExpr) : List VExpr → Type where
  | nil : SpineArguments root context binderTypes []
  | cons (head : SpineArgument root context binderTypes argument)
      (tail : SpineArguments root context binderTypes arguments) :
      SpineArguments root context binderTypes (argument :: arguments)

noncomputable def SpineArguments.get (origins : SpineArguments root context binderTypes arguments)
    (index : Nat) (selected : arguments[index]? = some expression) :
    SpineArgument root context binderTypes expression := by
  induction origins generalizing index with
  | nil => simp at selected
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
      cases selected
      exact head
    | succ index => exact ih index selected

structure SpineView
    {node : EndpointState env U context (mkApps head arguments) type}
    (start : Located root node) where
  headType : VExpr
  headNode : EndpointState env U context head headType
  headLocation : Located root headNode
  prefix_eq : headLocation.binderPrefix = start.binderPrefix
  arguments : SpineArguments root context start.binderPrefix arguments

/-- Peel the concrete application spine using the bounded endpoint head
exposure. Every conversion retains its own path step. -/
noncomputable def spineView (arguments : List VExpr)
    {node : EndpointState env U context (mkApps head arguments) type}
    (start : Located root node) : SpineView start :=
  match arguments with
  | [] => ⟨_, node, start, rfl, .nil⟩
  | argument :: arguments =>
      let tail := spineView arguments (head := .app head argument) start
      let front := appView tail.headLocation
      ⟨_, front.function, .appFunction front.location,
        front.prefix_eq.trans tail.prefix_eq,
        .cons ⟨_, front.argument, .appArgument front.location,
          front.prefix_eq.trans tail.prefix_eq⟩ tail.arguments⟩

/-- A path with no binder step inherits exactly its root environment. -/
theorem Located.environment_eq_of_prefix_nil
    (location : Located root selected) (empty : location.binderPrefix = [])
    (initial : List Closure) : location.environment initial = initial := by
  induction location with
  | here => rfl
  | expose parent ih | convertTerm parent ih | appFunction parent ih | appArgument parent ih | appDomain parent ih | appResult parent ih | lamDomain parent ih | piDomain parent ih | projField parent ih | projMajor parent ih | assignedFormation parent ih | appPiFormation parent ih => exact ih empty
  | lamBody parent _ | lamCodomain parent _ | appCodomain parent _ | piBody parent _ => cases empty

theorem SpineArgument.sound
    {root : EndpointRef env U source rootExpression rootType}
    (argument : SpineArgument root context binderTypes expression) :
    env.IsDefEqStrong U context expression expression argument.type := argument.node.sound

theorem SpineArgument.cost_le (argument : SpineArgument root context [] expression)
    (initial : List Closure) :
    (Closure.close argument.node.origin initial).cost ≤
      (Closure.close root.origin initial).cost := by
  have bound := argument.location.cost_le initial
  simpa only [argument.location.environment_eq_of_prefix_nil argument.prefix_eq initial] using bound

/-- Recover the family arguments from the assigned-type formation leaf of
the given original source tree, before any projection demand is supplied. -/
noncomputable def familySpine
    (original : Derivation env U source left right (mkApps (.const name levels) arguments)) :
    SpineView (Located.here (root := original.familyFormationRef.reference)) :=
  spineView arguments .here

noncomputable def familyArgument
    (original : Derivation env U source left right (mkApps (.const name levels) arguments))
    (index : Nat) (selected : arguments[index]? = some expression) :
    SpineArgument original.familyFormationRef.reference source [] expression :=
  (familySpine original).arguments.get index selected

theorem familyArgument_cost_le
    (original : Derivation env U source left right (mkApps (.const name levels) arguments))
    (index : Nat) (selected : arguments[index]? = some expression) (initial : List Closure) :
    (Closure.close (familyArgument original index selected).node.origin initial).cost ≤
      (Closure.close original.origin initial).cost :=
  Nat.le_trans ((familyArgument original index selected).cost_le initial)
    (original.familyFormationRef.cost_le initial)

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
