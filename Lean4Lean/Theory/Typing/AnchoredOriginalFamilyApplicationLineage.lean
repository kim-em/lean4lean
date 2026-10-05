import Lean4Lean.Theory.Typing.AnchoredOriginalFamilySpine
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPrefix

/-! Argument discovery retains its enclosing original application, including
the actual expected domain and function typing. This is the source evidence
needed for declaration alignment; the argument's inferred type is never
identified with an earlier declaration domain by raw equality. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

structure SpineApplication
    (root : EndpointRef env U source expression type)
    (context : List VExpr) (binderTypes : List VExpr) (argument : VExpr) where
  functionExpression : VExpr
  assigned : VExpr
  node : EndpointState env U context (.app functionExpression argument) assigned
  start : Located root node
  prefix_eq : start.binderPrefix = binderTypes
  selected : ApplicationPrefix start

noncomputable abbrev SpineApplication.view (application : SpineApplication root context binderTypes expression) : AppView application.start :=
  application.selected.view

noncomputable def SpineApplication.argument
    (application : SpineApplication root context binderTypes expression) :
    SpineArgument root context binderTypes expression :=
  ⟨application.view.domainExpression, application.view.argument,
    .appArgument application.view.location,
    application.view.prefix_eq.trans application.prefix_eq⟩

structure SpineHead {node : EndpointState env U context (mkApps head arguments) type}
    (start : Located root node) where
  assigned : VExpr
  node : EndpointState env U context head assigned
  location : Located root node
  prefix_eq : location.binderPrefix = start.binderPrefix
  context_eq : ∀ initial, location.contextDerivation initial = start.contextDerivation initial
  environment_eq : ∀ initial, location.environment initial = start.environment initial

noncomputable def spineHead (arguments : List VExpr)
    {node : EndpointState env U context (mkApps head arguments) type}
    (start : Located root node) : SpineHead start := by
  cases arguments with
  | nil => exact ⟨_, node, start, rfl, fun _ => rfl, fun _ => rfl⟩
  | cons argument rest =>
    let tail := spineHead rest (head := .app head argument) start
    let selected := applicationPrefix tail.location
    refine ⟨_, selected.view.function, .appFunction selected.view.location,
      selected.view.prefix_eq.trans tail.prefix_eq, ?_, ?_⟩
    · intro initial
      change selected.view.location.contextDerivation initial = _
      rw [← selected.location_eq, PrefixRoute.locate_contextDerivation, tail.context_eq]
    · intro initial
      change selected.view.location.environment initial = _
      rw [← selected.location_eq, PrefixRoute.locate_environment, tail.environment_eq]

/-- Follow the actual application spine while retaining the application at
which the selected argument was checked. All conversion exposure remains in
its original location; no source proof is reconstructed. -/
noncomputable def spineApplication (arguments : List VExpr)
    {node : EndpointState env U context (mkApps head arguments) type}
    (start : Located root node) (index : Nat)
    (selected : arguments[index]? = some expression) :
    SpineApplication root context start.binderPrefix expression := by
  cases arguments with
  | nil => simp at selected
  | cons argument rest =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
      cases selected
      let tail := spineHead rest (head := .app head expression) start
      exact ⟨head, tail.assigned, tail.node, tail.location, tail.prefix_eq,
        applicationPrefix tail.location⟩
    | succ index =>
      exact spineApplication rest (head := .app head argument) start index selected

theorem spineApplication_context
    {root : EndpointRef env U source rootExpression rootType} (arguments : List VExpr)
    {node : EndpointState env U context (mkApps head arguments) type}
    (start : Located root node) (index : Nat) (selected : arguments[index]? = some expression)
    (initial : ContextDerivation env U source) :
    (spineApplication arguments start index selected).view.location.contextDerivation initial =
      start.contextDerivation initial := by
  induction arguments generalizing head index with
  | nil => simp at selected
  | cons argument rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
      cases selected
      change (applicationPrefix (spineHead rest (head := .app head expression) start).location).view.location.contextDerivation initial = _
      rw [← (applicationPrefix _).location_eq, PrefixRoute.locate_contextDerivation,
        (spineHead rest start).context_eq]
    | succ index => exact ih start index selected

theorem spineApplication_environment
    {root : EndpointRef env U source rootExpression rootType} (arguments : List VExpr)
    {node : EndpointState env U context (mkApps head arguments) type}
    (start : Located root node) (index : Nat) (selected : arguments[index]? = some expression)
    (initial : List Closure) :
    (spineApplication arguments start index selected).view.location.environment initial =
      start.environment initial := by
  induction arguments generalizing head index with
  | nil => simp at selected
  | cons argument rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
      cases selected
      change (applicationPrefix (spineHead rest (head := .app head expression) start).location).view.location.environment initial = _
      rw [← (applicationPrefix _).location_eq, PrefixRoute.locate_environment,
        (spineHead rest start).environment_eq]
    | succ index => exact ih start index selected

theorem spineApplication_functionExpression (arguments : List VExpr)
    {node : EndpointState env U context (mkApps head arguments) type}
    (start : Located root node) (index : Nat) (selected : arguments[index]? = some expression) :
    (spineApplication arguments start index selected).functionExpression = mkApps head (arguments.take index) := by
  induction arguments generalizing head index with
  | nil => simp at selected
  | cons argument rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
      cases selected
      rfl
    | succ index => exact ih start index selected

/-- The assigned-family formation path can be selected beneath any actual
original root, including a projection major's assigned-formation edge. -/
noncomputable def familyApplication
    {node : EndpointState env U context (mkApps (.const name levels) arguments) type}
    (start : Located root node) (index : Nat)
    (selected : arguments[index]? = some expression) :
    SpineApplication root context start.binderPrefix expression :=
  spineApplication arguments start index selected

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
