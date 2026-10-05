import Lean4Lean.Theory.Typing.AnchoredOriginalLambdaPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalDependencyEndpoints
import Lean4Lean.Theory.Typing.EquationHeaderDerivation
import Lean4Lean.Theory.Inductive.CaseReductionData

/-! Native terminals observe an open equation body, whereas their retained
equation origin is closed. This extraction follows only actual reference,
conversion and lambda-body edges of that origin. It supplies no semantic
answer and does not equate the body's inferred type with the declared result.
The remaining interpreter must construct a frame for this exact location. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure OriginalEndpointFactor
open InductiveSignature
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- The actual body occurrence after peeling a finite original lambda spine.
Its assigned type is deliberately retained, not replaced by a declared type. -/
structure OriginalLambdaTelescopeBody
    {root : EndpointRef sourceEnv U rootContext rootExpression rootType}
    {node : EndpointState sourceEnv U source (wrapLams domains body) assigned}
    (start : Located root node) where
  context : List VExpr
  type : VExpr
  endpoint : EndpointState sourceEnv U context body type
  location : Located root endpoint
  context_eq : context = domains.reverse ++ source
  prefix_eq : location.binderPrefix = domains.reverse ++ start.binderPrefix

/-- Pure original-proof traversal, including actual conversion prefixes at
each binder. No earlier fundamental theorem or query supplier is used. -/
noncomputable def OriginalEndpointFactor.Located.lambdaTelescopeBody
    {root : EndpointRef sourceEnv U rootContext rootExpression rootType}
    (domains : List VExpr) {body assigned : VExpr}
    {node : EndpointState sourceEnv U source (wrapLams domains body) assigned}
    (start : Located root node) : OriginalLambdaTelescopeBody start := by
  cases domains with
  | nil =>
    exact ⟨source, assigned, node, start, rfl, rfl⟩
  | cons domain domains =>
    let selected := lambdaPrefix start
    let child := OriginalEndpointFactor.Located.lambdaTelescopeBody domains
      (Located.lamBody selected.view.location)
    refine ⟨child.context, child.type, child.endpoint, child.location, ?_, ?_⟩
    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append]
        using child.context_eq
    · rw [child.prefix_eq]
      change domains.reverse ++ (domain :: selected.view.location.binderPrefix) = _
      rw [selected.view.prefix_eq]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
termination_by domains.length

theorem OriginalLambdaTelescopeBody.dependency_cost_le
    {root : EndpointRef sourceEnv U rootContext rootExpression rootType}
    {node : EndpointState sourceEnv U source (wrapLams domains body) assigned}
    {start : Located root node} (selected : OriginalLambdaTelescopeBody start)
    (ordered : sourceEnv.Ordered) (initial : List Closure) :
    (Closure.close (selected.endpoint.dependencyOrigin ordered)
      (selected.location.dependencyEnvironment ordered initial)).cost ≤
        (Closure.close (root.dependencyOrigin ordered) initial).cost :=
  selected.location.dependency_cost_le ordered initial

/-- Select the open native RHS under the SAME retained equation origin and
universe instance. Parser soundness changes only the expression index. -/
noncomputable def EquationHeaderOrigin.nativeRhsBody
    {rule : VDefEq} {levels : List VLevel} {U : Nat}
    (origin : EquationHeaderOrigin env rule)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    {body : CaseSchema.EquationBody}
    (extracted : CaseSchema.EquationBody.extract rule.lhs rule.rhs rule.type = some body) :=
  let reference := EndpointRef.left (EquationHeaderOrigin.instantiatedRhs origin levelsWF)
  let shape : rule.rhs.instL levels =
      wrapLams (body.domains.map (·.instL levels)) (body.rhs.instL levels) := by
    rw [← (CaseSchema.EquationBody.extract_sound extracted).2.1, instL_wrapLams]
  (Located.here (root := reference) |>.castExpression shape).lambdaTelescopeBody
    (body.domains.map (·.instL levels))

end Lean4Lean.AnchoredSource.Adapted
