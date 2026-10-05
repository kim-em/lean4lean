import Lean4Lean.Theory.Typing.AnchoredOriginalFactorTraversal
import Lean4Lean.Theory.Typing.AnchoredNativeSeededSpine

/-! One backward application step at an actual original endpoint. Preparation
retains the located result-type cuts and constructs one finite query for the
original argument at its natural assigned type. Completion consumes the
answer to that query; it does not assume semantics for arbitrary Strong
derivations or type an argument at a declaration's inferred telescope domain.

The retained cut origins are obligations for the typed query interpretation.
This module does not identify their assigned types with the argument's type,
and does not assert that erasing those origins implements that interpretation.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false

/-- The finite request produced before invoking the original argument child.
The syntax-only packing forgets locations, but the request retains the full
located trace independently, including the assigned type of every cut. -/
structure ApplicationPreparation
    {sourceEnv env : VEnv} {U : Nat}
    {rootSource : List VExpr} {rootExpression rootType : VExpr}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat)
    (σ : Subst) (available : Valuation)
    {source : List VExpr} {f a assigned : VExpr}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    {start : Located root node} (view : AppView start)
    (result : Profile n) (before : Footprint) where
  residual : CodeCert env U registry target locals σ
    (view.codomainExpression.inst a) result before
  seed : NativeArgumentSeed env U registry target locals σ available a
  required : Footprint
  cuts : LocatedFootprintAt (env := env) root view.location.binderPrefix registry target locals σ a 0 0 before required
  cutsBound : ∀ initial, cuts.cost initial ≤
    (Closure.close view.result.origin (view.location.environment initial)).cost
  collected : FactoredArguments env U registry target locals σ available a required
    (max n seed.rank)
  body : CodeCert env U registry target (Locals.push locals) (σ.cons (a.subst σ))
    view.codomainExpression result required

namespace ApplicationPreparation
variable
    {sourceEnv env : VEnv} {U : Nat}
    {rootSource : List VExpr} {rootExpression rootType : VExpr}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {registry : CanonicalHead.Registry} {target : List VExpr} {locals : List Nat}
    {σ : Subst} {available : Valuation}
    {source : List VExpr} {f a assigned : VExpr}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    {start : Located root node} {view : AppView start}
    {result : Profile n} {before : Footprint}

def input (request : ApplicationPreparation (env := env) registry target locals σ available view result before) :
    Profile request.collected.rank :=
  (raiseProfile request.collected.rank
    (Nat.le_trans (Nat.le_max_right _ _) request.collected.bound) request.seed.demand).union
      request.collected.input

noncomputable def observation
    (request : ApplicationPreparation (env := env) registry target locals σ available view result before) :
    Obs env U registry target locals σ a request.input
      (request.seed.footprint ++ request.collected.argumentFootprint) :=
  .union
    (request.seed.observation.raise
      (Nat.le_trans (Nat.le_max_right _ _) request.collected.bound))
    request.collected.observation

theorem resources
    (request : ApplicationPreparation (env := env) registry target locals σ available view result before) :
    (request.seed.footprint ++ request.collected.argumentFootprint).Available available := by
  intro index need member
  exact (List.mem_append.mp member).elim (request.seed.resources index need)
    (request.collected.argumentAvailable index need)

/-- This is the single finite answer required by completion. Its source type
is the actual application's original argument type, with no header retyping
premise and no universally quantified semantic supplier. -/
abbrev Answer
    (request : ApplicationPreparation (env := env) registry target locals σ available view result before) :=
  GradedTransferResult env U registry target locals σ σ available a a
    view.domainExpression request.input

/-- Every retained result-type cut can be compared with the original
argument within the original application's reserve. The bound is against
the selected result child, not merely against their shared root. -/
theorem cuts_argument_schedule
    (request : ApplicationPreparation (env := env) registry target locals σ available view result before)
    (initial : List Closure) :
    schedule .coherence (request.cuts.cost initial +
      (Closure.close view.argument.origin (view.location.environment initial)).cost) <
      schedule .fundamental (Closure.close root.origin initial).cost := by
  apply schedule_strict
  exact Nat.lt_of_lt_of_le
    (Nat.lt_of_le_of_lt (Nat.add_le_add_right (request.cutsBound initial) _)
      (view.result_argument_cost_lt initial))
    (start.cost_le initial)

/-- The single merged argument query is charged to the actual argument
endpoint, independently of the size of its resulting observation profile. -/
theorem argument_schedule
    (_request : ApplicationPreparation (env := env) registry target locals σ available view result before)
    (initial : List Closure) :
    schedule .fundamental
      (Closure.close view.argument.origin (view.location.environment initial)).cost <
      schedule .fundamental (Closure.close root.origin initial).cost := by
  apply schedule_strict
  exact Nat.lt_of_le_of_lt (Nat.le_add_left _ _)
    (Nat.lt_of_lt_of_le (view.result_argument_cost_lt initial) (start.cost_le initial))

/-- The larger Pi query returned by completion continues at the actual
function child; growing the query does not grow its original closure cost. -/
theorem function_schedule
    (_request : ApplicationPreparation (env := env) registry target locals σ available view result before)
    (initial : List Closure) :
    schedule .fundamental
      (Closure.close view.function.origin (view.location.environment initial)).cost <
      schedule .fundamental (Closure.close root.origin initial).cost := by
  apply schedule_strict
  have child := binder_other_cost (domain := view.domain.origin)
    (bodies := [view.codomain.origin])
    (children := [view.function.origin, view.argument.origin, view.result.origin])
    (child := view.function.origin) (by simp) (view.location.environment initial)
  exact Nat.lt_of_lt_of_le child
    (Nat.le_trans (view.cost_le initial) (start.cost_le initial))

noncomputable def complete
    (request : ApplicationPreparation (env := env) registry target locals σ available view result before)
    (henv : env.Ordered) (hle : sourceEnv ≤ env)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (answer : request.Answer) :
    SeededApplicationCodeInput env U registry target locals σ available
      view.domainExpression view.codomainExpression a result before := by
  have raw := (view.argument.sound.defeq.mono hle).substDF henv
    substitutions.wf hTarget substitutions
  have related := answer.requestedRelated henv hTarget
  have domain := answer.requestedCertificate
  have code := TypeRelated.lower henv answer.bound answer.typeCode
  exact {
    residual := request.residual
    seed := request.seed
    required := request.required
    cuts := request.cuts.erase
    collected := request.collected
    support := lowerProfile request.collected.rank answer.bound answer.support
    domainFootprint := answer.typeFootprint
    domain := domain
    domainAvailable := answer.typeAvailable
    guard := ⟨answer.requestedTyped, domain.formed, .refl, code,
      ⟨raw, raw, _, answer.requestedTyped, domain.formed, code, related, related⟩⟩
    body := request.body.raise
      (Nat.le_trans (Nat.le_max_left _ _) request.collected.bound) }

end ApplicationPreparation

private theorem one_comp (argument : VExpr) (σ : Subst) :
    (Subst.one argument).comp σ = σ.cons (argument.subst σ) := by
  funext index
  cases index <;> rfl

/-- Factor a query at the application's actual result-type child. The bound
is obtained from the traversal, and the result path is selected here rather
than supplied by the caller. -/
theorem CodeCert.prepareOriginalApplication
    {sourceEnv env : VEnv} {U : Nat}
    {rootSource : List VExpr} {rootExpression rootType : VExpr}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {registry : CanonicalHead.Registry} {target : List VExpr} {locals : List Nat}
    {σ : Subst} {available : Valuation}
    {source : List VExpr} {f a assigned : VExpr}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    {start : Located root node} (view : AppView start)
    (seed : NativeArgumentSeed env U registry target locals σ available a)
    {result : Profile n} {before : Footprint}
    (certificate : CodeCert env U registry target locals σ
      (view.codomainExpression.inst a) result before)
    (resources : before.Available available) :
    ∃ request : ApplicationPreparation (env := env) registry target locals σ available view result before,
      request.seed = seed := by
  obtain ⟨required, ⟨body⟩, ⟨cuts⟩⟩ := CodeCert.factorInstAtStart certificate
    view.result (.appResult view.location) locals (Locals.push locals)
  simp only [one_comp] at body
  obtain ⟨collected⟩ := cuts.erase.erase.arguments available resources (max n seed.rank)
  exact ⟨⟨certificate, seed, required, cuts.erase, cuts.cost_le, collected, body⟩, rfl⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
