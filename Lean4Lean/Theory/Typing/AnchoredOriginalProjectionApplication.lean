import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSpine
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionValue

/-! A projected application's actual argument seed and actual result-type
factorization construct a finite typed frame. The retained trace still names
every original cut. The result certificate here uses the current CodeCert
grammar, whose whole-projection cuts are necessarily empty; this theorem does
not cover an enlarged certificate grammar containing typed projection nodes. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

structure ProjectionApplicationPreparation
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat)
    (σ : Subst) (available : Valuation)
    {node : EndpointState sourceEnv U source (.app f (.proj name index major)) assigned}
    {start : Located root node} (view : AppView start) (key : Key k)
    (result : Profile n) (before : Footprint) where
  sourceSeed : ProjectedApplicationSeed (env := env) registry target locals σ available view key
  residual : CodeCert env U registry target locals σ
    (view.codomainExpression.inst (.proj name index major)) result before
  required : Footprint
  outside : Footprint
  cuts : LocatedFootprintAt (env := env) root view.location.binderPrefix registry target
    locals σ (.proj name index major) 0 0 before required
  cutsBound : ∀ initial, cuts.cost initial ≤
    (Closure.close view.result.origin (view.location.environment initial)).cost
  collected : ProjectionFactoredArguments env registry target view.argument locals σ available
    required outside (max n sourceSeed.seed.rank)
  outsideResources : outside.Available available
  body : CodeCert env U registry target (Locals.push locals)
    (σ.cons ((VExpr.proj name index major).subst σ)) view.codomainExpression result required

private theorem one_comp (argument : VExpr) (σ : Subst) :
    (Subst.one argument).comp σ = σ.cons (argument.subst σ) := by
  funext index
  cases index <;> rfl

/-- The seed comes from the actual typed application argument. Every dependent
cut is produced by traversal of the original result formation child. -/
theorem CodeCert.prepareProjectionApplication
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {registry : CanonicalHead.Registry} {target : List VExpr} {locals : List Nat}
    {σ : Subst} {available : Valuation}
    {node : EndpointState sourceEnv U source (.app f (.proj name index major)) assigned}
    {start : Located root node} (view : AppView start) {key : Key k}
    (seed : ProjectedApplicationSeed (env := env) registry target locals σ available view key)
    {result : Profile n} {before : Footprint}
    (certificate : CodeCert env U registry target locals σ
      (view.codomainExpression.inst (.proj name index major)) result before)
    (resources : before.Available available) :
    ∃ request : ProjectionApplicationPreparation (env := env) registry target locals σ available
      view key result before, request.sourceSeed = seed := by
  obtain ⟨required, ⟨body⟩, ⟨cuts⟩⟩ := CodeCert.factorInstAtStart certificate
    view.result (.appResult view.location) locals (Locals.push locals)
  simp only [one_comp] at body
  obtain ⟨collected⟩ := cuts.erase.erase.arguments available resources (max n seed.seed.rank)
  have empty := legacyProjectionEmpty collected.observation
  let typed : ProjectionFactoredArguments env registry target view.argument locals σ available
      required collected.outside (max n seed.seed.rank) := {
    rank := collected.rank, bound := collected.bound, input := collected.input
    footprint := [], query := empty ▸ ProjectionObs.empty
    resources := (fun _ _ member => nomatch member), pack := collected.pack }
  exact ⟨⟨seed, certificate, required, collected.outside, cuts.erase, cuts.cost_le,
    typed, collected.outsideAvailable, body⟩, rfl⟩

namespace ProjectionApplicationPreparation
variable {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {registry : CanonicalHead.Registry} {target : List VExpr} {locals : List Nat}
    {σ : Subst} {available : Valuation}
    {node : EndpointState sourceEnv U source (.app f (.proj name index major)) assigned}
    {start : Located root node} {view : AppView start} {key : Key k}
    {result : Profile n} {before : Footprint}

/-- Completion queries only the actual argument endpoint's retained original
projection children and conversion leaves. The incoming application adapter
is retained through the exact seed equality. -/
theorem complete
    (request : ProjectionApplicationPreparation (env := env) registry target locals σ available
      view key result before)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (initial : ContextDerivation sourceEnv U source)
    (calls : PrefixCall.Fundamentals env registry (projectionHead view.argument).route initial)
    (fieldFundamental : StateFundamental env registry initial (projectionHead view.argument).field)
    (majorFundamental : DerivationFundamental env registry initial (projectionHead view.argument).major)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : TailPairedFits env registry target initial locals σ σ available) :
    ∃ frame : ProjectionSeededFrame env registry target view.argument locals σ available
      view.codomainExpression result,
      frame.seed = request.sourceSeed.seed ∧ frame.required = request.required ∧
      frame.outside = request.outside ∧ HEq frame.collected request.collected := by
  exact ProjectionSeededFrame.ofOriginalEndpointExact view.argument henv hscoped below initial
    calls fieldFundamental majorFundamental closed formed substitutions tails request.sourceSeed.seed
    request.collected request.outsideResources
    (request.body.raise (Nat.le_trans (Nat.le_max_left _ _) request.collected.bound))

/-- The exact trace bound charges cut reindexing and the natural argument
below the selected actual application, even when it occurs below binders. -/
theorem cuts_argument_schedule
    (request : ProjectionApplicationPreparation (env := env) registry target locals σ available
      view key result before) (initial : List Closure) :
    schedule .coherence (request.cuts.cost initial +
      (Closure.close view.argument.origin (view.location.environment initial)).cost) <
    schedule .fundamental (Closure.close node.origin (start.environment initial)).cost := by
  apply schedule_strict
  exact Nat.lt_of_le_of_lt (Nat.add_le_add_right (request.cutsBound initial) _)
    (view.result_argument_cost_lt initial)

end ProjectionApplicationPreparation
end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
