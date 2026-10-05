import Lean4Lean.Theory.Typing.AnchoredOriginalSortableApplicationRule
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPrefix

/-! Recover the original constructor binder's frozen domain from its actual
unadapted function query. The source argument remains at its inferred domain;
no type injectivity or assumed domain-alignment callback is used. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- The actual original function child interprets the unadapted prefix at
its original key. Exact Pi extraction recovers the finite domain chain at
that key's full input, even when the input is empty. -/
theorem AppView.frozenKeyRow
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {function argument : VExpr}
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} (view : AppView start)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (initial : ContextDerivation sourceEnv U rootSource)
    (domainF : StateSortableFundamental env registry
      ((Located.appDomain view.location).contextDerivation initial) view.domain)
    (bodyF : StateSortableFundamental env registry
      ((Located.appCodomain view.location).contextDerivation initial) view.codomain)
    (functionF : StateHereditaryFundamental env registry
      ((Located.appFunction view.location).contextDerivation initial) view.function)
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : SortableTailFits sourceEnv env U registry target source locals σ σ available)
    {key : Key n} {output : Atom n} {footprint : Footprint}
    (query : SortableObs env U registry target locals σ function (Profile.fn key output) footprint)
    (resources : footprint.Available available) :
    ∃ result, Nonempty (SortablePiRowCertificate env U registry target locals σ available true
      view.domainExpression view.codomainExpression key result) ∧
      (Profile.singleton output).HasType result := by
  let domain := Classical.choose view.location.originalDomains.1
  have domainEq : view.domain = .ref domain := Classical.choose_spec view.location.originalDomains.1
  have actualDomain : StateSortableFundamental env registry
      (view.location.contextDerivation initial) (.ref domain) := by
    change StateSortableFundamental env registry (view.location.contextDerivation initial) view.domain at domainF
    simpa only [domainEq] using domainF
  have actualBody : StateSortableFundamental env registry
      (.cons (view.location.contextDerivation initial) domain) view.codomain := bodyF
  obtain ⟨answer⟩ := functionF target locals σ σ available closed formed substitutions
    (SortableTailPairedFits.diagonal (view.location.contextDerivation initial) tails) query resources
  exact answer.requestedCertificate.piRowOriginal henv hscoped below formed closed
    (view.location.contextDerivation initial) domain view.codomain substitutions tails
    actualDomain actualBody answer.typeAvailable answer.requestedTyped

/-- Reorient the extracted original-key row for the projected field recipe.
All frozen request metadata remains unchanged. -/
theorem AppView.frozenKeyAlignment
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {function argument : VExpr}
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} (view : AppView start)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (initial : ContextDerivation sourceEnv U rootSource)
    (domainF : StateSortableFundamental env registry
      ((Located.appDomain view.location).contextDerivation initial) view.domain)
    (bodyF : StateSortableFundamental env registry
      ((Located.appCodomain view.location).contextDerivation initial) view.codomain)
    (functionF : StateHereditaryFundamental env registry
      ((Located.appFunction view.location).contextDerivation initial) view.function)
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : SortableTailFits sourceEnv env U registry target source locals σ σ available)
    {key : Key n} {output : Atom n} {footprint : Footprint}
    (query : SortableObs env U registry target locals σ function (Profile.fn key output) footprint)
    (resources : footprint.Available available) :
    Nonempty (DomainChain env U registry target key.input
      (view.domainExpression.subst σ) key.domain) := by
  obtain ⟨_, ⟨row⟩, _⟩ := view.frozenKeyRow henv hscoped below initial domainF bodyF functionF
    closed formed substitutions tails query resources
  exact ⟨row.alignment.symm henv⟩

/-- All three fixed calls are strictly below this actual source application,
including the original codomain's captured binder environment. -/
theorem AppView.frozenKey_schedule
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {function argument : VExpr}
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} (view : AppView start)
    (initial : ContextDerivation sourceEnv U rootSource) :
    let parent := schedule .fundamental
      (Closure.close node.origin (start.environment initial.closures)).cost
    schedule .fundamental (Closure.close view.domain.origin
      ((Located.appDomain view.location).contextDerivation initial).closures).cost < parent ∧
    schedule .fundamental (Closure.close view.codomain.origin
      ((Located.appCodomain view.location).contextDerivation initial).closures).cost < parent ∧
    schedule .fundamental (Closure.close view.function.origin
      ((Located.appFunction view.location).contextDerivation initial).closures).cost < parent := by
  dsimp only
  rw [Located.contextDerivation_closures, Located.contextDerivation_closures,
    Located.contextDerivation_closures]
  have domain := binder_domain_cost view.domain.origin [view.codomain.origin]
    [view.function.origin, view.argument.origin, view.result.origin]
    (view.location.environment initial.closures)
  have body := binder_body_cost (domain := view.domain.origin) (bodies := [view.codomain.origin])
    (children := [view.function.origin, view.argument.origin, view.result.origin])
    (body := view.codomain.origin) (by simp) (view.location.environment initial.closures)
  have function := binder_other_cost (domain := view.domain.origin) (bodies := [view.codomain.origin])
    (children := [view.function.origin, view.argument.origin, view.result.origin])
    (child := view.function.origin) (by simp) (view.location.environment initial.closures)
  exact ⟨schedule_strict (Nat.lt_of_lt_of_le domain (view.cost_le initial.closures)) _ _,
    schedule_strict (Nat.lt_of_lt_of_le body (view.cost_le initial.closures)) _ _,
    schedule_strict (Nat.lt_of_lt_of_le function (view.cost_le initial.closures)) _ _⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
