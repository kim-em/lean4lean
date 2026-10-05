import Lean4Lean.Theory.Typing.AnchoredSortableInstantiation
import Lean4Lean.Theory.Typing.AnchoredSortablePiExtraction
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableApplicationPreparation

/-! Actual mixed cuts become native substitution supplies using the fixed
original argument child. Current hereditary queries are source-type-unindexed:
the checked reflection theorem supplies the genuine argument query. This does
not assert reflection for the separate typed projection-metadata grammar. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Reanchor the selected exact row through its two original formation
children, then substitute the actual returned argument query. -/
theorem rowInstantiateSortableOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B argument : VExpr} {domainLevel bodyLevel : VLevel}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tail : SortableTailFits sourceEnv env U registry target source locals σ σ available)
    (domainF : StateSortableFundamental env registry context (.ref originalDomain))
    (bodyF : StateSortableFundamental env registry (.cons context originalDomain) originalBody)
    (row : SortablePiRowCertificate env U registry target locals σ available relevant A B key result)
    (admitted : Admitted env U registry target key (argument.subst σ) (argument.subst σ))
    (argumentResult : SortableGradedResult env U registry target locals σ available argument key.input) :
    Nonempty (SortableCertificateResult env U registry target locals σ available
      (B.inst argument) relevant result) := by
  obtain ⟨anchored⟩ := row.reanchorOriginal henv below formed closed
    context originalDomain originalBody substitutions tail domainF bodyF admitted
  have domain := originalDomain.sound.defeq.mono below
  have body := originalBody.sound.defeq.mono below
  have scope := body.closedN henv
    (CtxWF.closed henv ⟨substitutions.wf, domainLevel, domain⟩)
  have live := tail.leavesLive henv hscoped formed anchored.outsideAvailable
    (anchored.pack.scoped (anchored.body.scoped scope))
  exact anchored.body.instantiate henv hscoped formed closed argumentResult
    anchored.pack anchored.covered anchored.outsideAvailable live

/-- The only semantic call here is to the actual original argument endpoint.
Its returned assigned-type certificate and relation are retained alongside
the computed supply; no independently typed cut answer is assumed. -/
theorem SortableApplicationPreparation.supplyOriginal
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} {view : AppView start}
    (request : SortableApplicationPreparation (env := env) registry target locals σ available
      view relevant result before)
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : SortableTailPairedFits env registry target
      (view.location.contextDerivation initial) locals σ σ available)
    (argumentF : StateHereditaryFundamental env registry
      ((Located.appArgument view.location).contextDerivation initial) view.argument) :
    ∃ answer : SortableComputationalTransferResult env U registry target locals σ σ available
      argument argument view.domainExpression request.collected.input,
      Nonempty (SortableGradedSupply env U registry target locals σ (.one argument)
        available request.required) := by
  obtain ⟨answer⟩ := argumentF target locals σ σ available closed formed substitutions tails
    request.collected.observation request.collected.argumentAvailable
  have domain := view.domain.sound.defeq.mono below
  have body := view.codomain.sound.defeq.mono below
  have scope := body.closedN henv
    (CtxWF.closed henv ⟨substitutions.wf, _, domain⟩)
  have live := tails.forward.leavesLive henv hscoped formed request.collected.outsideAvailable
    (request.collected.pack.scoped (request.body.scoped scope))
  exact ⟨answer, SortableGradedSupply.instantiate answer.toSortableGradedResult
    request.collected.pack (fun _ member => member) request.collected.outsideAvailable live⟩

/-- Close inverse substitution back at the literal source result expression,
including native Pi queries in any of the mixed argument cuts. -/
theorem SortableApplicationPreparation.reconstructOriginal
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} {view : AppView start}
    (request : SortableApplicationPreparation (env := env) registry target locals σ available
      view relevant result before)
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : SortableTailPairedFits env registry target
      (view.location.contextDerivation initial) locals σ σ available)
    (argumentF : StateHereditaryFundamental env registry
      ((Located.appArgument view.location).contextDerivation initial) view.argument) :
    Nonempty (SortableCertificateResult env U registry target locals σ available
      (view.codomainExpression.inst argument) relevant result) := by
  obtain ⟨answer, ⟨supply⟩⟩ := request.supplyOriginal initial henv hscoped below closed formed
    substitutions tails argumentF
  have realized : (Subst.one argument).comp σ = σ.cons (argument.subst σ) := by
    funext index
    cases index <;> rfl
  simpa only [inst_eq] using request.body.substitute henv hscoped formed
    (.one argument) σ realized locals available closed supply

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
