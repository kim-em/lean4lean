import Lean4Lean.Theory.Typing.AnchoredOriginalSortableApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableFundamental
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableArguments

/-! Actual one-pass application preparation in the hereditary query grammar.
All whole cuts, including new computational lambda/application queries,
retain their original locations. One fixed smaller original argument F call
constructs the domain admission for the exact collected query. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

structure SortableApplicationPreparation
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat)
    (σ : Subst) (available : Valuation)
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} (view : AppView start)
    (relevant : Bool) (result : Profile n) (before : Footprint) where
  required : Footprint
  cuts : SortableLocatedFootprint (env := env) root view.location.binderPrefix registry target locals σ
    argument 0 0 (fun initial => (Closure.close view.result.origin (view.location.environment initial)).cost)
    before required
  collected : SortableFactoredArguments env U registry target locals σ available argument required n
  body : SortableCert env U registry target (Locals.push locals) (σ.cons (argument.subst σ))
    view.codomainExpression relevant result required

private theorem one_comp (argument : VExpr) (σ : Subst) :
    (Subst.one argument).comp σ = σ.cons (argument.subst σ) := by
  funext index
  cases index <;> rfl

theorem SortableCert.prepareApplication
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} (view : AppView start)
    (certificate : SortableCert env U registry target locals σ
      (view.codomainExpression.inst argument) relevant result before)
    (resources : before.Available available) :
    Nonempty (SortableApplicationPreparation (env := env) registry target locals σ available
      view relevant result before) := by
  obtain ⟨required, ⟨body⟩, ⟨cuts⟩⟩ := SortableCert.factorInstAtStart certificate
    view.result (.appResult view.location) locals (Locals.push locals)
  obtain ⟨collected⟩ := cuts.arguments available resources _
  rw [one_comp] at body
  exact ⟨⟨required, cuts, collected, body⟩⟩

/-- The finite input and full domain certificate are produced by the actual
argument occurrence, not supplied by a caller or erased to the legacy syntax. -/
theorem SortableApplicationPreparation.complete
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} {view : AppView start}
    (request : SortableApplicationPreparation (env := env) registry target locals σ available
      view relevant result before)
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : SortableTailPairedFits env registry target
      (view.location.contextDerivation initial) locals σ σ available)
    (argumentF : StateHereditaryFundamental env registry
      ((Located.appArgument view.location).contextDerivation initial) view.argument) :
    Nonempty (SortableApplicationFrame env U registry target locals σ available
      view.domainExpression view.codomainExpression argument relevant request.collected.input
      (raiseProfile request.collected.rank request.collected.bound result)) := by
  obtain ⟨answer⟩ := argumentF target locals σ σ available closed formed substitutions tails
    request.collected.observation request.collected.argumentAvailable
  have typed := lowerProfile.hasType answer.bound answer.typed
  have related := lowerProfile.related answer.bound henv formed answer.related
  have domain := answer.typeCertificate.lower request.collected.rank answer.bound
  have code := answer.typeCode.lower henv answer.bound
  have raw := (view.argument.sound.defeq.mono below).substDF henv substitutions.wf formed substitutions
  exact ⟨{
    support := _, domainFootprint := answer.typeFootprint, domain := domain
    domainAvailable := answer.typeAvailable
    guard := ⟨typed, domain.formed, .refl, code,
      ⟨raw, raw, _, typed, domain.formed, code, related, related⟩⟩
    bodyFootprint := request.required, body := request.body.raise request.collected.bound
    packed := request.collected.input, outside := request.collected.outside
    pack := request.collected.pack, covered := fun _ member => member
    outsideAvailable := request.collected.outsideAvailable }⟩

/-- The full selected result closure, not the enclosing root, bounds every
whole cut. This permits adding the actual argument charge under the parent. -/
theorem SortableApplicationPreparation.cuts_argument_schedule
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} {view : AppView start}
    (request : SortableApplicationPreparation (env := env) registry target locals σ available
      view relevant result before)
    (initial : ContextDerivation sourceEnv U rootSource) (otherCost : Nat) :
    schedule .coherence (request.cuts.cost initial.closures +
      (Closure.close view.argument.origin (view.location.environment initial.closures)).cost) <
    schedule .coherence ((Closure.close node.origin (start.environment initial.closures)).cost + otherCost) := by
  apply schedule_strict
  exact Nat.lt_of_lt_of_le
    (Nat.lt_of_le_of_lt (Nat.add_le_add_right (request.cuts.cost_le initial.closures) _)
      (view.result_argument_cost_lt initial.closures)) (Nat.le_add_right _ _)

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
