import Lean4Lean.Theory.Typing.AnchoredOriginalSortableContract
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationCoherence

/-! The finite application query really carries false-sort output rows.
An actual original argument formation call supplies its assigned-type
capability and admission; the query is built with native sortable Pi syntax.
This step does not claim general substitution back into legacy Obs. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

structure SortableApplicationFrame (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat)
    (σ : Subst) (available : Valuation) (A B argument : VExpr)
    (relevant : Bool) (input result : Profile n) where
  support : Profile n
  domainFootprint : Footprint
  domain : SortableCert env U registry target locals σ A true support domainFootprint
  domainAvailable : domainFootprint.Available available
  guard : LambdaGuard env U registry target σ A ⟨A.subst σ, argument.subst σ, input⟩ support
  bodyFootprint : Footprint
  body : SortableCert env U registry target (Locals.push locals) (σ.cons (argument.subst σ))
    B relevant result bodyFootprint
  packed : Profile n
  outside : Footprint
  pack : BinderPack n packed bodyFootprint outside
  covered : ∀ atom ∈ packed.atoms, atom ∈ input.atoms
  outsideAvailable : outside.Available available

namespace SortableApplicationFrame
variable {n : Nat} {input result : Profile n}

def key (frame : SortableApplicationFrame env U registry target locals σ available A B argument
    relevant input result) : Key n := ⟨A.subst σ, argument.subst σ, input⟩

def profile (frame : SortableApplicationFrame env U registry target locals σ available A B argument
    relevant input result) : Profile (n + 1) :=
  .pi (A.subst σ) (B.subst σ.lift) frame.support [(frame.key, result)]

noncomputable def certificate
    (frame : SortableApplicationFrame env U registry target locals σ available A B argument
      relevant input result) :
    SortableCert env U registry target locals σ (.forallE A B) relevant frame.profile
      (frame.domainFootprint ++ frame.outside) := by
  have rows : SortableRows env U registry target locals σ A B relevant frame.support
      [(frame.key, result)] frame.outside := by
    simpa only [List.append_nil, key] using
      SortableRows.cons frame.guard frame.body frame.pack frame.covered SortableRows.nil
  exact .piLiteral frame.domain rows

theorem resources
    (frame : SortableApplicationFrame env U registry target locals σ available A B argument
      relevant input result) : (frame.domainFootprint ++ frame.outside).Available available :=
  fun index need member => (List.mem_append.mp member).elim
    (frame.domainAvailable index need) (frame.outsideAvailable index need)

/-- Actual beta source reconstruction uses the new computational grammar:
the factored body and argument stay native sortable queries when needed.
No interpretation of a synthesized lambda or application is invoked. -/
theorem betaCertificate
    {output : Atom n}
    (frame : SortableApplicationFrame env U registry target locals σ available A B argument
      relevant input (.singleton output))
    (argumentObservation : SortableObs env U registry target locals σ argument input argumentFootprint)
    (argumentAvailable : argumentFootprint.Available available) :
    ∃ footprint, Nonempty (SortableCert env U registry target locals σ
      (.app (.lam A B) argument) relevant (.singleton output) footprint) ∧
      footprint.Available available := by
  have function := SortableObs.lam frame.domain frame.guard
    (SortableObs.code relevant frame.body) frame.pack frame.covered
  have application := SortableObs.app function argumentObservation (.refl _) frame.guard.anchor
  exact ⟨_, ⟨.observe application frame.body.formed⟩,
    fun index need member => (List.mem_append.mp member).elim
      (frame.resources index need) (argumentAvailable index need)⟩

end SortableApplicationFrame

/-- Consume the actual smaller argument's new formation clause. The
remaining inputs are finite syntactic factoring data, not semantic suppliers. -/
theorem AppView.sortableApplicationFrame
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} (view : AppView start)
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : SortableTailPairedFits env registry target
      (view.location.contextDerivation initial) locals σ σ available)
    (argumentF : StateSortableFundamental env registry
      ((Located.appArgument view.location).contextDerivation initial) view.argument)
    {input result packed : Profile n}
    (query : SortableCert env U registry target locals σ argument argumentRelevant input queryFootprint)
    (resources : queryFootprint.Available available)
    (body : SortableCert env U registry target (Locals.push locals) (σ.cons (argument.subst σ))
      view.codomainExpression relevant result bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ input.atoms)
    (outsideResources : outside.Available available) :
    Nonempty (SortableApplicationFrame env U registry target locals σ available
      view.domainExpression view.codomainExpression argument relevant input result) := by
  obtain ⟨answer⟩ := argumentF target locals σ σ available closed formed substitutions tails query resources
  have raw := (view.argument.sound.defeq.mono below).substDF henv substitutions.wf formed substitutions
  exact ⟨{
    support := answer.support
    domainFootprint := answer.typeFootprint, domain := answer.typeCertificate
    domainAvailable := answer.typeAvailable
    guard := ⟨answer.typed, answer.typeCertificate.formed, .refl, answer.typeCode,
      ⟨raw, raw, _, answer.typed, answer.typeCertificate.formed, answer.typeCode,
        answer.termRelated, answer.termRelated⟩⟩
    bodyFootprint := bodyFootprint, body := body, packed := packed, outside := outside
    pack := pack, covered := covered, outsideAvailable := outsideResources }⟩

/-- The new formation clause uses the same strict actual argument charge;
query grade and the Bool flag have no effect on the recursive measure. -/
theorem AppView.sortableArgument_schedule
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} (view : AppView start)
    (initial : ContextDerivation sourceEnv U rootSource) (otherCost : Nat) :
    schedule .fundamental (Closure.close view.argument.origin
      ((Located.appArgument view.location).contextDerivation initial).closures).cost <
    schedule .coherence ((Closure.close node.origin (start.environment initial.closures)).cost + otherCost) := by
  apply schedule_strict
  rw [Located.contextDerivation_closures]
  have smaller := binder_other_cost (domain := view.domain.origin)
    (bodies := [view.codomain.origin])
    (children := [view.function.origin, view.argument.origin, view.result.origin])
    (child := view.argument.origin) (by simp) (view.location.environment initial.closures)
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le smaller (view.cost_le initial.closures))
    (Nat.le_add_right _ _)

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
