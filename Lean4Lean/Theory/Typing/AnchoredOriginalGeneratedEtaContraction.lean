import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedEtaLift
import Lean4Lean.Theory.Typing.AnchoredOriginalRichReferenceExposure
import Lean4Lean.Theory.Typing.AnchoredOriginalSupportedEquality
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericComputational
import Lean4Lean.Theory.Typing.AnchoredEtaExpansion

/-! Native rich eta contraction at actual original endpoints. Only the
literal bound-variable query is erased. Function queries retain their
projected code and are replayed between eta's two original function children. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private etaBody from Lean4Lean.Theory.Typing.AnchoredOriginalEndpoints
open private LambdaGuard.anchorRelated from Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiReindex
open private lower_raised from Lean4Lean.Theory.Typing.AnchoredFamilyArgumentGrades
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option quotPrecheck false

private def uncastObservation
    {node : EndpointState sourceEnv U source expression assigned}
    (he : expression = nextExpression) (ht : assigned = nextAssigned)
    (query : RichObs sourceEnv env U registry target (node.cast he ht) locals σ profile footprint) :
    RichObs sourceEnv env U registry target node locals σ profile footprint := by
  cases he; cases ht; exact query

private def uncastLocation
    {root : EndpointRef sourceEnv U rootSource rootExpression rootAssigned}
    {node : EndpointState sourceEnv U source expression assigned}
    (he : expression = nextExpression) (ht : assigned = nextAssigned)
    (location : Located root (node.cast he ht)) : Located root node := by
  cases he; cases ht; exact location

private theorem eta_subst (A f : VExpr) (σ : Subst) :
    (VExpr.lam A (.app f.lift (.bvar 0))).subst σ =
      .lam (A.subst σ) (.app (f.subst σ).lift (.bvar 0)) := by
  show VExpr.lam (A.subst σ) (.app (f.lift.subst σ.lift) ((VExpr.bvar 0).subst σ.lift)) = _
  rw [lift_subst_lift]
  rfl

section
variable
  {sourceEnv : VEnv} {U : Nat} {source : List VExpr} {A B f : VExpr} {u v : VLevel}
  (context : ContextDerivation sourceEnv U source)
  (domainWF : u.WF U) (bodyWF : v.WF U)
  (domain : Derivation sourceEnv U source A A (.sort u))
  (codomain : Derivation sourceEnv U (A :: source) B B (.sort v))
  (liftedCodomain : Derivation sourceEnv U (A.lift :: A :: source)
    (B.liftN 1 1) (B.liftN 1 1) (.sort v))
  (term : Derivation sourceEnv U source f f (.forallE A B))
  (liftedTerm : Derivation sourceEnv U (A :: source) f.lift f.lift
    (.forallE A.lift (B.liftN 1 1)))
  (liftedDomain : Derivation sourceEnv U (A :: source) A.lift A.lift (.sort u))
  (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
  (substitutions : Ctx.SubstEq env U target σ τ source)
  (ordered : sourceEnv.Ordered)
local notation "original" => Derivation.eta domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain
local notation "body" => etaBody domainWF bodyWF codomain liftedCodomain liftedTerm liftedDomain
local notation "limit" => (Closure.close ((original).dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost
local notation "base" => frame.captureBase substitutions
local notation "destination" => (OriginalNestedDisplay.identity base (.ref (.left term)) (.ofLocation .here context)).weaken (Ctx.Lift'.skip (A := A) .refl)

/-- The requested support comes from the actual exposed lambda F. The
original function is queried at the finite raw profile produced by reindex,
then its real output adapter recovers exactly that requested support. -/
theorem generatedEtaNativeContraction
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (leftF : OriginalComputationalInductionAt env registry ordered context
      (.expose (.here (root := .left original))) limit)
    (liftedF : OriginalComputationalInductionAt env registry ordered (.cons context (.left domain))
      (.here (root := .left liftedTerm)) limit)
    (termF : OriginalComputationalInductionAt env registry ordered context (.here (root := .left term)) limit)
    {key : Key n} {output : Atom n} {ambient packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (functionR : GeneratedObservationCall base ((base).initialCaps.push (Need.Fits key.input))
      (etaLiftedFunctionDisplay context domain liftedTerm) destination
      (σ.cons key.anchor) (τ.cons key.anchor) ordered ordered (richSchedule .fundamental limit))
    (domainCode : RichCert sourceEnv env U registry target (.ref (.left domain)) locals σ true ambient domainFootprint)
    (guard : LambdaGuard env U registry target σ A key ambient)
    (observation : RichObs sourceEnv env U registry target body (Locals.push locals)
      (σ.cons key.anchor) (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    Nonempty (OriginalSupportedEqualityResult original env registry target locals σ τ available (Profile.fn key output)) := by
  let needs := bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons
  have bounded : ∀ need ∈ needs, need.rank ≤ n := fun need member =>
    (pack.atomized_localNeeds need member).1
  have coveredNeeds : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms :=
    fun need member atom present => covered atom ((pack.atomized_localNeeds need member).2 atom present)
  have bodyClosed : (available.push needs).AtomClosed := Valuation.push_atomized_closed closed _
  have bodyAvailable : bodyFootprint.Available (available.push needs) := pack.available_atomized_localNeeds outsideAvailable
  have headCap : ∀ need ∈ (available.push needs) 0, Need.Fits key.input need := by
    intro need member
    exact ⟨bounded need member, coveredNeeds need member⟩
  let appQuery := uncastObservation rfl (inst_liftN_bvar B 0) observation
  let appLocation := uncastLocation rfl (inst_liftN_bvar B 0)
    (Located.lamBody (Located.expose (.here (root := .left original))))
  obtain ⟨request, rooted⟩ := appQuery.etaFunctionRequest appLocation henv hscoped formed
    bodyClosed bodyAvailable key headCap
  obtain ⟨functionQuery⟩ := request.originalFunctionQuery domainWF bodyWF (.done _) rooted
  let child := frame.bind (.left domain) domainCode domainAvailable guard.inputTyped
    (LambdaGuard.anchorRelated henv guard) needs bounded coveredNeeds
  have childSubstitutions : Ctx.SubstEq env U target (σ.cons key.anchor) (τ.cons key.anchor) (A :: source) :=
    .cons substitutions (domain.forget.defeq.mono below) (guard.path.cast guard.anchor.1)
  have pair := eta_lifted_function_pair domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain
    ordered (frame.dependencyEnvironment ordered)
  have liftedSmaller : (Closure.close (liftedTerm.dependencyOrigin ordered)
      (child.dependencyEnvironment ordered)).cost < limit := by
    change (Closure.close (liftedTerm.dependencyOrigin ordered)
      (.close (domain.dependencyOrigin ordered) (frame.dependencyEnvironment ordered) :: frame.dependencyEnvironment ordered)).cost < _
    omega
  obtain ⟨liftedAnswer⟩ := liftedF target (Locals.push locals) (σ.cons key.anchor) (τ.cons key.anchor)
    (available.push needs) child liftedSmaller bodyClosed formed childSubstitutions functionQuery request.resources
  obtain ⟨adapter⟩ := request.adapter henv hscoped formed rfl guard
    (by simpa only [subst, lift_subst_cons] using liftedAnswer.related)
  obtain ⟨unlifted⟩ := generatedEtaUnlift context domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain
    frame substitutions ordered henv below closed domainCode domainAvailable guard needs bounded coveredNeeds bodyClosed
    functionR functionQuery request.resources
  let input := unlifted.adaptRequest henv hscoped formed (Nat.succ_le_succ request.bound) adapter
  have termSmaller : (Closure.close (term.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost < limit := by omega
  obtain ⟨termAnswer⟩ := termF target locals σ τ available frame termSmaller closed formed substitutions input.observation input.resources
  have leftSmaller : (Closure.close ((EndpointRef.left original).expose.dependencyOrigin ordered)
      (frame.dependencyEnvironment ordered)).cost < limit := by
    rw [Derivation.dependencyOrigin.eq_def ordered (Derivation.eta domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain)]
    apply original_child_same_environment
    apply Origin.rule_child
    simp only [EndpointRef.expose, Derivation.expose, etaBody, EndpointState.dependencyOrigin_cast,
      EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin, dependencyEtaLeftOrigin, dependencyEtaBodyOrigin, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr trivial
  obtain ⟨leftAnswer⟩ := leftF target locals σ τ available frame leftSmaller closed formed substitutions
    (.lam domainWF bodyWF domainCode guard observation pack covered)
    (fun i need member => (List.mem_append.mp member).elim (domainAvailable i need) (outsideAvailable i need))
  have adapted := input.adapter.termMap henv hscoped formed
    (Profile.HasType.raise input.bound leftAnswer.typed) (leftAnswer.typeCode.raise henv input.bound) termAnswer.related
  have related : Related env U registry target (f.subst σ) (f.subst τ) ((VExpr.forallE A B).subst σ)
      (Profile.fn key output) leftAnswer.support := by
    simpa only [lower_raised] using Related.lower henv input.bound formed adapted
  have expanded := Related.etaExpand henv ((term.forget.defeq.mono below).substDF henv substitutions.wf formed substitutions) related
  let right := termAnswer.rightQuery.adaptRequest henv hscoped formed input.bound input.adapter
  let restored : RichGradedResult sourceEnv env U registry target (.ref (.right original)) locals τ available (Profile.fn key output) :=
    { right with observation := RichObs.changeReference (first := .left term) (second := .right original) rfl right.observation }
  refine ⟨{
    support := leftAnswer.support
    related := ?_
    rightQuery := restored
    typed := leftAnswer.typed
    typeCode := leftAnswer.typeCode }⟩
  change Related env U registry target ((VExpr.lam A (.app f.lift (.bvar 0))).subst σ)
    (f.subst τ) ((VExpr.forallE A B).subst σ) (Profile.fn key output) leftAnswer.support
  rw [eta_subst]
  exact expanded

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
