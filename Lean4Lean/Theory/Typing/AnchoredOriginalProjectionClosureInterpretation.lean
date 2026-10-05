import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionClosure
import Lean4Lean.Theory.Typing.AnchoredOriginalSortablePrefix
import Lean4Lean.Theory.Typing.AnchoredSortableInstantiation
import Lean4Lean.Theory.Typing.AnchoredSortableScope
import Lean4Lean.Theory.Typing.AnchoredSortablePiExtraction
import Lean4Lean.Theory.Typing.AnchoredSourceProjection

/-! Semantic interpretation of a retained projected leaf. The major and
field queries in this first interpreter belong to the checked hereditary
grammar; the projected value is retained as a source suspension. Every
semantic call names the actual original argument, major, field, or conversion
child. No interpretation of a synthesized projection is assumed.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

structure ProjectionValue (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (expression assigned : VExpr) (demand support : Profile n) where
  footprint : Footprint
  certificate : SortableCert env U registry target locals σ assigned true support footprint
  resources : footprint.Available available
  typed : demand.HasType support
  code : TypeRelated env U registry target (assigned.subst σ) (assigned.subst σ) support
  related : Related env U registry target (expression.subst σ) (expression.subst σ)
    (assigned.subst σ) demand support

/-- Interpret a primitive projected query and restore the actual assigned
type through its original conversion prefix. The field code starts at the
head's actual formation child, so its type is never silently identified with
the ambient assigned type. -/
theorem interpretProjection
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead node)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (context : ContextDerivation sourceEnv U source)
    (calls : PrefixCall.HereditaryFundamentals env registry head.route context)
    (majorF : DerivationHereditaryFundamental env registry context head.major)
    (fieldF : StateSortableFundamental env registry context head.field)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : SortableTailPairedFits env registry target context locals σ σ available)
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (majorQuery : SortableObs env U registry target locals σ major
      (.singleton (n := n + 1) (.record record)) majorFootprint)
    (fieldCode : SortableCert env U registry target locals σ head.fieldType true support fieldFootprint)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain (head.fieldType.subst σ))
    (majorResources : majorFootprint.Available available)
    (fieldResources : fieldFootprint.Available available) :
    Nonempty (ProjectionValue env U registry target locals σ available
      (.proj name index major) assigned request.input support) := by
  have rightF := HereditaryTailJoint.left henv hscoped (HereditaryTailJoint.symm majorF)
  obtain ⟨majorAnswer⟩ := (rightF target locals σ σ available closed formed substitutions tails).1
    majorQuery majorResources
  obtain ⟨fieldAnswer⟩ := fieldF target locals σ σ available closed formed substitutions tails
    fieldCode fieldResources
  obtain ⟨assignedAnswer⟩ := head.route.restoreSortableOriginal henv hscoped below context
    closed formed substitutions tails.forward calls fieldAnswer.toSortableTransferResult
  have fields := (majorAnswer.requestedRelated henv formed).projectRecord henv hscoped formed member
  have natural : Related env U registry target ((VExpr.proj name index major).subst σ)
      ((VExpr.proj name index major).subst σ) (head.fieldType.subst σ) request.input support := by
    simpa only [nameEq, subst] using alignment.related henv typed fieldAnswer.related fields
  exact ⟨{
    footprint := assignedAnswer.footprint
    certificate := assignedAnswer.certificate
    resources := assignedAnswer.available
    typed := typed
    code := (assignedAnswer.related.symm henv typed.wf_type).left_diagonal
    related := Related.convert henv typed assignedAnswer.related natural }⟩

/-- A known beta argument constructs the exact original source tail needed
by the retained projection template. Its assigned-type certificate comes
from that argument's actual F answer. -/
theorem interpretProjectionInst
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A argumentExpression major assigned : VExpr} {domainLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (argument : EndpointRef sourceEnv U source argumentExpression A)
    (template : EndpointRef sourceEnv U (A :: source) (.proj name index major) assigned)
    (head : ProjectionHead (.ref template))
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (argumentF : StateHereditaryFundamental env registry context (.ref argument))
    (calls : PrefixCall.HereditaryFundamentals env registry head.route (.cons context domain))
    (majorF : DerivationHereditaryFundamental env registry (.cons context domain) head.major)
    (fieldF : StateSortableFundamental env registry (.cons context domain) head.field)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : SortableTailPairedFits env registry target context locals σ σ available)
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    {input packed : Profile captureRank} {support : Profile n}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (majorQuery : SortableObs env U registry target (Locals.push locals)
      (σ.cons (argumentExpression.subst σ)) major
      (.singleton (n := n + 1) (.record record)) majorFootprint)
    (fieldCode : SortableCert env U registry target (Locals.push locals)
      (σ.cons (argumentExpression.subst σ)) head.fieldType true support fieldFootprint)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain
      (head.fieldType.subst (σ.cons (argumentExpression.subst σ))))
    (pack : BinderPack captureRank packed (majorFootprint ++ fieldFootprint) outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ input.atoms)
    (outsideResources : outside.Available available)
    (argumentQuery : SortableObs env U registry target locals σ argumentExpression input argumentFootprint)
    (argumentResources : argumentFootprint.Available available) :
    Nonempty (ProjectionValue env U registry target locals σ available
      ((VExpr.proj name index major).inst argumentExpression) (assigned.inst argumentExpression)
      request.input support) := by
  obtain ⟨answer⟩ := argumentF target locals σ σ available closed formed substitutions tails
    argumentQuery argumentResources
  have arguments := answer.requestedRelated henv formed
  let needs := (majorFootprint ++ fieldFootprint).localNeeds ++
    (majorFootprint ++ fieldFootprint).localNeeds.flatMap Need.singletons
  have bounded : ∀ need ∈ needs, need.rank ≤ captureRank := fun need member =>
    (pack.atomized_localNeeds need member).1
  have included : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade captureRank).atoms, atom ∈ input.atoms :=
    fun need member atom present => covered atom ((pack.atomized_localNeeds need member).2 atom present)
  let fitted := tails.pushCertificates domain answer.requestedCertificate answer.requestedCertificate
    answer.typeAvailable answer.typeAvailable answer.requestedTyped answer.requestedTyped
    arguments arguments needs bounded included
  have rawArgument := (argument.sound.defeq.mono below).substDF henv substitutions.wf formed substitutions
  have instantiated : Ctx.SubstEq env U target (σ.cons (argumentExpression.subst σ))
      (σ.cons (argumentExpression.subst σ)) (A :: source) :=
    .cons substitutions (domain.sound.defeq.mono below) rawArgument
  have localClosed := Valuation.push_atomized_closed closed (majorFootprint ++ fieldFootprint).localNeeds
  have resources := pack.available_atomized_localNeeds outsideResources
  obtain ⟨value⟩ := interpretProjection head henv hscoped below (.cons context domain) calls majorF fieldF
    localClosed formed instantiated fitted nameEq member majorQuery fieldCode typed alignment
    (fun index need member => resources index need (List.mem_append_left _ member))
    (fun index need member => resources index need (List.mem_append_right _ member))
  obtain ⟨nextPacked, nextOutside, nextPack, nextCovered, nextResources⟩ :=
    Footprint.pack_available value.resources bounded included
  obtain ⟨typeLevel, typeFormation⟩ := (template.sound.defeq.mono below).isType henv instantiated.wf
  have typeScope := typeFormation.closedN henv (CtxWF.closed henv instantiated.wf)
  have nextLive := tails.forward.leavesLive henv hscoped formed nextResources
    (nextPack.scoped (value.certificate.scoped typeScope))
  obtain ⟨typeResult⟩ := value.certificate.instantiate henv hscoped formed closed
    answer.toSortableGradedResult nextPack nextCovered nextResources nextLive
  exact ⟨{
    footprint := typeResult.footprint
    certificate := typeResult.certificate
    resources := typeResult.resources
    typed := typed
    code := by simpa only [subst_inst, inst_lift_cons] using value.code
    related := by simpa only [subst_inst, inst_lift_cons] using value.related }⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
