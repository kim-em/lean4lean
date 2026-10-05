import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionQuery
import Lean4Lean.Theory.Typing.AnchoredOriginalTailFundamental
import Lean4Lean.Theory.Typing.AnchoredOriginalCoherenceContract
import Lean4Lean.Theory.Typing.AnchoredSourceProjection

/-! A finite projection-query constructor indexed by its actual original
endpoint. Unlike an endpoint tag on Obs, it retains the exact field-domain
alignment and field certificate needed by the projection producer. The
original projDF step constructs this metadata on the other major. A whole
cut reindexes its field certificate before reflecting the source prefix.

This is an isolated query-constructor pilot. It does not claim that all
current Obs values can be annotated, or that constructor/eta field queries
already produce its input metadata.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- This query node uses the endpoint's actual assigned type, not a freely
chosen source field type. Its major observation and complete alignment are
finite syntax/evidence retained for the next source projection step. -/
structure OriginalProjectionMetadata
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (node : EndpointState sourceEnv U source (.proj name index major) assigned)
    (locals : List Nat) (σ : Subst) (demand : RecordData (Profile n))
    (request : DataRequest (Profile n)) where
  packet : ProjectionObservation env U registry target locals σ major assigned demand index request
  name_eq : demand.family.name = name

/-- The actual original rule transports the full projection metadata even
when both displayed majors differ from its stored source major. Only its
three fixed original children supply semantic induction clauses. -/
theorem OriginalProjectionMetadata.projDF
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {name : Name} {index : Nat} {info : VProjectionInfo}
    {levels : List VLevel} {parameters indices : List VExpr}
    {sourceMajor leftMajor rightMajor fieldType : VExpr} {fieldLevel : VLevel}
    (registered : sourceEnv.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : parameters.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels parameters index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : Derivation sourceEnv U source fieldType fieldType (.sort fieldLevel))
    (left : Derivation sourceEnv U source sourceMajor leftMajor
      (mkApps (.const name levels) (parameters ++ indices)))
    (right : Derivation sourceEnv U source sourceMajor rightMajor
      (mkApps (.const name levels) (parameters ++ indices)))
    (ctorClosed : info.ctorType.Closed)
    (relevance : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    {demand : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (query : OriginalProjectionMetadata env registry target
      (.proj registered levelsWF levelCount parameterCount indexCount selected fieldWF
        (.ref (.left field)) left ctorClosed relevance) locals σ demand request)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (context : ContextDerivation sourceEnv U source)
    (tails : TailPairedFits env registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fieldFundamental : StateFundamental env registry context (.ref (.left field)))
    (leftFundamental : DerivationFundamental env registry context left)
    (rightFundamental : DerivationFundamental env registry context right)
    (majorAvailable : query.packet.majorFootprint.Available available)
    (fieldAvailable : query.packet.fieldFootprint.Available available) :
    ∃ next : OriginalProjectionMetadata env registry target
        (.proj registered levelsWF levelCount parameterCount indexCount selected fieldWF
          (.ref (.left field)) right ctorClosed relevance) locals τ demand request,
      next.packet.support = query.packet.support ∧
      next.packet.majorFootprint.Available available ∧
      next.packet.fieldFootprint.Available available ∧
      Related env U registry target ((VExpr.proj name index leftMajor).subst σ)
        ((VExpr.proj name index rightMajor).subst τ) (fieldType.subst σ)
        request.input query.packet.support := by
  have leftAnswers := leftFundamental target locals σ σ available closed formed
    substitutions.left tails.left
  have rightAnswers := rightFundamental target locals σ τ available closed formed
    substitutions tails
  have majors : GradedTransfer env U registry target locals σ τ available leftMajor rightMajor
      (mkApps (.const name levels) (parameters ++ indices)) :=
    GradedTransfer.trans henv hscoped formed leftAnswers.2.1 rightAnswers.1
  obtain ⟨majorResult⟩ := majors query.packet.majorObservation majorAvailable
  obtain ⟨majorFootprint, ⟨majorObservation⟩, majorResources⟩ :=
    majorResult.observation.record_of_adapter henv majorResult.bound majorResult.adapter
      majorResult.resultAvailable closed
  have fieldTransfer : GradedTransfer env U registry target locals σ τ available
      fieldType fieldType (.sort fieldLevel) :=
    (fieldFundamental target locals σ τ available closed formed substitutions tails).1
  obtain ⟨fieldResult⟩ := query.packet.fieldCertificate.transfer_graded henv hscoped formed
    closed fieldTransfer fieldAvailable
  have fieldEq : env.IsDefEq U target (fieldType.subst σ) (fieldType.subst τ) (.sort fieldLevel) := by
    simpa only [subst] using (field.forget.defeq.mono below).substDF henv
      substitutions.wf formed substitutions
  let next : ProjectionObservation env U registry target locals τ rightMajor fieldType demand index request := {
    member := query.packet.member
    majorFootprint := majorFootprint
    majorObservation := majorObservation
    support := query.packet.support
    fieldFootprint := fieldResult.footprint
    fieldCertificate := fieldResult.certificate
    typed := query.packet.typed
    alignment := query.packet.alignment.trans (.step (.single fieldEq) query.packet.typed
      query.packet.fieldCertificate.formed fieldResult.related (.refl _)) }
  have fields := (majorResult.requestedRelated henv formed).projectRecord
    henv hscoped formed query.packet.member
  have related := query.packet.alignment.related henv query.packet.typed
    fieldResult.related.left_diagonal fields
  exact ⟨⟨next, query.name_eq⟩, rfl, majorResources, fieldResult.available,
    by simpa only [query.name_eq, subst] using related⟩

private theorem projection_reflected_available
    {before after : Footprint} {full base : Valuation}
    (resources : before.Available full)
    (same : before = after.sourceLift (.skipN .refl depth))
    (tail : ∀ index, full (index + depth) = base index) :
    after.Available base := by
  intro index need member
  rw [← tail index]
  apply resources (index + depth) need
  rw [same]
  exact List.mem_map.mpr ⟨(index, need), member,
    by simp only [Lift.liftVar_skipN, Lift.liftVar]⟩

/-- Retain and reconstruct the typed projection node at a whole cut. The
old assigned field type may depend on the removed source binders. Its exact
certificate is compared first; only the displayed destination certificate
and the major observation are reflected. No canonical projection typing is
created and no reflection property of the old field type is assumed. -/
theorem OriginalProjectionMetadata.reindexReflect
    {sourceEnv argumentEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {origin : CutOriginAt root boundary (.proj name index major) baseDepth}
    {registry : CanonicalHead.Registry} {target : List VExpr} {locals baseLocals : List Nat}
    {fullRealization σ : Subst} {fullAvailable available : Valuation}
    {demand : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (query : OriginalProjectionMetadata env registry target
      (origin.view.cast origin.expression_eq rfl) locals fullRealization demand request)
    (argument : EndpointState argumentEnv U argumentSource (.proj name index major) argumentType)
    (realizationTail : Subst.lift_l (.skipN .refl origin.depth) fullRealization = σ)
    (availableTail : ∀ index, fullAvailable (index + origin.depth) = available index)
    (majorAvailable : query.packet.majorFootprint.Available fullAvailable)
    (types : CodeTransferResult env U registry target locals fullRealization fullRealization
      fullAvailable origin.type (argumentType.lift' (.skipN .refl origin.depth)) query.packet.support)
    (path : TypeConversion env U target (origin.type.subst fullRealization)
      ((argumentType.lift' (.skipN .refl origin.depth)).subst fullRealization)) :
    ∃ next : OriginalProjectionMetadata env registry target argument baseLocals σ demand request,
      next.packet.support = query.packet.support ∧
      next.packet.majorFootprint.Available available ∧
      next.packet.fieldFootprint.Available available := by
  obtain ⟨majorFootprint, ⟨majorObservation⟩, majorEq⟩ :=
    query.packet.majorObservation.reflectSource (.skipN .refl origin.depth) rfl baseLocals
  obtain ⟨fieldFootprint, ⟨fieldCertificate⟩, fieldEq⟩ :=
    types.certificate.reflectSource (.skipN .refl origin.depth) rfl baseLocals
  rw [realizationTail] at majorObservation fieldCertificate
  have bridge : DomainChain env U registry target request.input
      (origin.type.subst fullRealization) (argumentType.subst σ) := by
    apply DomainChain.step (support := query.packet.support)
      (by simpa only [subst_lift', realizationTail] using path)
      query.packet.typed query.packet.fieldCertificate.formed
      (by simpa only [subst_lift', realizationTail] using types.related)
      (.refl _)
  exact ⟨⟨{
      member := query.packet.member
      majorFootprint := majorFootprint
      majorObservation := majorObservation
      support := query.packet.support
      fieldFootprint := fieldFootprint
      fieldCertificate := fieldCertificate
      typed := query.packet.typed
      alignment := query.packet.alignment.trans bridge }, query.name_eq⟩,
    rfl, projection_reflected_available majorAvailable majorEq availableTail,
    projection_reflected_available types.available fieldEq availableTail⟩

/-- Consume the actual two-display coherence answer. Its destination
certificate is already at the unweakened original argument context; only
the major observation needs reflection. This is the returned metadata
interface used by the current display-indexed mutual contract. -/
theorem OriginalProjectionMetadata.reindexFromCoherence
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {origin : CutOriginAt root boundary (.proj name index major) 0}
    {registry : CanonicalHead.Registry} {target : List VExpr} {locals baseLocals : List Nat}
    {fullRealization σ : Subst} {fullAvailable available : Valuation}
    {demand : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (query : OriginalProjectionMetadata env registry target
      (origin.view.cast origin.expression_eq rfl) locals fullRealization demand request)
    (rootContext : ContextDerivation sourceEnv U rootSource)
    (argumentContext : ContextDerivation sourceEnv U (boundary ++ rootSource))
    (argument : EndpointState sourceEnv U (boundary ++ rootSource)
      (.proj name index major) argumentType)
    (argumentProvenance : EndpointProvenance argumentContext argument)
    (realizationTail : Subst.lift_l (.skipN .refl origin.depth) fullRealization = σ)
    (availableTail : ∀ index, fullAvailable (index + origin.depth) = available index)
    (majorAvailable : query.packet.majorFootprint.Available fullAvailable)
    (fieldAvailable : query.packet.fieldFootprint.Available fullAvailable)
    (coherence : DisplayCoherenceAnswer env registry target
      (origin.sourceDisplay rootContext) (origin.argumentDisplay argumentContext argument argumentProvenance)
      fullRealization fullAvailable locals baseLocals) :
    ∃ next : OriginalProjectionMetadata env registry target argument baseLocals σ demand request,
      next.packet.support = query.packet.support ∧
      next.packet.majorFootprint.Available available ∧
      next.packet.fieldFootprint.Available available := by
  have originalCertificate : CodeCert env U registry target locals
      ((origin.sourceDisplay rootContext).sourceSubst fullRealization)
      (origin.sourceDisplay rootContext).sourceType query.packet.support query.packet.fieldFootprint := by
    simpa only [CutOriginAt.sourceDisplay, EndpointDisplay.identity,
      EndpointDisplay.sourceSubst, Subst.lift_l_refl] using query.packet.fieldCertificate
  obtain ⟨types⟩ := coherence.queries originalCertificate fieldAvailable
  obtain ⟨majorFootprint, ⟨majorObservation⟩, majorEq⟩ :=
    query.packet.majorObservation.reflectSource (.skipN .refl origin.depth) rfl baseLocals
  rw [realizationTail] at majorObservation
  have destinationCertificate : CodeCert env U registry target baseLocals σ argumentType
      query.packet.support types.footprint := by
    simpa only [EndpointDisplay.sourceSubst, CutOriginAt.argumentDisplay,
      realizationTail] using types.certificate
  have destinationResources : types.footprint.Available available := by
    intro slot need member
    have present := types.available slot need member
    simpa only [EndpointDisplay.sourceValuation, CutOriginAt.argumentDisplay,
      Lift.liftVar_skipN, Lift.liftVar, availableTail] using present
  have bridge : DomainChain env U registry target request.input
      (origin.type.subst fullRealization) (argumentType.subst σ) := by
    apply DomainChain.step (support := query.packet.support)
      (by simpa only [subst_lift', realizationTail] using coherence.path)
      query.packet.typed query.packet.fieldCertificate.formed
      (by simpa only [EndpointDisplay.sourceSubst, CutOriginAt.sourceDisplay,
        EndpointDisplay.identity, Subst.lift_l_refl, CutOriginAt.argumentDisplay,
        realizationTail] using types.related)
      (.refl _)
  exact ⟨⟨{
      member := query.packet.member
      majorFootprint := majorFootprint
      majorObservation := majorObservation
      support := query.packet.support
      fieldFootprint := types.footprint
      fieldCertificate := destinationCertificate
      typed := query.packet.typed
      alignment := query.packet.alignment.trans bridge }, query.name_eq⟩,
    rfl, projection_reflected_available majorAvailable majorEq availableTail,
    destinationResources⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
