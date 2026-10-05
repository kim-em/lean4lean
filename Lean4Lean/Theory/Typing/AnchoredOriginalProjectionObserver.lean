import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionMetadata
import Lean4Lean.Theory.Typing.AnchoredRecordRequestRetag

/-! Isolated source projection syntax with hereditary returned metadata.
The primitive constructor retains an exact field certificate and domain
chain at the actual original endpoint. Union, finite views and grade raising
preserve that constructor rather than erasing it into legacy Obs (which has
no primitive projection constructor).
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

inductive ProjectionObs (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (node : EndpointState sourceEnv U source (.proj name index major) assigned)
    (locals : List Nat) (σ : Subst) : {n : Nat} → Profile n → Footprint → Type where
  | field {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
      (nameEq : record.family.name = name)
      (member : (index, request) ∈ record.fields)
      (majorObservation : Obs env U registry target locals σ major
        (.singleton (n := n + 1) (.record record)) majorFootprint)
      (fieldCertificate : CodeCert env U registry target locals σ assigned support fieldFootprint)
      (typed : request.input.HasType support)
      (alignment : DomainChain env U registry target request.input request.domain (assigned.subst σ)) :
      ProjectionObs env registry target node locals σ request.input (majorFootprint ++ fieldFootprint)
  | empty : ProjectionObs env registry target node locals σ (n := n) .empty []
  | union
      (left : ProjectionObs env registry target node locals σ leftDemand leftFootprint)
      (right : ProjectionObs env registry target node locals σ rightDemand rightFootprint) :
      ProjectionObs env registry target node locals σ (leftDemand.union rightDemand)
        (leftFootprint ++ rightFootprint)
  | view
      (child : ProjectionObs env registry target node locals σ (.singleton first) footprint)
      (change : AtomView env U registry target first second) :
      ProjectionObs env registry target node locals σ (.singleton second) footprint
  | unpad {demand : Profile n}
      (child : ProjectionObs env registry target node locals σ demand.pad footprint) :
      ProjectionObs env registry target node locals σ demand footprint
  | raise {demand : Profile n} (child : ProjectionObs env registry target node locals σ demand footprint)
      (bound : n ≤ N) :
      ProjectionObs env registry target node locals σ (raiseProfile N bound (demand : Profile n)) footprint

/-- The finite constructor payload of the actual original projDF rule. -/
structure OriginalProjectionRule (sourceEnv : VEnv) (U : Nat) (source : List VExpr)
    (name : Name) (index : Nat) (leftMajor rightMajor fieldType : VExpr) where
  info : VProjectionInfo
  registered : sourceEnv.projections name info
  levels : List VLevel
  levelsWF : ∀ level ∈ levels, level.WF U
  levelCount : levels.length = info.uvars
  parameters : List VExpr
  parameterCount : parameters.length = info.nparams
  indices : List VExpr
  indexCount : indices.length = info.nindices
  sourceMajor : VExpr
  selected : info.fieldType name levels parameters index sourceMajor = some fieldType
  fieldLevel : VLevel
  fieldWF : fieldLevel.WF U
  field : Derivation sourceEnv U source fieldType fieldType (.sort fieldLevel)
  left : Derivation sourceEnv U source sourceMajor leftMajor
    (mkApps (.const name levels) (parameters ++ indices))
  right : Derivation sourceEnv U source sourceMajor rightMajor
    (mkApps (.const name levels) (parameters ++ indices))
  ctorClosed : info.ctorType.Closed
  relevance : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero

def OriginalProjectionRule.leftNode
    (rule : OriginalProjectionRule sourceEnv U source name index leftMajor rightMajor fieldType) :=
  EndpointState.proj rule.registered rule.levelsWF rule.levelCount rule.parameterCount
    rule.indexCount rule.selected rule.fieldWF (.ref (.left rule.field)) rule.left
    rule.ctorClosed rule.relevance

def OriginalProjectionRule.rightNode
    (rule : OriginalProjectionRule sourceEnv U source name index leftMajor rightMajor fieldType) :=
  EndpointState.proj rule.registered rule.levelsWF rule.levelCount rule.parameterCount
    rule.indexCount rule.selected rule.fieldWF (.ref (.left rule.field)) rule.right
    rule.ctorClosed rule.relevance

structure ProjectionTransferResult
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (rule : OriginalProjectionRule sourceEnv U source name index leftMajor rightMajor fieldType)
    (locals : List Nat) (σ τ : Subst) (available : Valuation) (demand : Profile n) where
  footprint : Footprint
  observation : ProjectionObs env registry target rule.rightNode locals τ demand footprint
  resources : footprint.Available available
  support : Profile n
  typeFootprint : Footprint
  certificate : CodeCert env U registry target locals σ fieldType support typeFootprint
  typeAvailable : typeFootprint.Available available
  typed : demand.HasType support
  typeCode : TypeRelated env U registry target (fieldType.subst σ) (fieldType.subst σ) support
  related : Related env U registry target ((VExpr.proj name index leftMajor).subst σ)
    ((VExpr.proj name index rightMajor).subst τ) (fieldType.subst σ) demand support

private theorem projection_code_union
    (left : TypeRelated env U registry target A A p)
    (right : TypeRelated env U registry target A A q) :
    TypeRelated env U registry target A A (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom member
  exact (List.mem_append.mp member).elim
    (fun h => left.singleton h) (fun h => right.singleton h)

/-- Interpret the new source constructor with only its actual three
original children. Every returned branch retains its typed projection
metadata, including after union, view adaptation and grade raising. -/
theorem ProjectionObs.projDF
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ τ : Subst}
    {available : Valuation}
    (rule : OriginalProjectionRule sourceEnv U source name index leftMajor rightMajor fieldType)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (context : ContextDerivation sourceEnv U source)
    (tails : TailPairedFits env registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fieldFundamental : StateFundamental env registry context (.ref (.left rule.field)))
    (leftFundamental : DerivationFundamental env registry context rule.left)
    (rightFundamental : DerivationFundamental env registry context rule.right)
    (query : ProjectionObs env registry target rule.leftNode locals σ demand footprint)
    (resources : footprint.Available available) :
    Nonempty (ProjectionTransferResult env registry target rule locals σ τ available demand) := by
  induction query with
  | field nameEq member majorObservation fieldCertificate typed alignment =>
    let metadata : OriginalProjectionMetadata env registry target rule.leftNode locals σ _ _ :=
      ⟨⟨member, _, majorObservation, _, _, fieldCertificate, typed, alignment⟩, nameEq⟩
    have majorResources := fun i need member => resources i need (List.mem_append_left _ member)
    have fieldResources := fun i need member => resources i need (List.mem_append_right _ member)
    obtain ⟨next, supportEq, nextMajor, nextField, related⟩ := metadata.projDF
      rule.registered rule.levelsWF rule.levelCount rule.parameterCount rule.indexCount
      rule.selected rule.fieldWF rule.field rule.left rule.right rule.ctorClosed rule.relevance
      henv hscoped below closed formed context tails substitutions
      fieldFundamental leftFundamental rightFundamental majorResources fieldResources
    have fieldTransfer : GradedTransfer env U registry target locals σ σ available
        fieldType fieldType (.sort rule.fieldLevel) :=
      (fieldFundamental target locals σ σ available closed formed substitutions.left tails.left).1
    obtain ⟨code⟩ := fieldCertificate.transfer_graded henv hscoped formed closed fieldTransfer fieldResources
    exact ⟨{
      footprint := next.packet.majorFootprint ++ next.packet.fieldFootprint
      observation := .field next.name_eq next.packet.member next.packet.majorObservation
        next.packet.fieldCertificate next.packet.typed next.packet.alignment
      resources := fun i need member => (List.mem_append.mp member).elim
        (nextMajor i need) (nextField i need)
      support := _, typeFootprint := _, certificate := fieldCertificate
      typeAvailable := fieldResources, typed := typed, typeCode := code.related
      related := related }⟩
  | @empty n =>
    exact ⟨{
      footprint := [], observation := .empty, resources := fun _ _ member => nomatch member
      support := .empty, typeFootprint := []
      certificate := .seed .empty (Profile.HasType.empty (Profile.WF.sort true))
      typeAvailable := fun _ _ member => nomatch member
      typed := Profile.HasType.empty Profile.WF.empty
      typeCode := by cases n <;> intro Δ ρ future atom member <;> cases member
      related := by cases n <;> intro atom member <;> cases member }⟩
  | union left right ihLeft ihRight =>
    obtain ⟨first⟩ := ihLeft (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨second⟩ := ihRight (fun i need member => resources i need (List.mem_append_right _ member))
    have wf := first.typed.wf_type.union second.typed.wf_type
    have code := projection_code_union first.typeCode second.typeCode
    have leftTyped := first.typed.enlarge (Profile.le_union_left _ _) wf
    have rightTyped := second.typed.enlarge (Profile.le_union_right _ _) wf
    exact ⟨{
      footprint := first.footprint ++ second.footprint
      observation := .union first.observation second.observation
      resources := fun i need member => (List.mem_append.mp member).elim
        (first.resources i need) (second.resources i need)
      support := first.support.union second.support
      typeFootprint := first.typeFootprint ++ second.typeFootprint
      certificate := .union first.certificate second.certificate
      typeAvailable := fun i need member => (List.mem_append.mp member).elim
        (first.typeAvailable i need) (second.typeAvailable i need)
      typed := leftTyped.union rightTyped, typeCode := code
      related := (first.related.retag henv leftTyped code).union
        (second.related.retag henv rightTyped code) }⟩
  | view child change ih =>
    obtain ⟨answer⟩ := ih resources
    exact ⟨{
      footprint := answer.footprint, observation := .view answer.observation change
      resources := answer.resources, support := change.mapType answer.support
      typeFootprint := answer.typeFootprint, certificate := .map change answer.certificate
      typeAvailable := answer.typeAvailable, typed := change.mapType_typed answer.typed
      typeCode := change.codeMap henv hscoped answer.typeCode
      related := change.termMap henv hscoped formed answer.related }⟩
  | unpad child ih =>
    obtain ⟨answer⟩ := ih resources
    exact ⟨{
      footprint := answer.footprint, observation := .unpad answer.observation
      resources := answer.resources, support := answer.support.down
      typeFootprint := answer.typeFootprint, certificate := .down answer.certificate
      typeAvailable := answer.typeAvailable, typed := answer.typed.pad_inv
      typeCode := answer.typeCode.down henv
      related := answer.related.unpad henv formed }⟩
  | raise child bound ih =>
    obtain ⟨answer⟩ := ih resources
    exact ⟨{
      footprint := answer.footprint, observation := .raise answer.observation bound
      resources := answer.resources, support := raiseProfile _ bound answer.support
      typeFootprint := answer.typeFootprint, certificate := answer.certificate.raise bound
      typeAvailable := answer.typeAvailable, typed := Profile.HasType.raise bound answer.typed
      typeCode := TypeRelated.raise henv bound answer.typeCode
      related := Related.raise henv bound answer.related }⟩

noncomputable def ProjectionObs.pad
    (query : ProjectionObs env registry target node locals σ (demand : Profile n) footprint) :
    ProjectionObs env registry target node locals σ demand.pad footprint := by
  simpa only [raiseProfile_step (Nat.le_refl n), raiseProfile_self] using
    ProjectionObs.raise query (Nat.le_succ n)

noncomputable def ProjectionObs.rowShift
    {key : Key n} {output : Atom n}
    (query : ProjectionObs env registry target node locals σ (Profile.fn key output) footprint) :
    ProjectionObs env registry target node locals σ (Profile.fn key.pad (.pad output)) footprint := by
  exact ProjectionObs.view query.pad (.commutePadFn key output)

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
