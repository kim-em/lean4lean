import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedCode
import Lean4Lean.Theory.Typing.AnchoredRecordProjection
import Lean4Lean.Theory.Typing.AnchoredSourceRecordExtraction

/-! A finite source projection packet retains its actual major observation
and a source certificate for the field type. The frozen field domain is
connected to that source type by a concrete finite conversion chain. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure ProjectionObservation (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (realization : Subst)
    (major fieldType : VExpr) (demand : RecordData (Profile n))
    (index : Nat) (request : DataRequest (Profile n)) where
  member : (index, request) ∈ demand.fields
  majorFootprint : Footprint
  majorObservation : Obs env U registry target locals realization major
    (Profile.singleton (n := n + 1) (.record demand)) majorFootprint
  support : Profile n
  fieldFootprint : Footprint
  fieldCertificate : CodeCert env U registry target locals realization fieldType support fieldFootprint
  typed : request.input.HasType support
  alignment : DomainChain env U registry target request.input request.domain (fieldType.subst realization)

noncomputable def ProjectionObservation.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {target future : List VExpr} {ρ : Lift}
    (route : FutureInsertion env U target future ρ)
    {locals : List Nat} {σ : Subst} {major fieldType : VExpr}
    {demand : RecordData (Profile n)} {index : Nat} {request : DataRequest (Profile n)}
    (node : ProjectionObservation env U registry target locals σ major fieldType demand index request) :
    ProjectionObservation env U registry future locals (σ.lift_r ρ) major fieldType
      (demand.rename ρ) index (request.rename ρ) where
  member := List.mem_map.mpr ⟨(index, request), node.member, rfl⟩
  majorFootprint := Footprint.rename ρ node.majorFootprint
  majorObservation := by
    simpa only [Profile.rename_singleton, Atom.rename_record, RecordData.rename] using
      node.majorObservation.future henv route
  support := node.support.rename ρ
  fieldFootprint := Footprint.rename ρ node.fieldFootprint
  fieldCertificate := node.fieldCertificate.future henv route
  typed := Profile.rename_hasType_iff.mpr node.typed
  alignment := by
    simpa only [lift'_subst, DataRequest.rename, DataRequest.map, KeyData.map] using
      node.alignment.future henv route

/-- The projection's semantic result uses only the original major and field
formation children. Restoring the major's requested grade is checked before
extracting its lower-rank field, and the source field certificate is retained. -/
theorem ProjectionObservation.interpret
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {major other majorType fieldType : VExpr}
    {fieldLevel : VLevel} {demand : RecordData (Profile n)}
    {index : Nat} {request : DataRequest (Profile n)}
    (node : ProjectionObservation env U registry target locals σ major fieldType demand index request)
    (originalMajor : GradedJoint env U registry source major other majorType)
    (originalField : GradedJoint env U registry source fieldType fieldType (.sort fieldLevel))
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits env U registry source target locals σ τ available)
    (majorAvailable : node.majorFootprint.Available available)
    (fieldAvailable : node.fieldFootprint.Available available) :
    Related env U registry target ((VExpr.proj demand.family.name index major).subst σ)
      ((VExpr.proj demand.family.name index other).subst τ) (fieldType.subst σ)
      request.input node.support := by
  obtain ⟨majorResult⟩ :=
    (originalMajor target locals σ τ available closed formed substitutions fits).1
      node.majorObservation majorAvailable
  have fields := (majorResult.requestedRelated henv formed).projectRecord
    henv hscoped formed node.member
  obtain ⟨fieldResult⟩ := node.fieldCertificate.transfer_graded henv hscoped formed closed
    (originalField target locals σ σ available closed formed substitutions.left fits.left).1
    fieldAvailable
  exact node.alignment.related henv node.typed fieldResult.related fields

/-- Replay the concrete projection packet on the other source endpoint.
The returned major observation comes from the original major child, and the
field certificate comes from the original field formation child. -/
theorem ProjectionObservation.transfer
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {major other majorType fieldType : VExpr}
    {fieldLevel : VLevel} {demand : RecordData (Profile n)}
    {index : Nat} {request : DataRequest (Profile n)}
    (node : ProjectionObservation env U registry target locals σ major fieldType demand index request)
    (originalMajor : GradedJoint env U registry source major other majorType)
    (originalField : GradedJoint env U registry source fieldType fieldType (.sort fieldLevel))
    (fieldFormation : env.HasType U source fieldType (.sort fieldLevel))
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits env U registry source target locals σ τ available)
    (majorAvailable : node.majorFootprint.Available available)
    (fieldAvailable : node.fieldFootprint.Available available) :
    ∃ next : ProjectionObservation env U registry target locals τ other fieldType demand index request,
      next.support = node.support ∧ next.majorFootprint.Available available ∧
      next.fieldFootprint.Available available ∧
      Related env U registry target ((VExpr.proj demand.family.name index major).subst σ)
        ((VExpr.proj demand.family.name index other).subst τ) (fieldType.subst σ)
        request.input node.support := by
  obtain ⟨majorResult⟩ :=
    (originalMajor target locals σ τ available closed formed substitutions fits).1
      node.majorObservation majorAvailable
  obtain ⟨majorFootprint, ⟨majorObservation⟩, majorResources⟩ :=
    majorResult.observation.record_of_adapter henv majorResult.bound majorResult.adapter
      majorResult.resultAvailable closed
  obtain ⟨fieldResult⟩ := node.fieldCertificate.transfer_graded henv hscoped formed closed
    (originalField target locals σ τ available closed formed substitutions fits).1 fieldAvailable
  have fieldEq : env.IsDefEq U target (fieldType.subst σ) (fieldType.subst τ) (.sort fieldLevel) := by
    simpa only [subst] using fieldFormation.substDF henv substitutions.wf formed substitutions
  let next : ProjectionObservation env U registry target locals τ other fieldType demand index request := {
    member := node.member
    majorFootprint := majorFootprint
    majorObservation := majorObservation
    support := node.support
    fieldFootprint := fieldResult.footprint
    fieldCertificate := fieldResult.certificate
    typed := node.typed
    alignment := node.alignment.trans (.step (.single fieldEq) node.typed
      node.fieldCertificate.formed fieldResult.related (.refl _)) }
  refine ⟨next, rfl, majorResources, fieldResult.available, ?_⟩
  have fields := (majorResult.requestedRelated henv formed).projectRecord
    henv hscoped formed node.member
  exact node.alignment.related henv node.typed fieldResult.related.left_diagonal fields

end Lean4Lean.AnchoredSource.Adapted
