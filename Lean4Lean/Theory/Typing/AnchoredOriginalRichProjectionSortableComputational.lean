import Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionComputational
import Lean4Lean.Theory.Typing.AnchoredProjectionSortableOutput
import Lean4Lean.Theory.Typing.AnchoredFamilyLiteralArguments

/-! Paired F assembly for a sortable projection output. The field certificate
supports exactly the selected output; the frozen record request's raw domain
is not identified with the caller's assigned type. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

private theorem fullRecordAdmission
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (related : Related env U registry target left right assigned
      (Profile.singleton (n := n+1) (.record record)) support)
    (member : (index, request) ∈ record.fields) :
    RankedData.RequestAdmission env U (relations env U registry n) target request
      (.proj record.family.name index left) (.proj record.family.name index right) := by
  obtain ⟨witness⟩ := related.recordRelation henv hscoped formed target .refl (.refl formed)
  have rename : record.rename .refl = record := by
    unfold RecordData.rename
    rw [show (fun e : VExpr => e.lift' .refl) = id from funext (fun _ => lift'_refl),
      show Profile.rename (n := n) .refl = id from funext Profile.rename_refl,
      RecordData.map_id]
  simp only [lift'_refl, rename] at witness
  exact (witness.fields.map_member member).mixedBack henv hscoped witness.insertion

/-- Both semantic channels use the actual major/field answers. The original
field certificate remains the source assigned support, and the right observer
contains the actual returned major query and field certificate. -/
theorem RichComputationalValue.projectedSortable
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    (head : ProjectionHead node)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    {atom : Atom n} {output : Atom m}
    (selected : atom ∈ request.input.atoms)
    (path : GeneralOutputPath env U registry target atom output)
    (sortable : (Profile.singleton output).HasType (.sort relevant))
    (fieldCode : RichCert sourceEnv env U registry target head.field locals σ true support fieldFootprint)
    (fieldResources : fieldFootprint.Available available)
    (typed : (Profile.singleton output).HasType support)
    (majorAnswer : RichComputationalValue sourceEnv env U registry target (.ref (.right head.major))
      locals σ τ available (Profile.singleton (n := n + 1) (.record record)))
    (fieldAnswer : RichCodeTransferResult env U registry target head.field head.field
      locals σ τ available true support) :
    ∃ answer : RichComputationalValue sourceEnv env U registry target (projectionNatural head)
      locals σ τ available (Profile.singleton output),
      HEq answer.certificate fieldCode ∧
      (∀ current, answer.rightQuery.observation.nativeDepth current =
        max (majorAnswer.rightQuery.observation.nativeDepth current)
          (fieldAnswer.certificate.nativeDepth current)) := by
  obtain ⟨majorFootprint, majorQuery, majorResources, majorDepth⟩ :=
    majorAnswer.rightQuery.recordObservation_nativeDepth henv
  have admitted := fullRecordAdmission henv hscoped formed majorAnswer.related member
  have outputRelated := (admitted.sortableOutputRelated henv hscoped formed selected path
    sortable typed fieldAnswer.related.left_diagonal).2
  have related : Related env U registry target ((VExpr.proj name index value).subst σ)
      ((VExpr.proj name index value).subst τ) (head.fieldType.subst σ)
      (Profile.singleton output) support := by
    simpa only [nameEq, subst_proj] using outputRelated
  refine ⟨{
    support := support
    footprint := fieldFootprint
    certificate := fieldCode
    resources := fieldResources
    typed := typed
    related := related
    typeCode := fieldAnswer.related.left_diagonal
    rightQuery := {
      rank := m
      bound := Nat.le_refl _
      raw := .singleton output
      footprint := majorFootprint ++ fieldAnswer.footprint
      observation := .projectionSortable (naturalProjectionHead head) nameEq member majorQuery
        selected path sortable fieldAnswer.certificate typed
      adapter := ?_
      resources := fun i need hm => (List.mem_append.mp hm).elim
        (majorResources i need) (fieldAnswer.resources i need)
      live := related.live henv hscoped formed } }, HEq.rfl, ?_⟩
  · simpa only [raiseProfile_self] using
      (show GeneralNormalProfileAdapter env U registry target (.singleton output) (.singleton output) from .refl _)
  · intro current
    simp only [RichObs.nativeDepth, majorDepth]

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
