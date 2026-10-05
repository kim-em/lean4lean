import Lean4Lean.Theory.Typing.AnchoredOriginalWorldLegacyPiSelection
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiRowSelection

/-! Attach the jointly selected legacy row to the actual original Pi children.
The same annotations and finite controls are retained, without reinitializing
sites or changing the selected syntax. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable def WorldLegacyPiSelection.erase
    {strata : EquationStratification env} {budget : WorldPiDomainBudget strata}
    (selection : WorldLegacyPiSelection env budget U registry target locals σ A B available sizeBudget key result) :
    LegacyPiSelection env U registry target locals σ A B available sizeBudget key result :=
  .selected selection.pending selection.row selection.smaller

theorem WorldLegacyPiSelection.attachControlled
    {strata : EquationStratification env} {budget : WorldPiDomainBudget strata}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (selection : WorldLegacyPiSelection env budget U registry target locals σ A B available sizeBudget key result)
    (within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => budget.depth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier budget.worlds) :
    Nonempty ((selection.row.attach (domainNode := domainNode) (bodyNode := bodyNode)).Controlled controls frontier) := by
  refine ⟨⟨?_, ?_⟩⟩
  · exact {
      annotation := .legacy selection.row.domain selection.domainAnnotation
      within := by
        intro control active
        simpa only [StoredOriginalQuery.headDepth, LegacyStoredPiRow.attach, RichCert.headDepth] using
          Nat.le_trans (selection.domainDepth _) (within control active)
      sponsored := fun world member => sponsored world (selection.domainWorlds member) }
  · exact {
      annotation := .legacy selection.row.body.certificate selection.bodyAnnotation
      within := by
        intro control active
        simpa only [StoredOriginalQuery.headDepth, LegacyStoredPiRow.attach, RichCert.headDepth] using
          Nat.le_trans (selection.bodyDepth _) (within control active)
      sponsored := fun world member => sponsored world (selection.bodyWorlds member) }

/-- Enter directly from the SAME annotated legacy certificate and return its
actual selected row, its pending grade/key/output program, and real controls
at the original domain/body endpoints. -/
theorem WorldSortableCertProvenance.piRowControlled
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {certificate : SortableCert env U registry target locals σ (.forallE A B) relevant profile footprint}
    (annotation : WorldSortableCertProvenance strata certificate)
    (resources : footprint.Available available)
    (within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => certificate.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier annotation.worlds)
    (present : atom ∈ profile.atoms)
    {m : Nat} {support : Profile m} {table : List (Key m × Profile m)} {key : Key m} {result : Profile m}
    (path : GeneralOutputPath env U registry target atom (n := m+1)
      (.pi selectedDomain selectedBody support table))
    (member : (key, result) ∈ table) :
    ∃ selection : WorldLegacyPiSelection env
      ⟨annotation.worlds, fun policy => certificate.headDepth policy⟩ U registry target locals σ A B available
      (sizeOf certificate) key result,
      Nonempty ((selection.row.attach (domainNode := domainNode) (bodyNode := bodyNode)).Controlled controls frontier) := by
  obtain ⟨selection⟩ := annotation.selectPiProgram resources (sizeOf certificate) (Nat.le_refl _)
    (budget := ⟨annotation.worlds, fun policy => certificate.headDepth policy⟩)
    (fun _ member => member) (fun _ => Nat.le_refl _) atom present path member
  exact ⟨selection, selection.attachControlled within sponsored⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
