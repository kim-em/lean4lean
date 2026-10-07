import Lean4Lean.Verify.Environment.Lemmas
import Lean4Lean.Theory.Inductive.CaseRegistration

/-! Introduce the abstract case schemas into the actual checking environment
at the constructor boundary, before checking any generated native recursor. -/

namespace Lean4Lean

open InductiveSignature

/-- The constructor-complete checker stage may use declaration-derived case
schemas. Its native projection table is retained during the projection
migration; that table is not used to justify the abstract case registration,
except for the certified fact `hprojs` that the schema projects only out of
structures registered at this stage (a producer obligation). The registered
projection entries are those of the same block (`hentries`), so the schema is
compatible with every registered structure (`Certified.structCompat`). -/
theorem CheckingEnv.Valid.registerCases
    {s : InductiveSignature} {g : Instance s}
    {base envTypes envCtors : VEnv}
    (H : CheckingEnv.Valid safety concrete (envCtors.addProjections entries))
    (hbase : base.WF)
    (hdata : CompilationData base source expanded s g auxiliaries block)
    (hprior : CertifiedSpecializations base auxiliaries)
    (hkey : source.types.head?.map (·.name) = some key)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors)
    (hentries : entries = block.projections)
    (hprojs : (CaseSchema.ofCompilation source s auxiliaries).ProjNamesRegistered
      (envCtors.addProjections entries) key)
    (hcoherent : source.ProjectionsCoherent (envCtors.addProjections entries)) :
    CheckingEnv.Valid safety concrete
      ((envCtors.addProjections entries).addEliminator key
        (CaseSchema.ofCompilation source s auxiliaries)) := by
  let schema := CaseSchema.ofCompilation source s auxiliaries
  have hformed : schema.Certified base source block :=
    CaseSchema.ofCompilation_certified hdata hprior
  have hregistry : (envCtors.addProjections entries).eliminators = base.eliminators := by
    rw [VEnv.addProjections_eliminators, VEnv.addConstVals_eliminators hctors,
      VEnv.addConstVals_eliminators htypes]
  have hfresh := (hformed.fresh hbase hkey).of_registry_eq hregistry
  have hequations : (envCtors.addProjections entries).defeqs = base.defeqs := by
    rw [VEnv.addProjections_defeqs, VEnv.addConstVals_defeqs hctors,
      VEnv.addConstVals_defeqs htypes]
  apply H.addEliminator
  apply hbase.inductEliminators H.tr.wf
    (((VEnv.addConstVals_le htypes).trans (VEnv.addConstVals_le hctors)).trans
      VEnv.addProjections_le) hformed hkey _ hequations hprojs hcoherent hfresh
    (hentries ▸ hformed.structCompat hbase htypes hctors)
  intro value hvalue
  apply VEnv.addProjections_le.constants
  rcases List.mem_append.mp hvalue with hvalue | hvalue
  · exact (VEnv.addConstVals_le hctors).constants (VEnv.addConstVals_get htypes hvalue)
  · exact VEnv.addConstVals_get hctors hvalue

end Lean4Lean
