import Lean4Lean.Theory.Typing.EliminatorCoherence
import Lean4Lean.Theory.Typing.StructureConstructorHistory

/-! Eliminator coherence is a consequence of well-formedness.

`VEnv.WF'.inductEliminators` requires the projections registered for the
certified declaration's families to be that declaration's own entries
(`VInductDecl.ProjectionsCoherent`). Every later projection registration is
for fresh family names, so the coherence persists. -/

namespace Lean4Lean.VEnv
open InductiveSignature CaseSchema VExpr
open private addDefEqs_as_rules addConsts_as_values
  from Lean4Lean.Theory.Typing.NativeConstructorRigidity
set_option linter.unusedSectionVars false

variable {env env' : VEnv}

private theorem EliminatorsCoherent.extend (H : env.EliminatorsCoherent) (hle : env ≤ env')
    (helim : env'.eliminators = env.eliminators)
    (hproj : ∀ F info, env'.projections F info → env.projections F info ∨ env.constants F = none) :
    env'.EliminatorsCoherent := by
  intro key schema hs
  rw [helim] at hs
  obtain ⟨base, source, block, hbl, hcert, hconst, hcoh⟩ := H key schema hs
  refine ⟨base, source, block, hbl.trans hle, hcert, fun v hv => hle.constants (hconst v hv), ?_⟩
  intro type htype info hp
  rcases hproj _ info hp with hp | hfresh
  · exact hcoh type htype info hp
  · exfalso
    obtain ⟨expanded, g, auxiliaries, hdata, _⟩ := hcert
    have hmem : type.toVConstVal ∈ block.types ++ block.ctors := by
      apply List.mem_append_left
      rw [hdata.types]; exact List.mem_map.mpr ⟨type, htype, rfl⟩
    have := hconst _ hmem
    change env.constants type.name = _ at this
    rw [hfresh] at this
    cases this

private theorem old_projections (h : env'.projections = env.projections) :
    ∀ F info, env'.projections F info → env.projections F info ∨ env.constants F = none := by
  intro F info hp
  rw [h] at hp
  exact .inl hp

private theorem EliminatorsCoherent.addInduct (H : env.EliminatorsCoherent)
    (hadd : env.AddInduct decl env') : env'.EliminatorsCoherent := by
  cases hadd with
  | @intro block installed hdecl hcompile hblock hinstall =>
    simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hinstall
    obtain ⟨envTypes, htypes, envCtors, hctors, envRecs, hrecs, rfl⟩ := hinstall
    have hle : env ≤ (envRecs.addDefEqRules block.rules) :=
      (((VEnv.addConstVals_le htypes).trans (VEnv.addConstVals_le hctors)).trans
        (VEnv.addProjections_le.trans (VEnv.addConstVals_le hrecs))).trans VEnv.addDefEqRules_le
    apply H.extend hle
    · rw [addDefEqRules_eliminators, VEnv.addConstVals_eliminators hrecs,
        VEnv.addProjections_eliminators, VEnv.addConstVals_eliminators hctors,
        VEnv.addConstVals_eliminators htypes]
    · intro F info hp
      rw [VEnv.addDefEqRules_projections, VEnv.addConstVals_projections hrecs,
        VEnv.addProjections_iff, VEnv.addConstVals_projections hctors,
        VEnv.addConstVals_projections htypes] at hp
      rcases hp with ⟨entry, hentry, rfl, rfl⟩ | hp
      · right
        rw [hcompile.projections] at hentry
        obtain ⟨type, htype, ctor, _, rfl⟩ := decl.projectionEntries_origin hentry
        exact VEnv.addConstVals_names_fresh htypes type.toVConstVal (by
          rw [hcompile.types]; exact List.mem_map.mpr ⟨type, htype, rfl⟩)
      · exact .inl hp

private theorem EliminatorsCoherent.addQuot (H : env.EliminatorsCoherent)
    (hadd : env.addQuot = some env') : env'.EliminatorsCoherent := by
  simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hadd
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := hadd
  have hle : env ≤ d.addDefEq quotDefEq :=
    ((((VEnv.addConst_le ha).trans (VEnv.addConst_le hb)).trans
      (VEnv.addConst_le hc)).trans (VEnv.addConst_le hd)).trans VEnv.addDefEq_le
  apply H.extend hle
  · rw [VEnv.addDefEq_eliminators, VEnv.addConst_eliminators hd, VEnv.addConst_eliminators hc,
      VEnv.addConst_eliminators hb, VEnv.addConst_eliminators ha]
  · exact old_projections ((VEnv.addConst_projections hd).trans <|
      (VEnv.addConst_projections hc).trans <|
        (VEnv.addConst_projections hb).trans (VEnv.addConst_projections ha))

theorem WF'.eliminatorsCoherent {ds : List VDecl} (H : VEnv.WF' ds env) :
    env.EliminatorsCoherent := by
  induction H with
  | empty => intro _ _ h; cases h
  | @decl d env' ds env hdecl hbase ih =>
    cases hdecl with
    | «axiom» _ hadd | «opaque» _ hadd =>
      exact ih.extend (VEnv.addConst_le hadd) (VEnv.addConst_eliminators hadd)
        (old_projections (VEnv.addConst_projections hadd))
    | «example» => exact ih
    | @«def» _ _ ci _ hadd =>
      exact ih.extend ((VEnv.addConst_le hadd).trans VEnv.addDefEq_le)
        (by rw [VEnv.addDefEq_eliminators, VEnv.addConst_eliminators hadd])
        (fun F info hp => .inl ((VEnv.addConst_projections hadd) ▸ hp))
    | mutualDef _ hadd _ =>
      have hadd' := addConsts_as_values ▸ hadd
      apply ih.extend
      · rw [addDefEqs_as_rules]
        exact (VEnv.addConsts_le hadd).trans VEnv.addDefEqRules_le
      · rw [addDefEqs_as_rules, addDefEqRules_eliminators, VEnv.addConstVals_eliminators hadd']
      · apply old_projections
        rw [addDefEqs_as_rules, VEnv.addDefEqRules_projections, VEnv.addConstVals_projections hadd']
    | quot _ hadd => exact ih.addQuot hadd
    | induct _ hadd => exact ih.addInduct hadd
  | inductEliminators hbase henv hle hcert hkey hconstants hfresh _ ihBase ih =>
    intro k s hs
    rcases hs with ⟨rfl, rfl⟩ | hs
    · refine ⟨_, _, _, hle.trans VEnv.addEliminator_le, hcert,
        fun v hv => VEnv.addEliminator_le.constants (hconstants.1 v hv), ?_⟩
      intro type htype info hp
      exact hconstants.2.2.2 type htype info hp
    · obtain ⟨b, src, blk, hbl, hc, hconst, hcoh⟩ := ih k s hs
      exact ⟨b, src, blk, hbl.trans VEnv.addEliminator_le, hc,
        fun v hv => VEnv.addEliminator_le.constants (hconst v hv), hcoh⟩
  | @inductProjections baseDecls ds base envTypes envCtors decl block
      hbase _ hsource _ _ _ _ _ htypesSource _ hprojections htypes hctors ihBase ihCtors =>
    have hle : base ≤ envCtors.addProjections block.projections :=
      (VEnv.addConstVals_le htypes).trans ((VEnv.addConstVals_le hctors).trans VEnv.addProjections_le)
    apply ihBase.extend hle
    · rw [VEnv.addProjections_eliminators, VEnv.addConstVals_eliminators hctors,
        VEnv.addConstVals_eliminators htypes]
    · intro F info hp
      rw [VEnv.addProjections_iff, VEnv.addConstVals_projections hctors,
        VEnv.addConstVals_projections htypes] at hp
      rcases hp with ⟨entry, hentry, rfl, rfl⟩ | hp
      · right
        rw [hprojections] at hentry
        obtain ⟨type, htype, ctor, _, rfl⟩ := decl.projectionEntries_origin hentry
        exact VEnv.addConstVals_names_fresh htypes type.toVConstVal (by
          rw [htypesSource]; exact List.mem_map.mpr ⟨type, htype, rfl⟩)
      · exact .inl hp

/-- Registered case eliminators are coherent with registered projections in
every well-formed environment. -/
theorem WF.eliminatorsCoherent (H : env.WF) : env.EliminatorsCoherent :=
  H.choose_spec.eliminatorsCoherent

end Lean4Lean.VEnv
