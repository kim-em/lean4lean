import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationalStageChains

/-! # The well-formed stage before recursors and their rules

The constructor and projection stage has the earlier pattern registry. Its
formation judgment for each generated recursor type can therefore be interpreted
using only coverage of earlier rules.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params
variable [Params]

/-- An installed declaration has a well-formed constructor/projection stage
below the ambient environment, with exactly the previous stage's patterns and
all its recursor types already well formed. -/
theorem computational_declaration_projection_environment
    {env₀ env₁ : VEnv} {decl : VInductDecl}
    (hstage : env₀ ∈ env.stages) (hdecl : decl.WF env₀)
    (hadd : env₀.addInduct decl = some env₁) (hle : env₁ ≤ env) :
    ∃ envP, envP.WF ∧ envP ≤ env ∧ envP.pats = env₀.pats ∧
      decl.addTypesCtorsProjs env₀ = some envP ∧
      ∀ rec ∈ decl.recs, envP.IsType rec.uvars [] rec.type := by
  obtain ⟨ds, H⟩ := henv.stagesH
  have hW₀ := (H.stage hstage).1
  obtain ⟨envT, envC, envR, hT, hC, hR, hRules⟩ := addInduct_stages hadd
  have hTC : decl.addTypesCtors env₀ = some envC := by
    unfold VInductDecl.addTypesCtors; rw [hT]; exact hC
  have hTCP := addTypesCtorsProjs_eq_some hTC
  rw [VInductDecl.addTypes_eq_addConstVals] at hT
  rw [VInductDecl.addCtors_eq_addConstVals] at hC
  have hWT := hW₀.addConstVals (fun ci hci => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hci
    exact hdecl.types_wf t ht) hT
  have hCW := hdecl.source.constructorsWF_at hT
  have hWC := hWT.addConstVals hCW hC
  have hparams := hdecl.sourceParameterWF hT
  have hWP : (decl.addProjs envC).WF :=
    WF.inductProjections
      (block := ⟨decl.typeConstants, decl.constructorConstants, [], [], decl.projectionEntries⟩)
      hW₀ hWC hdecl.source.2.1 hdecl.source.sourceTypes hdecl.source.2.2.2.1
      hCW hparams hparams.rawCtorShape rfl rfl rfl hT hC
  have hPle : decl.addProjs envC ≤ env :=
    ((addRecs_le hR).trans (addRules_le hRules)).trans hle
  have hpats : (decl.addProjs envC).pats = env₀.pats :=
    addProjs_pats.trans ((addConstVals_pats hC).trans (addConstVals_pats hT))
  exact ⟨_, hWP, hPle, hpats, hTCP, hdecl.recs_wf _ hTCP⟩

/-- A registered singleton's generated recursor type is well formed before
its rules are installed. This isolates the formation premise needed to extract
generic index typings, at the original packed universe parameters. -/
theorem registered_singleton_type_formation_before_rules {rec : VRecursor}
    (hAt : RecursorRegisteredAt env data decl env₀ env₁)
    (hstage : env₀ ∈ env.stages) (hrec : rec ∈ decl.recs) (hname : rec.name = data.name)
    (hlarge : data.largeTarget = true)
    (hzero : (data.schema.sourceLevel data.owner data.levels).inst packed ≈ .zero) :
    ∃ E, E.WF ∧ E ≤ env ∧ E.pats = env₀.pats ∧
      E.IsType data.uvars [] (data.recursorInstance.recursorType data.owner) := by
  have F := RecursorData.singletonSignature hAt.registered hlarge hzero
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hdecl, hadd, _, hle, _⟩ := hAt
  obtain ⟨E, hEW, hE, hpats, _, hforms⟩ :=
    computational_declaration_projection_environment hstage hdecl hadd hle
  have hc := hle.constants (addInduct_rec_find hadd hrec)
  rw [hname] at hc
  have he := Option.some.inj (hc.symm.trans F.recursor)
  have hu := congrArg VConstant.uvars he
  have ht := congrArg VConstant.type he
  have H := hforms rec hrec
  change rec.uvars = data.uvars at hu
  change rec.type = data.recursorInstance.recursorType data.owner at ht
  rw [hu, ht] at H
  exact ⟨E, hEW, hE, hpats, H⟩

/-- Set the free target universe to Prop before interpreting the generated
minor. The source levels remain exactly those of the actual occurrence. -/
theorem registered_singleton_specialized_formation_before_rules {rec : VRecursor}
    (hAt : RecursorRegisteredAt env data decl env₀ env₁)
    (hstage : env₀ ∈ env.stages) (hrec : rec ∈ decl.recs) (hname : rec.name = data.name)
    (hlarge : data.largeTarget = true)
    (hzero : (data.schema.sourceLevel data.owner data.levels).inst packed ≈ .zero)
    (hw : ∀ l ∈ packed, l.WF univs) (hlen : packed.length = data.uvars) :
    ∃ E, ∃ g : Instance data.schema.signature, E.WF ∧ E ≤ env ∧ E.pats = env₀.pats ∧
      g.uvars = univs ∧ g.levels = data.levels.map (·.inst packed) ∧ g.targetLevel = .zero ∧
      E.IsType g.uvars [] (g.recursorType data.owner) := by
  obtain ⟨E, hEW, hE, hpats, u, HT⟩ :=
    registered_singleton_type_formation_before_rules hAt hstage hrec hname hlarge hzero
  have F := RecursorData.singletonSignature hAt.registered hlarge hzero
  obtain ⟨k, hk, hkU, hfree⟩ := F.free
  let g := data.recursorInstance.specialize univs (packed.set k .zero)
  have hw' : ∀ l ∈ packed.set k .zero, l.WF univs := by
    intro l hl
    rcases List.mem_or_eq_of_mem_set hl with hl | rfl
    · exact hw l hl
    · trivial
  have hlevels : g.levels = data.levels.map (·.inst packed) :=
    List.map_congr_left fun l hl => hfree l hl packed .zero
  have htarget : g.targetLevel = .zero := by
    show data.target.inst (packed.set k .zero) = .zero
    rw [hk]
    simp [VLevel.inst, List.getD_eq_getElem?_getD, hlen, hkU]
  refine ⟨E, g, hEW, hE, hpats, rfl, hlevels, htarget, u.inst (packed.set k .zero), ?_⟩
  have H := HT.instL hw'
  rwa [Instance.recursorType_specialize _ univs] at H

end Lean4Lean.VEnv.Strengthening
