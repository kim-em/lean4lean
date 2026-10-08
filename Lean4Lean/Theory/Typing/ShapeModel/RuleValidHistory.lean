import Lean4Lean.Theory.Typing.ShapeModel.RuleValidQuot
import Lean4Lean.Theory.Typing.ShapeModel.RuleValidNative
import Lean4Lean.Theory.Typing.ShapeModel.RuleValidGeneric

/-!
# Validity of the rules of a well-formed environment, along its history

The tables of the semantic signature `envSig env` are built along a history of `env`
(`HistTables`, `EnvTablesHist.lean`). By induction along that history, every environment `E` of
the history is good (`Good env E`: its rules, eliminators and structures are valid in the shape
model of `env`) and every family recorded so far has a semantic header (`FamSem`). At each step,
the new rules are validated using soundness for the earlier environments of the step
(`Good.sound`): definitions need nothing, the quotient rule and the native iota rules of an
installation and the generic equations of an eliminator registration use the semantic headers of
their families and the soundness of the derivations certified before the step.
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean InductiveSignature

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv}

theorem Good.extend (h : Good env E)
    (hdf : ∀ df, E'.defeqs df → E.defeqs df ∨ letI := envSig env; ExtraValid env df)
    (hel : ∀ {b sch}, E'.eliminators b sch → E.eliminators b sch ∨
      letI := envSig env; ElimOK env b sch)
    (hpr : ∀ {s info}, E'.projections s info → E.projections s info ∨ FamTypeSem env s info) :
    Good env E' := by
  letI := envSig env
  refine ⟨fun df h' => (hdf df h').elim (h.1 df) id, fun hb hgen hmem hcl hperm h1 h2 h3 => ?_,
    fun hp => (hpr hp).elim h.2.2 id⟩
  rcases hel hb with hb' | hok
  · exact h.2.1 hb' hgen hmem hcl hperm h1 h2 h3
  · exact hok hgen hmem hcl hperm h1 h2 h3

/-! ### The induction -/

theorem viewFams_famSem (H : env.WF) (hgood : Good env E) (hle : E ≤ env) (hE : E.Ordered)
    {decl : VInductDecl} {params : List VExpr} {sel : VInductiveType → Bool}
    (hshape : ∀ t ∈ decl.types, decl.TypeShape E params t)
    (huv : ∀ t ∈ decl.types, t.uvars = decl.uvars)
    (hc : ∀ t ∈ decl.types, env.constants t.name = some t.toVConstant)
    (h : viewFams decl sel I = some d) :
    letI := envSig env; FamSem env I d.resultLevel (d.nparams + d.nindices) := by
  obtain ⟨t, ht, -, rfl, rfl⟩ := viewFams_some h
  exact famSem_of_typeShape H hgood hle hE (hshape t ht) (huv t ht) (hc t ht)

theorem SchemaCtorReserved.mono {E E' : VEnv}
    (he : ∀ {b sch}, E.eliminators b sch → E'.eliminators b sch) (h : SchemaCtorReserved E c) :
    SchemaCtorReserved E' c := by
  obtain ⟨key, schema, h1, h2⟩ := h
  exact ⟨key, schema, he h1, h2⟩

/-- A reserved constructor name is declared. -/
theorem SchemaCtorReserved.present {E : VEnv} (hE : E.WF) (h : SchemaCtorReserved E c) :
    ∃ ci, E.constants c = some ci := by
  obtain ⟨key, schema, h1, h2⟩ := h
  obtain ⟨b, src, blk, _, _, hcert, _, hconsts⟩ := hE.eliminator_origin h1
  obtain ⟨c', hc, rfl⟩ := (Certified.mem_schemaCtorNames hcert).mp h2
  refine ⟨_, hconsts c' (List.mem_append_right _ ?_)⟩
  obtain ⟨expanded, aux, hdata, _⟩ := hcert
  rw [hdata.ctors]; exact hc

/-- A family view recorded for a name fresh in a well-formed environment does not record a
reserved constructor name. -/
theorem fresh_not_reserved {E : VEnv} (hE : E.WF) (hn : E.constants n = none) :
    ¬SchemaCtorReserved E n := fun h => by
  obtain ⟨ci, hci⟩ := h.present hE
  rw [hn] at hci; cases hci

/-- A family view of a declaration whose families are fresh never records a reserved name. -/
theorem viewFams_none_of_reserved {E : VEnv} (hE : E.WF) {decl : VInductDecl}
    {sel : VInductiveType → Bool} (hfresh : ∀ t ∈ decl.types, E.constants t.name = none)
    (hc : SchemaCtorReserved E c) : viewFams decl sel c = none := by
  cases hv : viewFams decl sel c with
  | none => rfl
  | some d =>
    exfalso
    obtain ⟨t, ht, -, rfl, -⟩ := viewFams_some hv
    exact fresh_not_reserved hE (hfresh t ht) hc

/-- The constructor stage of a declaration with a certified case schema is well formed. -/
theorem constructorStage_wf {base envTypes envCtors : VEnv} {decl : VInductDecl}
    {block : VInductBlock} {schema : CaseSchema} (hbase : base.WF)
    (hcert : schema.Certified base decl block)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors) : envCtors.WF := by
  obtain ⟨expanded, aux, hdata, _⟩ := hcert
  obtain ⟨types, ctors, ht, hc, htypesWF, hctorsWF⟩ := hdata.sourceWF.2.2.2.2
  rw [hdata.types] at htypes
  rw [htypes] at ht
  cases ht
  rw [hdata.ctors] at hctors
  apply VEnv.WF.addConstVals (cis := decl.constructorConstants) _ hctorsWF hctors
  apply VEnv.WF.addConstVals hbase _ htypes
  intro value hvalue
  obtain ⟨family, hfamily, rfl⟩ := List.mem_map.mp hvalue
  exact htypesWF family hfamily

/-- The generic equations of a certified schema registered at the constructor stage of its
declaration, over the tables `T₀` of the declaration's base, are valid. -/
theorem constructorStage_elimOK (H : env.WF) {base envTypes envCtors : VEnv} {T₀ : Tables}
    {decl : VInductDecl} {block : VInductBlock} {schema : CaseSchema} {key : Name}
    (hgood : Good env base) (hbase : base.WF) (hT₀ : T₀.Inv base)
    (hcert : schema.Certified base decl block)
    (hkey : decl.types.head?.map (·.name) = some key)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors)
    (hle : envCtors.addEliminator key schema ≤ env)
    (hext : (T₀.addSchema envCtors decl).Extends (envTables env))
    (hfam : ∀ I d, (T₀.addSchema envCtors decl).fam I = some d →
      letI := envSig env; FamSem env I d.resultLevel (d.nparams + d.nindices))
    (hfrz : ∀ c, SchemaCtorReserved (envCtors.addEliminator key schema) c →
      (T₀.addSchema envCtors decl).fam c = none → (envTables env).fam c = none) :
    letI := envSig env; ElimOK env key schema := by
  letI := envSig env
  obtain ⟨hle1, hdfC, hprojC, helimC, hconsts⟩ := constructorStage_facts htypes hctors
  have hgoodC : Good env envCtors := hgood.extend
    (fun df h => .inl (by rwa [hdfC] at h)) (fun h => .inl (by rwa [helimC] at h))
    (fun h => .inl (by rwa [hprojC] at h))
  have hfresh := (hcert.fresh hbase hkey).of_registry_eq helimC
  have hcompat : schema.StructCompat envCtors :=
    CaseSchema.StructCompat.of_projections (hcert.structCompat hbase htypes hctors)
      VEnv.addProjections_le.projections
  exact @generic_elimOK env envCtors base T₀ decl block schema key H hgoodC
    (constructorStage_wf hbase hcert htypes hctors) hle hbase hle1 hcert hkey ⟨hconsts, hdfC⟩
    hfresh hcompat (hT₀.transport hle1 hdfC hprojC) hext hfam hfrz

/-- At a native installation that also installs its case eliminator, the schema registration
over the base tables is part of the installation's tables, and an unrecorded family of the
former is unrecorded in the latter. -/
theorem addSchema_extends_inductCases {T₀ : Tables} {env₀ env₁ envTypes envCtors : VEnv}
    {decl : VInductDecl} {block : VInductBlock} {schema : CaseSchema} {key : Name}
    {entries : List NativeRecursorData}
    (hT₀ : T₀.Inv env₀) (henv : env₀.WF) (hcert : schema.Certified env₀ decl block)
    (htypes : env₀.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors)
    (hnat : T₀.Extends (T₀.addNative decl entries))
    (helim₁ : ∀ {k s}, env₁.eliminators k s → (k = key ∧ s = schema) ∨ env₀.eliminators k s)
    (hconsts₁ : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, env₁.constants c.name = some c.toVConstant) :
    (T₀.addSchema envCtors decl).Extends ((T₀.addNative decl entries).addSchema env₁ decl) ∧
      ∀ n, (T₀.addSchema envCtors decl).fam n = none →
        ((T₀.addNative decl entries).addSchema env₁ decl).fam n = none := by
  classical
  have hcert₀ := hcert
  obtain ⟨expanded, aux, hdata, _, _, _, _⟩ := hcert
  obtain ⟨_, hnd, _, hCtorUv, _⟩ := hdata.sourceWF
  obtain ⟨_, _, _, _, _, hraw⟩ := hdata.sourceParameters
  have hsel₀ : ∀ t ∈ decl.types, selFreeIn envCtors T₀ t = true := fun t ht =>
    selFreeIn_constructorStage hT₀ henv hcert₀ htypes hctors ht
  have hfreshT : ∀ t ∈ decl.types, env₀.constants t.name = none := fun t ht =>
    VEnv.addConstVals_names_fresh htypes t.toVConstVal (by
      rw [hdata.types]; exact List.mem_map.mpr ⟨t, ht, rfl⟩)
  have hsel₁ : ∀ t ∈ decl.types, t.ctors = [] →
      selFreeIn env₁ (T₀.addNative decl entries) t = true := by
    intro t ht hnil
    simp only [selFreeIn, selFree, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨?_, ?_, fun c hc => by simp [hnil] at hc⟩, ?_⟩
    · show addView T₀.fam (viewFams decl selCtors) t.name = none
      refine addView_none.mpr ⟨(hT₀.freshT (hfreshT t ht)).1, viewFams_none fun t' ht' hs' hn => ?_⟩
      have := VInductDecl.type_eq_of_mem_name hnd ht' ht hn
      subst this
      simp [selCtors, hnil] at hs'
    · show addView T₀.ctor (viewCtors decl selCtors) t.name = none
      exact addView_none.mpr ⟨(hT₀.freshT (hfreshT t ht)).2.1,
        viewCtors_none fun t' ht' _ c hc hn => sourceNames_type_ne_ctor hnd ht ht' hc hn⟩
    · rintro ⟨k, s, hreg, hmem⟩
      rcases helim₁ hreg with ⟨rfl, rfl⟩ | hold
      · obtain ⟨c, hc, hcn⟩ := (Certified.mem_schemaCtorNames hcert₀).mp hmem
        obtain ⟨t', ht', hc'⟩ := List.mem_flatMap.mp hc
        exact sourceNames_type_ne_ctor hnd ht ht' hc' hcn
      · exact fresh_not_reserved henv (hfreshT t ht) ⟨k, s, hold, hmem⟩
  have huniq := ctorView_unique (sel := fun _ => true) (env := env₁) (decl := decl)
    (fun t ht _ c hc => ⟨hconsts₁ t ht c hc, hraw t ht c hc,
      hCtorUv c (List.mem_flatMap.mpr ⟨t, ht, hc⟩)⟩)
  refine ⟨⟨fun h => h, fun h => hnat.natives h, fun h => h, fun {n f} h => ?_,
    fun {n k} h => ?_⟩, fun n hn => ?_⟩
  · rcases addView_some.mp h with h | ⟨h0, h⟩
    · exact addView_of_old (addView_of_old h)
    obtain ⟨t, ht, -, rfl, rfl⟩ := viewFams_some h
    by_cases hnil : t.ctors = []
    · refine addView_some.mpr (.inr ⟨?_, viewFams_mem hnd ht (hsel₁ t ht hnil)⟩)
      exact addView_none.mpr ⟨h0, viewFams_none fun t' ht' hs' hn => by
        have := VInductDecl.type_eq_of_mem_name hnd ht' ht hn
        subst this
        simp [selCtors, hnil] at hs'⟩
    · exact addView_of_old (addView_some.mpr (.inr ⟨h0,
        viewFams_mem hnd ht (selCtors_iff.mpr hnil)⟩))
  · rcases addView_some.mp h with h | ⟨h0, h⟩
    · exact addView_of_old (addView_of_old h)
    obtain ⟨t, ht, -, c, hc, rfl, rfl⟩ := viewCtors_some h
    have hs : selCtors t = true := selCtors_iff.mpr (List.ne_nil_of_mem hc)
    exact addView_of_old (addView_some.mpr (.inr ⟨h0, viewCtors_mem ht hs hc
      (fun t' ht' _ c' hc' hn => huniq t ht rfl c hc t' ht' rfl c' hc' hn)⟩))
  · obtain ⟨h0, hv⟩ := addView_none.mp hn
    have hnone : ∀ sel, viewFams decl sel n = none := by
      intro sel
      cases hw : viewFams decl sel n with
      | none => rfl
      | some d =>
        exfalso
        obtain ⟨t, ht, -, rfl, -⟩ := viewFams_some hw
        rw [viewFams_mem hnd ht (hsel₀ t ht)] at hv
        cases hv
    exact addView_none.mpr ⟨addView_none.mpr ⟨h0, hnone _⟩, hnone _⟩

/-- Every environment of the history building the tables of `env` is good, and every family
recorded along it has a semantic header. -/
theorem good_of_hist (H : env.WF) {E : VEnv} {T : Tables} (hH : HistTables E T) (hle : E ≤ env)
    (hext : T.Extends (envTables env))
    (hfrz : ∀ c, SchemaCtorReserved E c → T.fam c = none → (envTables env).fam c = none) :
    Good env E ∧ ∀ I d, T.fam I = some d →
      letI := envSig env; FamSem env I d.resultLevel (d.nparams + d.nindices) := by
  letI := envSig env
  induction hH with
  | empty =>
    refine ⟨⟨fun _ h => h.elim, fun h => h.elim, fun h => h.elim⟩, fun I d h => ?_⟩
    cases h
  | @«axiom» env₀ env₁ T₀ ci _ henv hci hadd ih =>
    obtain ⟨hg, hf⟩ := ih ((VEnv.addConst_le hadd).trans hle) hext fun c hc =>
      hfrz c (hc.mono fun h => (VEnv.addConst_le hadd).eliminators h)
    refine ⟨hg.extend (fun df h => .inl (by rwa [VEnv.addConst_defeqs hadd] at h))
      (fun h => .inl (by rwa [VEnv.addConst_eliminators hadd] at h))
      (fun h => .inl (by rwa [VEnv.addConst_projections hadd] at h)), hf⟩
  | @«opaque» env₀ env₁ T₀ ci _ henv hci hadd ih =>
    obtain ⟨hg, hf⟩ := ih ((VEnv.addConst_le hadd).trans hle) hext fun c hc =>
      hfrz c (hc.mono fun h => (VEnv.addConst_le hadd).eliminators h)
    refine ⟨hg.extend (fun df h => .inl (by rwa [VEnv.addConst_defeqs hadd] at h))
      (fun h => .inl (by rwa [VEnv.addConst_eliminators hadd] at h))
      (fun h => .inl (by rwa [VEnv.addConst_projections hadd] at h)), hf⟩
  | @«def» env₀ env₁ T₀ ci hH henv hci hadd ih =>
    have hT := (HistTables.inv hH).1
    have hle₁ : env₀ ≤ env₁.addDefEq ci.toDefEq := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
    obtain ⟨hg, hf⟩ := ih (hle₁.trans hle)
      ((hT.extends_addDefs (cis := [ci]) (by simpa [VEnv.addConsts] using hadd)).trans hext)
      fun c hc => hfrz c (hc.mono fun h => hle₁.eliminators h)
    refine ⟨hg.extend (fun df h => ?_)
      (fun h => .inl (by rwa [VEnv.addDefEq_eliminators, VEnv.addConst_eliminators hadd] at h))
      (fun h => .inl (by
        change env₁.projections _ _ at h; rwa [VEnv.addConst_projections hadd] at h)), hf⟩
    rcases h with rfl | h
    · right
      have hdf : env.defeqs ci.toDefEq := hle.defeqs VEnv.addDefEq_self
      have hdefs : (envTables env).defs ci.name = some ci := by
        refine hext.defs ?_
        exact (Tables.addDefs_defs (by simp)).mpr (.inl ⟨by simp, rfl⟩)
      have hci' : env.constants ci.name = some ci.toVConstant :=
        hle.constants ((VEnv.addDefEq_le).constants (VEnv.addConst_self hadd))
      haveI := envSig_coherent_of_wf H
      exact extraValid_def (.inl ⟨ci, hdf, hdefs, rfl⟩) hci' (H.ordered.closed.2 hdf).2.1
    · left; rwa [VEnv.addConst_defeqs hadd] at h
  | @mutualDef env₀ env₁ T₀ cis hH henv h1 hadd h2 ih =>
    have hT := (HistTables.inv hH).1
    have hle₁ : env₀ ≤ env₁.addDefEqs cis := (VEnv.addConsts_le hadd).trans addDefEqs_le
    obtain ⟨hg, hf⟩ := ih (hle₁.trans hle) ((hT.extends_addDefs hadd).trans hext)
      fun c hc => hfrz c (hc.mono fun h => hle₁.eliminators h)
    obtain ⟨hfresh, hnd⟩ := addConsts_fresh hadd
    refine ⟨hg.extend (fun df h => ?_)
      (fun h => .inl (by
        rwa [VEnv.addDefEqs_eliminators, VEnv.addConsts_eliminators hadd] at h))
      (fun h => .inl (by rwa [addDefEqs_projections, addConsts_projections hadd] at h)), hf⟩
    rcases addDefEqs_defeqs.mp h with ⟨v, hv, rfl⟩ | h
    · right
      have hdf : env.defeqs v.toDefEq := hle.defeqs (addDefEqs_defeqs.mpr (.inl ⟨v, hv, rfl⟩))
      have hdefs : (envTables env).defs v.name = some v :=
        hext.defs ((Tables.addDefs_defs hnd).mpr (.inl ⟨hv, rfl⟩))
      have hci' : env.constants v.name = some v.toVConstant := by
        refine hle.constants ?_
        rw [addDefEqs_constants]; exact VEnv.addConsts_constants hadd v hv
      haveI := envSig_coherent_of_wf H
      exact extraValid_def (.inl ⟨v, hdf, hdefs, rfl⟩) hci' (H.ordered.closed.2 hdf).2.1
    · left; rwa [addConsts_defeqs hadd] at h
  | @quot env₀ env₁ T₀ hH henv hready hadd ih =>
    obtain ⟨hle₁, hdfIff, hproj, hfQ0, -⟩ := addQuot_parts hadd
    obtain ⟨hg, hf⟩ := ih (hle₁.trans hle) ((Tables.extends_addQuot T₀).trans hext)
      fun c hc hc0 => hfrz c (hc.mono fun h => hle₁.eliminators h) (by
        show addView T₀.fam quotFams c = none
        rw [addView_none]
        refine ⟨hc0, ?_⟩
        by_cases hQ : c = ``Quot
        · subst hQ; exact absurd hc (fresh_not_reserved henv hfQ0)
        · simp [quotFams, hQ])
    have hT' := (HistTables.inv (HistTables.quot hH henv hready hadd)).1
    obtain ⟨hQI, hfQ, hcQ, -⟩ := hT'.quot rfl
    have hQI' := hQI.mono hle
    refine ⟨hg.extend (fun df h => ?_) (fun h => .inl ?_)
      (fun h => .inl (by rwa [hproj] at h)), fun I d h => ?_⟩
    · rcases (hdfIff df).mp h with rfl | h
      · exact .inr (quot_extraValid H (hext.quot rfl))
      · exact .inl h
    · rwa [VEnv.addQuot_eliminators hadd] at h
    · rcases addView_some.mp h with h | ⟨-, h⟩
      · exact hf I d h
      · by_cases hI : I = ``Quot
        · subst hI
          simp only [quotFams, if_true, Option.some.injEq] at h
          subst h; exact quot_famSem hQI'
        · simp [quotFams, hI] at h
  | @induct env₀ env₁ cbase T₀ decl expanded block s g aux hH henv hdecl hcomp hblock helimWF hE
      hinstall hcle hdata hprior ih =>
    have hT := (HistTables.inv hH).1
    have hinst := hT.install' henv hcomp hblock hinstall hcle hdata hprior
    have hle₁ := install_le hinstall
    obtain ⟨envTypes, envCtors, envRecs, htypes, hctors, hrecs, hinstEq⟩ := install_parts hinstall
    have hfreshT : ∀ t ∈ decl.types, env₀.constants t.name = none := fun t ht =>
      VEnv.addConstVals_names_fresh htypes t.toVConstVal (by
        rw [hdata.types]; exact List.mem_map.mpr ⟨t, ht, rfl⟩)
    have hfrz₀ : ∀ c, SchemaCtorReserved env₀ c → T₀.fam c = none →
        (envTables env).fam c = none := by
      intro c hc hc0
      refine hfrz c (hc.mono fun h => hle₁.eliminators h) ?_
      show addView T₀.fam (viewFams decl selCtors) c = none
      exact addView_none.mpr ⟨hc0, viewFams_none_of_reserved henv hfreshT hc⟩
    obtain ⟨hg, hf⟩ := ih (hle₁.trans hle) (hinst.1.trans hext) hfrz₀
    have hE₀ := henv.ordered
    have hTypeConst : ∀ t ∈ decl.types, env.constants t.name = some t.toVConstant := by
      intro t ht
      refine hle.constants ?_
      rw [hinstEq]
      simp only [VEnv.addDefEqRules_constants]
      have hmem : t.toVConstVal ∈ block.types := by
        rw [hdata.types]; exact List.mem_map.mpr ⟨t, ht, rfl⟩
      exact (VEnv.addConstVals_le hrecs).constants (VEnv.addEliminators_addProjections_le.constants
        ((VEnv.addConstVals_le hctors).constants (VEnv.addConstVals_get htypes hmem)))
    obtain ⟨params, _, _, hTypeShape, _, _⟩ := hdata.sourceParameters
    have hfam' : ∀ I d, (T₀.addNative decl
        (NativeRecursorData.compilationEntries default decl s aux g)).fam I = some d →
        FamSem env I d.resultLevel (d.nparams + d.nindices) := by
      intro I d h
      rcases addView_some.mp h with h | ⟨-, h⟩
      · exact hf I d h
      · exact viewFams_famSem H hg ((hle₁.trans hle)) hE₀
          (fun t ht => (hTypeShape t ht).mono hcle) hdata.sourceWF.2.2.1 hTypeConst h
    refine ⟨hg.extend (fun df h => ?_) (fun h => .inl ?_) (fun h => ?_), hfam'⟩
    · rcases (install_defeqs hinstall).mp h with h | h
      · exact .inr (native_extraValid H hg henv hle hdecl hcomp hblock hinstall hcle hdata hprior
          hT hext hfam' h)
      · exact .inl h
    · rcases (install_eliminators hinstall).mp h with h | h
      · rw [hE] at h; cases h
      · exact h
    · rcases (install_projections hinstall).mp h with ⟨entry, -, rfl, rfl⟩ | h
      · right
        have hp := hle.projections h
        exact famTypeSem_of_famSem H hp (hfam' _ _ (hinst.2.projections h).1)
      · exact .inl h
  | @inductCases env₀ env₁ cbase T₀ decl expanded block s g aux key schema hH henv hdecl hcomp
      hblock helimWF hE hinstall hcle hdata hprior ih =>
    have hT := (HistTables.inv hH).1
    have henv₁ : env₁.WF :=
      ⟨_, .decl (.induct hdecl (.intro hdecl hcomp hblock helimWF hinstall)) henv.choose_spec⟩
    have hinst := hT.install' henv hcomp hblock hinstall hcle hdata hprior
    have hcases := Tables.Inv.inductCases hT henv henv₁ hcomp hblock helimWF hE hinstall hcle
      hdata hprior
    have hle₁ := install_le hinstall
    obtain ⟨envTypes, envCtors, envRecs, htypes, hctors, hrecs, hinstEq⟩ := install_parts hinstall
    obtain ⟨envTypes', envCtors', htypes', hctors', hcase⟩ := helimWF
    cases Option.some.inj (htypes.symm.trans htypes')
    cases Option.some.inj (hctors.symm.trans hctors')
    rcases hcase with ⟨hE', -⟩ | ⟨key', schema', hE', hcert, hkey, hprojs, -⟩
    · rw [hE] at hE'; cases hE'
    rw [hE] at hE'
    obtain ⟨hk', hs'⟩ := Prod.mk.inj (List.cons.inj hE').1
    subst hk' hs'
    have hfreshT : ∀ t ∈ decl.types, env₀.constants t.name = none := fun t ht =>
      VEnv.addConstVals_names_fresh htypes t.toVConstVal (by
        rw [hdata.types]; exact List.mem_map.mpr ⟨t, ht, rfl⟩)
    let T₀N := T₀.addNative decl (NativeRecursorData.compilationEntries default decl s aux g)
    have hfrz₀ : ∀ c, SchemaCtorReserved env₀ c → T₀.fam c = none →
        (envTables env).fam c = none := by
      intro c hc hc0
      refine hfrz c (hc.mono fun h => hle₁.eliminators h) ?_
      show addView (addView T₀.fam (viewFams decl selCtors)) (viewFams decl (selFreeIn env₁ T₀N))
        c = none
      exact addView_none.mpr ⟨addView_none.mpr ⟨hc0, viewFams_none_of_reserved henv hfreshT hc⟩,
        viewFams_none_of_reserved henv hfreshT hc⟩
    obtain ⟨hg, hf⟩ := ih (hle₁.trans hle) (hcases.1.trans hext) hfrz₀
    have hE₀ := henv.ordered
    have hTypeConst : ∀ t ∈ decl.types, env.constants t.name = some t.toVConstant := by
      intro t ht
      refine hle.constants ?_
      rw [hinstEq]
      simp only [VEnv.addDefEqRules_constants]
      have hmem : t.toVConstVal ∈ block.types := by
        rw [hdata.types]; exact List.mem_map.mpr ⟨t, ht, rfl⟩
      exact (VEnv.addConstVals_le hrecs).constants (VEnv.addEliminators_addProjections_le.constants
        ((VEnv.addConstVals_le hctors).constants (VEnv.addConstVals_get htypes hmem)))
    obtain ⟨params, _, _, hTypeShape, _, _⟩ := hdata.sourceParameters
    have hfam' : ∀ I d, (T₀N.addSchema env₁ decl).fam I = some d →
        FamSem env I d.resultLevel (d.nparams + d.nindices) := by
      intro I d h
      rcases addView_some.mp h with h | ⟨-, h⟩
      · rcases addView_some.mp h with h | ⟨-, h⟩
        · exact hf I d h
        · exact viewFams_famSem H hg ((hle₁.trans hle)) hE₀
            (fun t ht => (hTypeShape t ht).mono hcle) hdata.sourceWF.2.2.1 hTypeConst h
      · exact viewFams_famSem H hg ((hle₁.trans hle)) hE₀
          (fun t ht => (hTypeShape t ht).mono hcle) hdata.sourceWF.2.2.1 hTypeConst h
    have hextN : T₀N.Extends (envTables env) := (T₀N.extends_addViews _ _).trans hext
    have hfamN : ∀ I d, T₀N.fam I = some d →
        FamSem env I d.resultLevel (d.nparams + d.nindices) := fun I d h =>
      hfam' I d (addView_of_old h)
    have hreg : env₁.eliminators key schema :=
      (install_eliminators hinstall).mpr (.inl (by rw [hE]; exact List.mem_singleton_self _))
    have hconsts₁ : ∀ t ∈ decl.types, ∀ c ∈ t.ctors,
        env₁.constants c.name = some c.toVConstant := fun t ht c hc =>
      VInductBlock.install_ctor_lookup hinstall (by
        rw [hdata.ctors]; exact List.mem_flatMap.mpr ⟨t, ht, hc⟩)
    have helim₁ : ∀ {k sch}, env₁.eliminators k sch → (k = key ∧ sch = schema) ∨
        env₀.eliminators k sch := by
      intro k sch h
      rcases (install_eliminators hinstall).mp h with h | h
      · rw [hE, List.mem_singleton, Prod.mk.injEq] at h
        exact .inl h
      · exact .inr h
    obtain ⟨hextS, hnoneS⟩ := addSchema_extends_inductCases (entries :=
      NativeRecursorData.compilationEntries default decl s aux g) hT henv hcert htypes hctors
      hinst.1 helim₁ hconsts₁
    have hstage : envCtors.addEliminator key schema ≤ env₁ := by
      have h1 : envCtors.addEliminators block.eliminators ≤ env₁ := by
        rw [hinstEq]
        exact VEnv.addProjections_le.trans ((VEnv.addConstVals_le hrecs).trans
          VEnv.addDefEqRules_le)
      rw [hE] at h1
      exact h1
    refine ⟨hg.extend (fun df h => ?_) (fun h => ?_) (fun h => ?_), hfam'⟩
    · rcases (install_defeqs hinstall).mp h with h | h
      · exact .inr (native_extraValid H hg henv hle hdecl hcomp hblock hinstall hcle hdata hprior
          hT hextN hfamN h)
      · exact .inl h
    · rcases helim₁ h with ⟨rfl, rfl⟩ | h
      · exact .inr (constructorStage_elimOK H hg henv hT hcert hkey htypes hctors
          (hstage.trans hle) (hextS.trans hext) (fun I d h => hfam' I d (hextS.fam h))
          (fun c hc hc0 => hfrz c (hc.mono fun h => hstage.eliminators h) (hnoneS c hc0)))
      · exact .inl h
    · rcases (install_projections hinstall).mp h with ⟨entry, -, rfl, rfl⟩ | h
      · right
        have hp := hle.projections h
        exact famTypeSem_of_famSem H hp (hfam' _ _ (hcases.2.projections h).1)
      · exact .inl h
  | @elim base env₀ T₀ source block schema key hH hbase henv hle₀ hcert hkey hconsts hfresh
      hcompat ih =>
    have hT := (HistTables.inv hH).1
    have hel := hT.eliminator (key := key) hbase hle₀ hcert hconsts.1 hconsts.2.1
    have hle₁ : env₀ ≤ env₀.addEliminator key schema := VEnv.addEliminator_le
    have hfrz₀ : ∀ c, SchemaCtorReserved env₀ c → T₀.fam c = none →
        (envTables env).fam c = none := by
      intro c hc hc0
      refine hfrz c (hc.mono fun h => hle₁.eliminators h) ?_
      show addView T₀.fam (viewFams source (selFreeIn env₀ T₀)) c = none
      rw [addView_none]
      refine ⟨hc0, ?_⟩
      cases hv : viewFams source (selFreeIn env₀ T₀) c with
      | none => rfl
      | some d =>
        exfalso
        obtain ⟨t, -, hsel, rfl, -⟩ := viewFams_some hv
        exact not_reserved_of_selFreeIn hsel hc
    obtain ⟨hg, hf⟩ := ih (hle₁.trans hle) (hel.1.trans hext) hfrz₀
    have hE := henv.ordered
    have hcert₀ := hcert
    obtain ⟨expanded, aux, hdata, _, _, hnames, _⟩ := hcert
    obtain ⟨params, _, _, hTypeShape, _, _⟩ := hdata.sourceParameters
    have hTypeConst : ∀ t ∈ source.types, env.constants t.name = some t.toVConstant := by
      intro t ht
      refine hle.constants (hle₁.constants ?_)
      exact hconsts.1 t.toVConstVal (List.mem_append_left _ (by
        rw [hdata.types]; exact List.mem_map.mpr ⟨t, ht, rfl⟩))
    have hfam' : ∀ I d, (T₀.addSchema env₀ source).fam I = some d →
        FamSem env I d.resultLevel (d.nparams + d.nindices) := by
      intro I d h
      rcases addView_some.mp h with h | ⟨-, h⟩
      · exact hf I d h
      · exact viewFams_famSem H hg ((hle₁.trans hle)) hE
          (fun t ht => (hTypeShape t ht).mono hle₀) hdata.sourceWF.2.2.1 hTypeConst h
    refine ⟨hg.extend (fun df h => .inl h) (fun h => ?_) (fun h => .inl h), hfam'⟩
    rcases VEnv.addEliminator_iff.mp h with ⟨rfl, rfl⟩ | h
    · exact .inr (generic_elimOK H hg henv hle hbase hle₀ hcert₀
        hkey ⟨hconsts.1, hconsts.2.1⟩ hfresh hcompat hT hext hfam' hfrz)
    · exact .inl h
  | @proj base envTypes envCtors T₀ decl block key schema hH hbase hctorsWF hE hcert hkey hhdr
      hsource htypesWF hcu hctorsWF' hparams hshape htypesSource hctorsSource hprojections htypes
      hctors ih =>
    have hT := (HistTables.inv hH).1
    have hreg := hT.registerCasesProjections hbase hE hcert htypes hctors
    obtain ⟨hbc, hdfC, hprojC, helimC, -⟩ := constructorStage_facts htypes hctors
    have hEC : envCtors.addEliminators block.eliminators = envCtors.addEliminator key schema := by
      rw [hE]; rfl
    have hle₁ : base ≤ (envCtors.addEliminators block.eliminators).addProjections
        block.projections := hbc.trans VEnv.addEliminators_addProjections_le
    have hfrz₀ : ∀ c, SchemaCtorReserved base c → T₀.fam c = none →
        (envTables env).fam c = none := by
      intro c hc hc0
      refine hfrz c (hc.mono fun h => hle₁.eliminators h) ?_
      show addView T₀.fam (viewFams decl (selFreeIn envCtors T₀)) c = none
      rw [addView_none]
      refine ⟨hc0, ?_⟩
      cases hv : viewFams decl (selFreeIn envCtors T₀) c with
      | none => rfl
      | some d =>
        exfalso
        obtain ⟨t, -, hsel, rfl, -⟩ := viewFams_some hv
        exact not_reserved_of_selFreeIn hsel (hc.mono fun h => by rwa [helimC])
    obtain ⟨hg, hf⟩ := ih (hle₁.trans hle) (hreg.1.trans hext) hfrz₀
    have hE₀ := hbase.ordered
    obtain ⟨params, _, _, hTypeShape, _, _⟩ := hparams
    have hTypeConst : ∀ t ∈ decl.types, env.constants t.name = some t.toVConstant := by
      intro t ht
      refine hle.constants ?_
      rw [VEnv.addProjections_constants, VEnv.addEliminators_constants]
      have hmem : t.toVConstVal ∈ block.types := by
        rw [htypesSource]; exact List.mem_map.mpr ⟨t, ht, rfl⟩
      exact (VEnv.addConstVals_le hctors).constants (VEnv.addConstVals_get htypes hmem)
    have huv : ∀ t ∈ decl.types, t.uvars = decl.uvars := by
      obtain ⟨_, _, hdata, _⟩ := hcert
      exact hdata.sourceWF.2.2.1
    have hfam' : ∀ I d, (T₀.addSchema envCtors decl).fam I = some d →
        FamSem env I d.resultLevel (d.nparams + d.nindices) := by
      intro I d h
      rcases addView_some.mp h with h | ⟨-, h⟩
      · exact hf I d h
      · exact viewFams_famSem H hg (hle₁.trans hle) hE₀ hTypeShape huv hTypeConst h
    have hstage : envCtors.addEliminator key schema ≤
        (envCtors.addEliminators block.eliminators).addProjections block.projections := by
      rw [hEC]; exact VEnv.addProjections_le
    refine ⟨hg.extend (fun df h => .inl ?_) (fun h => ?_) (fun h => ?_), hfam'⟩
    · rwa [VEnv.addProjections_defeqs, VEnv.addEliminators_defeqs, hdfC] at h
    · rw [VEnv.addProjections_eliminators, VEnv.addEliminators_iff, hE, List.mem_singleton,
        Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · exact .inr (constructorStage_elimOK H hg hbase hT hcert hkey htypes hctors
          (hstage.trans hle) hext hfam'
          (fun c hc hc0 => hfrz c (hc.mono fun h => hstage.eliminators h) hc0))
      · exact .inl (by rwa [helimC] at h)
    · rcases VEnv.addProjections_iff.mp h with ⟨entry, -, rfl, rfl⟩ | h
      · right
        exact famTypeSem_of_famSem H (hle.projections h) (hfam' _ _ (hreg.2.projections h).1)
      · exact .inl (by rwa [VEnv.addEliminators_projections, hprojC] at h)

/-- The validity facts of the shape model of a well-formed environment. -/
theorem good_of_wf (H : env.WF) : Good env env :=
  (good_of_hist H (envTables_hist H) VEnv.LE.rfl Tables.Extends.rfl fun _ _ h => h).1

/-- Head separation for every well-formed environment. -/
theorem headSeparation_of_wf (H : env.WF) : env.HeadSeparation :=
  have hg := good_of_wf H
  headSeparation_of_valid H (fun hp => hg.2.2 hp) hg.1 hg.2.1

end

end Lean4Lean.ShapeModel
