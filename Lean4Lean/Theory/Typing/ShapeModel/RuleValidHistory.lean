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

/-- Every environment of the history building the tables of `env` is good, and every family
recorded along it has a semantic header. -/
theorem good_of_hist (H : env.WF) {E : VEnv} {T : Tables} (hH : HistTables E T) (hle : E ≤ env)
    (hext : T.Extends (envTables env)) :
    Good env E ∧ ∀ I d, T.fam I = some d →
      letI := envSig env; FamSem env I d.resultLevel (d.nparams + d.nindices) := by
  letI := envSig env
  induction hH with
  | empty =>
    refine ⟨⟨fun _ h => h.elim, fun h => h.elim, fun h => h.elim⟩, fun I d h => ?_⟩
    cases h
  | @«axiom» env₀ env₁ T₀ ci _ henv hci hadd ih =>
    obtain ⟨hg, hf⟩ := ih ((VEnv.addConst_le hadd).trans hle) hext
    refine ⟨hg.extend (fun df h => .inl (by rwa [VEnv.addConst_defeqs hadd] at h))
      (fun h => .inl (by rwa [VEnv.addConst_eliminators hadd] at h))
      (fun h => .inl (by rwa [VEnv.addConst_projections hadd] at h)), hf⟩
  | @«opaque» env₀ env₁ T₀ ci _ henv hci hadd ih =>
    obtain ⟨hg, hf⟩ := ih ((VEnv.addConst_le hadd).trans hle) hext
    refine ⟨hg.extend (fun df h => .inl (by rwa [VEnv.addConst_defeqs hadd] at h))
      (fun h => .inl (by rwa [VEnv.addConst_eliminators hadd] at h))
      (fun h => .inl (by rwa [VEnv.addConst_projections hadd] at h)), hf⟩
  | @«def» env₀ env₁ T₀ ci hH henv hci hadd ih =>
    have hT := (HistTables.inv hH).1
    have hle₁ : env₀ ≤ env₁.addDefEq ci.toDefEq := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
    obtain ⟨hg, hf⟩ := ih (hle₁.trans hle)
      ((hT.extends_addDefs (cis := [ci]) (by simpa [VEnv.addConsts] using hadd)).trans hext)
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
    obtain ⟨hle₁, hdfIff, hproj, -⟩ := addQuot_parts hadd
    obtain ⟨hg, hf⟩ := ih (hle₁.trans hle) ((Tables.extends_addQuot T₀).trans hext)
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
  | @induct env₀ env₁ cbase T₀ decl expanded block s g aux hH henv hdecl hcomp hblock hinstall
      hcle hdata hprior ih =>
    have hT := (HistTables.inv hH).1
    have hinst := hT.install' henv hcomp hblock hinstall hcle hdata hprior
    have hle₁ := install_le hinstall
    obtain ⟨hg, hf⟩ := ih (hle₁.trans hle) (hinst.1.trans hext)
    have hE := henv.ordered
    obtain ⟨envTypes, envCtors, envRecs, htypes, hctors, hrecs, hinstEq⟩ := install_parts hinstall
    have hTypeConst : ∀ t ∈ decl.types, env.constants t.name = some t.toVConstant := by
      intro t ht
      refine hle.constants ?_
      rw [hinstEq]
      simp only [VEnv.addDefEqRules_constants]
      have hmem : t.toVConstVal ∈ block.types := by
        rw [hdata.types]; exact List.mem_map.mpr ⟨t, ht, rfl⟩
      exact (VEnv.addConstVals_le hrecs).constants (VEnv.addProjections_le.constants
        ((VEnv.addConstVals_le hctors).constants (VEnv.addConstVals_get htypes hmem)))
    obtain ⟨params, _, _, hTypeShape, _, _⟩ := hdata.sourceParameters
    have hfam' : ∀ I d, (T₀.addNative decl
        (NativeRecursorData.compilationEntries default decl s aux g)).fam I = some d →
        FamSem env I d.resultLevel (d.nparams + d.nindices) := by
      intro I d h
      rcases addView_some.mp h with h | ⟨-, h⟩
      · exact hf I d h
      · exact viewFams_famSem H hg ((hle₁.trans hle)) hE
          (fun t ht => (hTypeShape t ht).mono hcle) hdata.sourceWF.2.2.1 hTypeConst h
    refine ⟨hg.extend (fun df h => ?_) (fun h => .inl ?_) (fun h => ?_), hfam'⟩
    · rcases (install_defeqs hinstall).mp h with h | h
      · exact .inr (native_extraValid H hg henv hle hdecl hcomp hblock hinstall hcle hdata hprior
          hT hext hfam' h)
      · exact .inl h
    · rwa [install_eliminators hinstall] at h
    · rcases (install_projections hinstall).mp h with ⟨entry, -, rfl, rfl⟩ | h
      · right
        have hp := hle.projections h
        exact famTypeSem_of_famSem H hp (hfam' _ _ (hinst.2.projections h).1)
      · exact .inl h
  | @elim base env₀ T₀ source block schema key hH hbase henv hle₀ hcert hkey hconsts hfresh
      hcompat ih =>
    have hT := (HistTables.inv hH).1
    have hel := hT.eliminator (key := key) hbase hle₀ hcert hconsts.1 hconsts.2.1
    have hle₁ : env₀ ≤ env₀.addEliminator key schema := VEnv.addEliminator_le
    obtain ⟨hg, hf⟩ := ih (hle₁.trans hle) (hel.1.trans hext)
    have hE := henv.ordered
    obtain ⟨expanded, g, aux, hdata, _, _, hnames⟩ := hcert
    obtain ⟨params, _, _, hTypeShape, _, _⟩ := hdata.sourceParameters
    have hTypeConst : ∀ t ∈ source.types, env.constants t.name = some t.toVConstant := by
      intro t ht
      refine hle.constants (hle₁.constants ?_)
      exact hconsts.1 t.toVConstVal (List.mem_append_left _ (by
        rw [hdata.types]; exact List.mem_map.mpr ⟨t, ht, rfl⟩))
    have hfam' : ∀ I d, (T₀.addSchema source).fam I = some d →
        FamSem env I d.resultLevel (d.nparams + d.nindices) := by
      intro I d h
      rcases addView_some.mp h with h | ⟨-, h⟩
      · exact hf I d h
      · exact viewFams_famSem H hg ((hle₁.trans hle)) hE
          (fun t ht => (hTypeShape t ht).mono hle₀) hdata.sourceWF.2.2.1 hTypeConst h
    refine ⟨hg.extend (fun df h => .inl h) (fun h => ?_) (fun h => .inl h), hfam'⟩
    rcases VEnv.addEliminator_iff.mp h with ⟨rfl, rfl⟩ | h
    · exact .inr (generic_elimOK H hg henv hle hbase hle₀ ⟨expanded, g, aux, hdata, ‹_›, ‹_›, hnames⟩
        hkey hconsts hfresh hcompat hT hext hfam')
    · exact .inl h
  | @proj base envTypes envCtors T₀ decl block hH hbase hctorsWF hsource htypesWF hcu hctorsWF'
      hparams hshape htypesSource hctorsSource hprojections htypes hctors ih =>
    have hT := (HistTables.inv hH).1
    have henv' := VEnv.WF.inductProjections hbase hctorsWF hsource htypesWF hcu hctorsWF'
      hparams hshape htypesSource hctorsSource hprojections htypes hctors
    have hreg := hT.registerProjections hbase henv' hsource hcu hparams hshape htypesSource
      hctorsSource hprojections htypes hctors
    have hle₁ : envCtors ≤ envCtors.addProjections block.projections := VEnv.addProjections_le
    obtain ⟨hg, hf⟩ := ih (hle₁.trans hle) (hreg.1.trans hext)
    have hE := hctorsWF.ordered
    have hbc : base ≤ envCtors := (VEnv.addConstVals_le htypes).trans (VEnv.addConstVals_le hctors)
    obtain ⟨params, _, _, hTypeShape, _, _⟩ := hparams
    have hTypeConst : ∀ t ∈ decl.types, env.constants t.name = some t.toVConstant := by
      intro t ht
      refine hle.constants ?_
      rw [VEnv.addProjections_constants]
      have hmem : t.toVConstVal ∈ block.types := by
        rw [htypesSource]; exact List.mem_map.mpr ⟨t, ht, rfl⟩
      exact (VEnv.addConstVals_le hctors).constants (VEnv.addConstVals_get htypes hmem)
    have hfam' : ∀ I d, (T₀.addViews (viewFams decl selStruct) (viewCtors decl selStruct)).fam I =
        some d → FamSem env I d.resultLevel (d.nparams + d.nindices) := by
      intro I d h
      have hFS := (hreg.2.views.fam h).1
      rcases addView_some.mp h with h | ⟨-, h⟩
      · exact hf I d h
      · obtain ⟨t, ht, -, rfl, rfl⟩ := viewFams_some h
        obtain ⟨ci, hci, huv, -⟩ := hFS
        have := (hle.constants hci).symm.trans (hTypeConst t ht)
        cases this
        exact famSem_of_typeShape H hg (hle₁.trans hle) hE ((hTypeShape t ht).mono hbc) huv
          (hTypeConst t ht)
    refine ⟨hg.extend (fun df h => .inl (by rwa [VEnv.addProjections_defeqs] at h))
      (fun h => .inl (by rwa [VEnv.addProjections_eliminators] at h)) (fun h => ?_), hfam'⟩
    rcases VEnv.addProjections_iff.mp h with ⟨entry, -, rfl, rfl⟩ | h
    · right
      exact famTypeSem_of_famSem H (hle.projections h) (hfam' _ _ (hreg.2.projections h).1)
    · exact .inl h

/-- The validity facts of the shape model of a well-formed environment. -/
theorem good_of_wf (H : env.WF) : Good env env :=
  (good_of_hist H (envTables_hist H) VEnv.LE.rfl Tables.Extends.rfl).1

/-- Head separation for every well-formed environment. -/
theorem headSeparation_of_wf (H : env.WF) : env.HeadSeparation :=
  have hg := good_of_wf H
  headSeparation_of_valid H (fun hp => hg.2.2 hp) hg.1 hg.2.1

end

end Lean4Lean.ShapeModel
