import Lean4Lean.Verify.Inductive.SourceModels
import Lean4Lean.Theory.Inductive.ConstructorArity
import Lean4Lean.Verify.Inductive.Recursor.Structure
import Lean4Lean.Verify.Inductive.Specification.Formation
import Lean4Lean.Theory.Inductive.CaseProjNames
import Lean4Lean.Theory.Typing.ProjNamesTyping
import Lean4Lean.Theory.Typing.CaseSourceSort
import Lean4Lean.Theory.Typing.ProjectionLemmas

/-! # The constructor boundary and its source signature

`ConstructorBoundary` is the data available once every constructor of a declaration is checked
and declared, before any checker run in the projected environment: the header materialization,
the checked constructor tails and the abstract translation. The source signature of the
declaration (`sourceSignature`, whose model is `sourceSignature_models`) is computed from it, so
the declaration's case eliminator can be certified at this boundary, before the projections and
the native recursors. -/

namespace Lean4Lean

theorem InductiveSignature.vars_append_eq_bvarRange (a b : Nat) :
    vars a b ++ vars b 0 = VExpr.bvarRange (a + b) (a + b) := by
  apply List.ext_getElem
  · simp [vars]
  · intro j h1 h2
    simp only [List.length_append, vars, List.length_map, List.length_reverse,
      List.length_range] at h1
    rw [VExpr.bvarRange_getElem _ _ _ (by omega)]
    by_cases hj : j < a
    · rw [List.getElem_append_left (by simp [vars]; omega)]
      simp only [vars, List.getElem_map, List.getElem_reverse, List.getElem_range,
        List.length_range, VExpr.bvar.injEq]
      omega
    · rw [List.getElem_append_right (by simp [vars]; omega)]
      simp only [vars, List.getElem_map, List.getElem_reverse, List.getElem_range,
        List.length_range, List.length_map, List.length_reverse, VExpr.bvar.injEq]
      omega

namespace VEnv

/-- A closed term typed at a telescope, applied to the telescope's own
variables in the telescope's context, has the telescope's body type. -/
theorem HasType.mkApps_bvarRange {env : VEnv} {U : Nat} (henv : env.WF)
    {f B : VExpr} {doms : List VExpr}
    (hf : env.HasType U [] f (VExpr.wrapForalls doms B))
    (hctx : OnCtx doms.reverse (env.IsType U))
    (hB : B.ClosedN doms.length) :
    env.HasType U doms.reverse
      (VExpr.mkApps f (VExpr.bvarRange doms.length doms.length)) B := by
  have hf' : env.HasType U doms.reverse f (VExpr.wrapForalls doms B) :=
    hf.weak0 henv.ordered
  have h := HasType.mkApps_of_telescope henv hctx
    (args := VExpr.bvarRange doms.length doms.length) hf' (by simp) ?_
  · rwa [VExpr.instOuter_range_bvar' B _ _ hB (Nat.le_refl _), Nat.sub_self,
      VExpr.liftN_zero] at h
  · intro j hj hj'
    simp only [VExpr.bvarRange_length] at hj
    rw [VExpr.bvarRange_getElem _ _ _ hj, VExpr.bvarRange_take _ _ _ (Nat.le_of_lt hj)]
    have hclosed : doms[j].ClosedN j := by
      have := OnCtx.reverse_getElem_closedN henv (Γ := []) (by simpa using hctx) j hj'
      simpa using this
    rw [VExpr.instOuter_range_bvar' _ _ _ hclosed (by omega)]
    have hl := Lookup.reverse_append doms [] j hj'
    simp only [List.append_nil] at hl
    exact .bvar hl

end VEnv

theorem VInductDecl.SourceWF.mono_of_addConstVals {decl : VInductDecl} {env env' envTypes envCtors : VEnv}
    (H : decl.SourceWF env) (hle : env ≤ env')
    (htypes : env'.addConstVals decl.typeConstants = some envTypes)
    (hctors : envTypes.addConstVals decl.constructorConstants = some envCtors) :
    decl.SourceWF env' := by
  rcases H with ⟨hnonempty, hnames, htypeUvars, hctorUvars, sourceTypes, sourceCtors,
    hsourceTypes, _, hsourceTypesWF, hsourceCtorsWF⟩
  have hsourceTypesLE : sourceTypes ≤ envTypes :=
    VEnv.addConstVals_mono hle hsourceTypes htypes
  exact ⟨hnonempty, hnames, htypeUvars, hctorUvars, envTypes, envCtors, htypes, hctors,
    fun type htype => (hsourceTypesWF type htype).mono hle,
    fun ctor hctor => (hsourceCtorsWF ctor hctor).mono hsourceTypesLE⟩

theorem VInductDecl.FormationWF.mono_of_addConstVals {decl : VInductDecl} {env env' envTypes : VEnv}
    (H : decl.FormationWF env) (hle : env ≤ env')
    (htypes : env'.addConstVals decl.typeConstants = some envTypes) :
    decl.FormationWF env' := by
  rcases H with ⟨params, resultLevel, formationTypes, hformationTypes, htypeShapes,
    hctorShapes, hraw⟩
  have hformationTypesLE : formationTypes ≤ envTypes :=
    VEnv.addConstVals_mono hle hformationTypes htypes
  exact ⟨params, resultLevel, envTypes, htypes,
    fun type htype => ⟨(htypeShapes type htype).1, (htypeShapes type htype).2.mono hle⟩,
    fun type htype ctor hctor =>
      let Hctor := hctorShapes type htype ctor hctor
      ⟨Hctor.1.mono hformationTypesLE, Hctor.2.mono hformationTypesLE⟩, hraw⟩

/-- The case eliminators registered with an ordinary declaration at its constructor boundary:
none for a declaration without families, otherwise the case schema of a source signature of
the declaration (`CaseSchema.ofCompilation decl s []`) under the key of its first family, with
the ingredients of its certificate. Unlike `VInductBlock.EliminatorsWF`, these ingredients are
monotone along larger environments in which the declaration's families and constructors are
fresh (`OrdinaryCaseEliminators.mono`). -/
def VInductDecl.OrdinaryCaseEliminators (env : VEnv) (decl : VInductDecl)
    (es : List (Name × InductiveSignature.CaseSchema)) : Prop :=
  (decl.types = [] ∧ es = []) ∨
  ∃ (s : InductiveSignature) (key : Name),
    es = [(key, InductiveSignature.CaseSchema.ofCompilation decl s [])] ∧
    decl.types.head?.map (·.name) = some key ∧
    decl.SourceWF env ∧ decl.FormationWF env ∧ s.Models env decl ∧
    ∃ envTypes envCtors, env.addConstVals decl.typeConstants = some envTypes ∧
      envTypes.addConstVals decl.constructorConstants = some envCtors ∧
      s.FamilyTypesWF (envCtors.addProjections decl.projectionEntries) decl.uvars ∧
      (InductiveSignature.CaseSchema.ofCompilation decl s []).ProjNamesRegistered envCtors key ∧
      (InductiveSignature.CaseSchema.ofCompilation decl s []).HeaderAgreement env decl

theorem VInductDecl.OrdinaryCaseEliminators.eliminatorsWF {env : VEnv} {decl : VInductDecl}
    {es : List (Name × InductiveSignature.CaseSchema)} {block : VInductBlock}
    (H : decl.OrdinaryCaseEliminators env es)
    (htypes : block.types = decl.typeConstants) (hctors : block.ctors = decl.constructorConstants)
    (hprojections : block.projections = decl.projectionEntries)
    (heliminators : block.eliminators = es)
    (hadded : ∃ envTypes envCtors, env.addConstVals decl.typeConstants = some envTypes ∧
      envTypes.addConstVals decl.constructorConstants = some envCtors) :
    VInductBlock.EliminatorsWF env decl block := by
  rcases H with ⟨hT, hE⟩ | ⟨s, key, hE, hkey, hsource, hformation, hmodel, envTypes, envCtors,
    ht, hc, hfam, hprojs, hhdr⟩
  · obtain ⟨envTypes, envCtors, ht, hc⟩ := hadded
    exact ⟨envTypes, envCtors, htypes ▸ ht, hctors ▸ hc, .inl ⟨hT, heliminators.trans hE⟩⟩
  · refine ⟨envTypes, envCtors, htypes ▸ ht, hctors ▸ hc,
      .inr ⟨key, _, heliminators.trans hE, ⟨?_, hkey, hhdr⟩, hprojs⟩⟩
    exact InductiveSignature.CaseSchema.ofCaseCompilation_certified
      (InductiveSignature.CaseCompilationData.ofOrdinary hsource hformation hmodel ht hc
        (es := []) (fun _ h => by cases h) hfam htypes hctors hprojections) .nil InductiveSignature.recursorNamesFresh_nil

/-- The block's eliminators are certified over every environment in which its families and
constructors install. Larger safety models of the same production environment are such
environments. -/
def VInductBlock.EliminatorsReplay (env : VEnv) (decl : VInductDecl) (block : VInductBlock) :
    Prop :=
  ∀ envTypes envCtors, env.addConstVals decl.typeConstants = some envTypes →
    envTypes.addConstVals decl.constructorConstants = some envCtors →
    VInductBlock.EliminatorsWF env decl block

theorem VInductBlock.EliminatorsReplay.eliminatorsWF {env : VEnv} {decl : VInductDecl}
    {block : VInductBlock} (H : VInductBlock.EliminatorsReplay env decl block)
    (hdecl : decl.SourceWF env) : VInductBlock.EliminatorsWF env decl block := by
  obtain ⟨-, -, -, -, envTypes, envCtors, ht, hc, -⟩ := hdecl
  exact H envTypes envCtors ht hc

theorem VInductBlock.EliminatorsReplay.congr_block {env : VEnv} {decl : VInductDecl}
    {block block' : VInductBlock} (H : VInductBlock.EliminatorsReplay env decl block)
    (h : block' = block) : VInductBlock.EliminatorsReplay env decl block' := h ▸ H

theorem VInductDecl.OrdinaryCaseEliminators.mono {env env' envTypes' envCtors' : VEnv}
    {decl : VInductDecl} {es : List (Name × InductiveSignature.CaseSchema)}
    (H : decl.OrdinaryCaseEliminators env es) (hle : env ≤ env')
    (htypes' : env'.addConstVals decl.typeConstants = some envTypes')
    (hctors' : envTypes'.addConstVals decl.constructorConstants = some envCtors') :
    decl.OrdinaryCaseEliminators env' es := by
  rcases H with H | ⟨s, key, hE, hkey, hsource, hformation, hmodel, envTypes, envCtors,
    ht, hc, hfam, hprojs, ⟨RP, hRP, hhdr⟩⟩
  · exact .inl H
  have htLE : envTypes ≤ envTypes' := VEnv.addConstVals_mono hle ht htypes'
  have hcLE : envCtors ≤ envCtors' := VEnv.addConstVals_mono htLE hc hctors'
  refine .inr ⟨s, key, hE, hkey, hsource.mono_of_addConstVals hle htypes' hctors',
    hformation.mono_of_addConstVals hle htypes', hmodel.mono hle htypes', envTypes', envCtors',
    htypes', hctors', hfam.mono (VEnv.addProjections_mono hcLE), hprojs.mono hcLE,
    RP, hRP, fun owner => ?_⟩
  obtain ⟨RI, hRI, hagree⟩ := hhdr owner
  refine ⟨RI, hRI, fun type htype hname => ?_⟩
  obtain ⟨envTypes₀, ht₀, hdefeq⟩ := hagree type htype hname
  exact ⟨envTypes', htypes', hdefeq.mono (VEnv.addConstVals_mono hle ht₀ htypes')⟩

/-- The constructor stage of a block with its certified eliminators is well formed, given that
the constructor stage itself is. -/
theorem VInductBlock.EliminatorsWF.casesWF {base envTypes envCtors : VEnv} {decl : VInductDecl}
    {block : VInductBlock} (H : VInductBlock.EliminatorsWF base decl block) (hbase : base.WF)
    (hctorsWF : envCtors.WF)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors) :
    (envCtors.addEliminators block.eliminators).WF := by
  obtain ⟨eT, eC, ht, hc, helim⟩ := H
  cases htypes.symm.trans ht
  cases hctors.symm.trans hc
  rcases helim with ⟨-, hE⟩ | ⟨key, schema, hE, hreg, hprojs⟩
  · rw [hE]; exact hctorsWF
  · rw [hE]
    exact hreg.register_after_constructors hbase htypes hctors hprojs

/-- The case eliminators registered at an ordinary constructor boundary are the declaration's
own restoration-free case schemas. -/
theorem VInductDecl.OrdinaryCaseEliminators.own {env : VEnv} {decl : VInductDecl}
    {es : List (Name × InductiveSignature.CaseSchema)}
    (H : decl.OrdinaryCaseEliminators env es) : decl.OwnCaseEliminators env es := by
  rcases H with ⟨-, hE⟩ | ⟨s, key, hE, -, -, -, hmodel, -⟩
  · intro p hp; rw [hE] at hp; cases hp
  · intro p hp
    rw [hE] at hp
    rcases List.mem_singleton.mp hp with rfl
    exact ⟨rfl, rfl, hmodel⟩

theorem VInductBlock.EliminatorsReplay.congr_fields {env : VEnv} {decl : VInductDecl}
    {block block' : VInductBlock} (H : VInductBlock.EliminatorsReplay env decl block)
    (htypes : block'.types = block.types) (hctors : block'.ctors = block.ctors)
    (hprojections : block'.projections = block.projections)
    (heliminators : block'.eliminators = block.eliminators) :
    VInductBlock.EliminatorsReplay env decl block' := fun T C ht hc =>
  (H T C ht hc).congr_block htypes hctors hprojections heliminators

theorem VInductDecl.OrdinaryCaseEliminators.replay {env env' : VEnv}
    {decl : VInductDecl} {es : List (Name × InductiveSignature.CaseSchema)} {block : VInductBlock}
    (H : decl.OrdinaryCaseEliminators env es) (hle : env ≤ env')
    (htypes : block.types = decl.typeConstants) (hctors : block.ctors = decl.constructorConstants)
    (hprojections : block.projections = decl.projectionEntries)
    (heliminators : block.eliminators = es) :
    VInductBlock.EliminatorsReplay env' decl block := fun _ _ ht hc =>
  (H.mono hle ht hc).eliminatorsWF htypes hctors hprojections heliminators ⟨_, _, ht, hc⟩

end Lean4Lean

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel InductiveSignature

structure ConstructorBoundary (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (nparams : Nat) (isUnsafe : Bool) (depth : Nat)
    (sourceEnv : VEnv) (indTypes : Array InductiveType) where
  headerVEnv : VEnv
  sourceContext : ContextWF c
  sourceContextVEnv : sourceContext.venv = sourceEnv
  sourceMaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
    sourceContext.venv c.lparams sourceContext.mlctx.vlctx stats decl depth
  headerMLCtx : TypeChecker.MLCtx
  headers : HeaderCertificate sourceEnv decl
  params : List VExpr
  headerParams : headers.params = params
  sourceHeaderParams : sourceMaterialized.headers.params = params
  parameterScope : VLCtx
  sourceParameterScope : sourceMaterialized.parameterScope = parameterScope
  materialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
    headerVEnv c.lparams headerMLCtx.vlctx stats decl depth
  materializedParams : materialized.headers.params = params
  materializedParameterScope : materialized.parameterScope = parameterScope
  constructorTails : CheckedRecursorConstructorTails headerVEnv c.lparams
    parameterScope stats decl indTypes
  ctorVEnv : VEnv
  formation : FormationCertificate sourceEnv decl
  core : TrInductDeclCore sourceEnv c.lparams nparams indTypes.toList
    isUnsafe decl headerVEnv ctorVEnv

end Lean4Lean.VerifyInductive


namespace Lean4Lean.VerifyInductive

/-- The window environment of a declaration with certified case eliminators: its constructor
stage with the eliminators, and then with its projection entries, is well formed. -/
theorem _root_.Lean4Lean.VInductBlock.EliminatorsWF.windowWF {base envTypes envCtors : VEnv}
    {decl : VInductDecl} {es : List (Name × InductiveSignature.CaseSchema)}
    {lparams : List Name} {nparams : Nat} {types : List Lean.InductiveType} {isUnsafe : Bool}
    (Hcases : VInductBlock.EliminatorsWF base decl (decl.caseBlock es)) (hbase : base.WF)
    (Hcore : TrInductDeclCore base lparams nparams types isUnsafe decl envTypes envCtors)
    (hparams : decl.SourceParameterWF base) :
    (envCtors.addEliminators es).WF ∧
      ((envCtors.addEliminators es).addProjections decl.projectionEntries).WF := by
  have hcases : (envCtors.addEliminators es).WF :=
    Hcases.casesWF hbase (TrInductDeclCore.envCtorsWF Hcore hbase) Hcore.typesAdded
      Hcore.ctorsAdded
  refine ⟨hcases, ?_⟩
  obtain ⟨_, _, _, _, helim⟩ := Hcases
  rcases helim with ⟨hT, -⟩ | ⟨key, schema, hE, hreg, -⟩
  · rw [VInductDecl.projectionEntries_eq_nil hT]
    exact hcases
  exact VEnv.WF.inductProjections (base := base) (envTypes := envTypes)
    (decl := decl) (block := decl.caseBlock es)
    hbase hcases ⟨key, schema, hE, hreg⟩
    (TrInductDeclCore.sourceNames_nodup Hcore) (TrInductDeclCore.typeHeadersWF Hcore)
    (TrInductDeclCore.constructorUvars Hcore) (TrInductDeclCore.constructorsWF Hcore)
    hparams hparams.rawCtorShape rfl rfl rfl Hcore.typesAdded Hcore.ctorsAdded

end Lean4Lean.VerifyInductive

/-! Source signature selections at the completed constructor boundary. -/

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel InductiveSignature

/-- The exact production telescope retained with a selected constructor.
Typed source correspondence alone cannot recover literal index occurrences
or the translations needed when generating a recursor. -/
def SourceConstructorReplay (env : VEnv) (Us : List Name) (scope : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (target : VInductiveType) (source : Constructor) (sourceCtor : VConstVal)
    (s : InductiveSignature) (ctor : InductiveSignature.Constructor s.families.size) : Prop :=
  ∃ tail tailTarget sourceDomains,
    TrSourceConstRaw env Us source.name source.type sourceCtor ∧
    RecursorParamPrefix stats 0 source.type tail ∧
    CheckedConstructorParameterPrefix env Us stats source.type stats.params.size tail scope sourceDomains ∧
    TrExprS env Us scope tail tailTarget ∧
    ConstructorTailCertificate env decl target scope.toCtx 0 tailTarget ∧
    Nonempty (checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
      env Us (constructorTelescopeTarget sourceCtor) scope tailTarget stats.params.size 0) ∧
    VExpr.wrapForalls s.params tailTarget = s.constructorType ctor

/-- A fixed parameter prefix is injective in its residual expression. -/
private theorem wrapForalls_body_eq {params : List VExpr}
    (H : VExpr.wrapForalls params left = VExpr.wrapForalls params right) : left = right := by
  induction params with
  | nil => exact H
  | cons param params ih => exact ih (VExpr.forallE.inj H).2

/-- The retained tail is the literal generator telescope, so its result
indices and stored field domains are available syntactically as well as by typing. -/
theorem sourceConstructor_tail_eq {s : InductiveSignature}
    {ctor : InductiveSignature.Constructor s.families.size}
    (H : VExpr.wrapForalls s.params tail = s.constructorType ctor) :
    tail = VExpr.wrapForalls (s.fieldTypes ctor)
      (s.familyApp ctor.owner (VLevel.params s.uvars)
        (vars s.params.length ctor.fields.length) ctor.indices) := by
  apply wrapForalls_body_eq (params := s.params)
  simpa only [constructorType, VExpr.wrapForalls_append] using H

/-- The selected constructor keeps the literal result arity already checked
by its original tail certificate. No semantic inversion is required. -/
theorem SourceConstructorReplay.constructorArity
    (H : SourceConstructorReplay env Us scope stats decl target source sourceCtor s ctor)
    (names : (decl.types.map (·.name)).Nodup) (targetMember : target ∈ decl.types)
    (params : s.params.length = decl.nparams)
    (family : s.families[ctor.owner].indices.length = target.numIndices) :
    ctor.indices.length = s.families[ctor.owner].indices.length := by
  obtain ⟨_, _, _, _, _, _, _, certificate, _, literal⟩ := H
  obtain ⟨domains, result, same, application, head⟩ := certificate.raw
  exact constructor_indices_length_of_rawTail names targetMember params family
    ⟨domains, result, same, application.raw, head⟩ (sourceConstructor_tail_eq literal)

/-- A later constructor pass consumes the same cached parameter prefix.
Its residual therefore translates to the literal telescope selected for
generation, without making another normalization choice. -/
theorem SourceConstructorReplay.tailTranslation
    {s : InductiveSignature}
    {ctor : InductiveSignature.Constructor s.families.size}
    (H : SourceConstructorReplay env Us scope stats decl target source sourceCtor s ctor)
    (hprefix : RecursorParamPrefix stats 0 source.type residual) :
    TrExprS env Us scope residual
      (VExpr.wrapForalls (s.fieldTypes ctor)
        (s.familyApp ctor.owner (VLevel.params s.uvars)
          (vars s.params.length ctor.fields.length) ctor.indices)) := by
  obtain ⟨tail, tailTarget, _, _, hchecked, _, htranslation, _, _, htype⟩ := H
  have htail := hchecked.tail_eq hprefix
  have htarget := sourceConstructor_tail_eq htype
  simpa only [← htail, ← htarget] using htranslation

/-- The retained constructor replay produces a generator constructor over
the shared parameter and family table. Its stored type is related to the
actual source constructor chosen by that replay. -/
theorem CheckedConstructorTailReplayAt.signatureConstructor
    {env : VEnv} {decl : VInductDecl} {s : InductiveSignature}
    {Us : List Name} {scope : VLCtx} {source : Constructor}
    {target : VInductiveType}
    (H : CheckedConstructorTailReplayAt env Us scope stats decl target source)
    (henv : env.WF) (hu : Us.length = decl.uvars)
    (huvars : s.uvars = decl.uvars) (hparams : s.params.length = decl.nparams)
    (hnames : s.families.toList.map (·.name) = decl.types.map (·.name))
    (hsafety : s.isUnsafe = decl.isUnsafe)
    (hctx : env.IsDefEqCtx decl.uvars [] s.params.reverse scope.toCtx)
    (owner : Fin s.families.size) (howner : s.families[owner].name = target.name) :
    ∃ sourceCtor ∈ target.ctors, ∃ ctor : InductiveSignature.Constructor s.families.size,
      sourceCtor.name = source.name ∧ ctor.name = source.name ∧ ctor.owner = owner ∧
      env.IsDefEqU decl.uvars [] (s.constructorType ctor) sourceCtor.type ∧
      (∀ i (hi : i < ctor.fields.length),
        SignatureFieldModel env decl s
          (((s.fieldTypes ctor).take i).reverse ++ s.params.reverse) i ctor.fields[i]) ∧
      SourceConstructorReplay env Us scope stats decl target source sourceCtor s ctor := by
  obtain ⟨sourceCtor, tail, tailTarget, sourceDomains, hmem, hraw, hprefix, hcomparisons, htranslation, htail,
    ⟨hsynthesis⟩⟩ := H
  have hindices : hsynthesis.indices = [] :=
    List.eq_nil_of_length_eq_zero hsynthesis.indexCount
  have hscope : scope.toCtx = hsynthesis.params.reverse := by
    simpa only [hindices, List.reverse_nil, List.nil_append] using hsynthesis.scopeCtx
  have huniform := htail.uniform.defeqCtx henv.ordered (hctx.symm henv.ordered)
  obtain ⟨ctor, hname, hctorOwner, htype, hfields⟩ := signatureConstructorOfUniform
    huvars hparams hnames hsafety owner howner source.name huniform
  obtain ⟨level, htailType⟩ := htail.isType
  obtain ⟨closedLevel, hclosed⟩ := (hctx.symm henv.ordered).closeForalls htailType
  have hclosed' : env.IsDefEqU decl.uvars []
      (VExpr.wrapForalls hsynthesis.params tailTarget)
      (VExpr.wrapForalls s.params tailTarget) := by
    simpa only [hscope, List.reverse_reverse] using
      (show env.IsDefEqU decl.uvars []
        (VExpr.wrapForalls scope.toCtx.reverse tailTarget)
        (VExpr.wrapForalls s.params.reverse.reverse tailTarget) from ⟨_, hclosed⟩)
  have hsource : env.IsDefEqU decl.uvars [] sourceCtor.type
      (VExpr.wrapForalls hsynthesis.params tailTarget) := by
    simpa only [constructorTelescopeTarget, hindices, List.append_nil, hu] using
      (show env.IsDefEqU Us.length [] sourceCtor.type
        (VExpr.wrapForalls (hsynthesis.params ++ hsynthesis.indices) tailTarget) from
        ⟨_, hsynthesis.header⟩)
  refine ⟨sourceCtor, hmem, ctor, hraw.name, hname, hctorOwner, ?_, hfields,
    tail, tailTarget, sourceDomains, hraw, hprefix, hcomparisons, htranslation, htail,
    ⟨hsynthesis⟩, htype⟩
  rw [← htype]
  exact (hsource.trans henv trivial hclosed').symm

namespace ConstructorBoundary
variable {isUnsafe : Bool}

/-- Constructor identities are unique in the actual production array as
well as in its translated table. This identifies retained replay witnesses
with the constructors visited by subsequent passes. -/
theorem productionConstructorNames
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    (indTypes.toList.flatMap (·.ctors)).map Lean.Constructor.name =
      decl.constructorConstants.map VConstVal.name := by
  have names : ∀ {sources targets},
      List.Forall₂ (TrInductiveType sourceEnv R.headerVEnv c.lparams) sources targets →
      (sources.flatMap (·.ctors)).map Lean.Constructor.name =
        (targets.flatMap (·.ctors)).map VConstVal.name := by
    intro sources targets H
    induction H with
    | nil => rfl
    | @cons source target sources targets h _ ih =>
      have ctorNames : ∀ {sources targets},
          List.Forall₂ (fun source target => TrSourceConst R.headerVEnv c.lparams
            source.name source.type target) sources targets →
          sources.map Lean.Constructor.name = targets.map VConstVal.name := by
        intro sources targets hc
        induction hc with
        | nil => rfl
        | cons h _ ih => simp only [List.map_cons, h.name, ih]
      have hctors := ctorNames h.ctors
      simpa only [List.flatMap_cons, List.map_append, hctors] using
        congrArg (target.ctors.map VConstVal.name ++ ·) ih
  exact names R.core.types

theorem productionConstructorNames_nodup
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    ((indTypes.toList.flatMap (·.ctors)).map Lean.Constructor.name).Nodup := by
  rw [R.productionConstructorNames]
  exact VEnv.addConstVals_names_nodup R.core.ctorsAdded

/-- Shared source-universe parameters and family choices, before the
eliminator's additional universe is introduced. -/
noncomputable def sourceSignatureHeader
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) : InductiveSignature :=
  R.sourceMaterialized.signatureHeader

theorem sourceSignatureHeader_params
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) : R.sourceSignatureHeader.params = R.params :=
  R.sourceHeaderParams

theorem sourceSignatureHeader_params_length
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) : R.sourceSignatureHeader.params.length = decl.nparams :=
  R.sourceMaterialized.signatureParams_length

theorem sourceSignatureHeader_families
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    List.Forall₂ (fun f src =>
      f.name = src.name ∧ f.indices.length = src.numIndices ∧
      f.resultLevel = src.resultLevel ∧
      sourceEnv.IsDefEqU decl.uvars []
        (VExpr.wrapForalls (R.sourceSignatureHeader.params ++ f.indices) (.sort f.resultLevel))
        src.type)
      R.sourceSignatureHeader.families.toList decl.types := by
  apply Lean4Lean.List.forall₂_of_getElem (by
    simp [sourceSignatureHeader, checkInductiveTypes.loopInd.MaterializedHeaderResult.signatureHeader])
  intro i hi hi'
  obtain ⟨source, _, htr⟩ := Lean4Lean.List.Forall₂.forall_exists_r R.core.types
    _ (List.getElem_mem hi')
  have hu : decl.types[i].uvars = decl.uvars := htr.header.uvars.trans R.core.uvars.symm
  have htype : R.sourceContext.venv.IsType decl.uvars [] decl.types[i].type := by
    simpa only [R.sourceContextVEnv, VConstant.WF, hu] using htr.header.wf
  obtain ⟨hn, hiCount, hl, ht⟩ := R.sourceMaterialized.signatureFamily_model
    R.sourceContext.checking.tr.wf i hi' htype
  simpa [sourceSignatureHeader,
    checkInductiveTypes.loopInd.MaterializedHeaderResult.signatureHeader,
    checkInductiveTypes.loopInd.MaterializedHeaderResult.signatureFamilies,
    R.sourceContextVEnv] using And.intro hn (And.intro hiCount (And.intro hl ht.symm))

/-- Each checked source constructor supplies one constructor over the same
source family table. Ordered source names identify the replay's exact target. -/
theorem sourceSignatureHeader_constructor
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (i : Nat) (hi : i < decl.types.length)
    (j : Nat) (hj : j < decl.types[i].ctors.length) :
    ∃ ctor : InductiveSignature.Constructor R.sourceSignatureHeader.families.size,
      R.sourceSignatureHeader.families[ctor.owner].name = decl.types[i].name ∧
      ctor.name = decl.types[i].ctors[j].name ∧
      R.headerVEnv.IsDefEqU decl.uvars []
        (R.sourceSignatureHeader.constructorType ctor) decl.types[i].ctors[j].type ∧
      (∀ k (hk : k < ctor.fields.length),
        SignatureFieldModel R.headerVEnv decl R.sourceSignatureHeader
          (((R.sourceSignatureHeader.fieldTypes ctor).take k).reverse ++
            R.sourceSignatureHeader.params.reverse) k ctor.fields[k]) ∧
      ∃ production ∈ indTypes.toList.flatMap (·.ctors),
        SourceConstructorReplay R.headerVEnv c.lparams R.parameterScope stats decl
          decl.types[i] production decl.types[i].ctors[j] R.sourceSignatureHeader ctor := by
  have hip : i < indTypes.size := by
    simpa only [R.constructorTails.size_eq] using hi
  have htr := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt R.core i (by simpa using hip) hi
  simp only [Array.getElem_toList] at htr
  have hjp : j < indTypes[i].ctors.length := by
    have hlength := Lean4Lean.List.Forall₂.length_eq htr.ctors
    omega
  have hctor := Lean4Lean.List.forall₂_getElem htr.ctors j (by simpa using hjp) hj
  have henv : sourceEnv.WF := by
    simpa only [R.sourceContextVEnv] using R.sourceContext.checking.tr.wf
  have hctx : R.headerVEnv.IsDefEqCtx decl.uvars []
      R.sourceSignatureHeader.params.reverse R.parameterScope.toCtx := by
    simpa only [R.materialized.uvars, R.materializedParams,
      R.materializedParameterScope, R.sourceSignatureHeader_params] using R.materialized.paramsContext
  let owner : Fin R.sourceSignatureHeader.families.size :=
    ⟨i, by simpa [sourceSignatureHeader,
      checkInductiveTypes.loopInd.MaterializedHeaderResult.signatureHeader] using hi⟩
  have howner : R.sourceSignatureHeader.families[owner].name = decl.types[i].name := by
    simp [owner, sourceSignatureHeader,
      checkInductiveTypes.loopInd.MaterializedHeaderResult.signatureHeader,
      checkInductiveTypes.loopInd.MaterializedHeaderResult.signatureFamilies,
      checkInductiveTypes.loopInd.MaterializedHeaderResult.signatureFamily]
  obtain ⟨sourceCtor, hmem, ctor, hsourceName, hname, hctorOwner, htype, hfields, hreplay⟩ :=
    (R.constructorTails.replay i hip j hjp).signatureConstructor
      (Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF R.core henv) R.core.uvars.symm rfl
      R.sourceSignatureHeader_params_length R.sourceMaterialized.signatureFamilies_names
      rfl hctx owner howner
  have hmem' : sourceCtor ∈ decl.constructorConstants :=
    List.mem_flatMap.mpr ⟨decl.types[i], List.getElem_mem hi, hmem⟩
  have hmemTarget : decl.types[i].ctors[j] ∈ decl.constructorConstants :=
    List.mem_flatMap.mpr ⟨decl.types[i], List.getElem_mem hi, List.getElem_mem hj⟩
  have hsame : sourceCtor = decl.types[i].ctors[j] :=
    List.eq_of_mem_of_nodup_map (VEnv.addConstVals_names_nodup R.core.ctorsAdded)
      hmem' hmemTarget (hsourceName.trans hctor.name.symm)
  cases hsame
  exact ⟨ctor, by simpa only [hctorOwner] using howner,
    hname.trans hsourceName.symm, htype, hfields,
    indTypes[i].ctors[j], List.mem_flatMap.mpr
      ⟨indTypes[i], by simpa using Array.getElem_mem hip, List.getElem_mem hjp⟩, hreplay⟩

theorem sourceSignatureHeader_ownedConstructor
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (pair : VInductiveType × VConstVal) (hpair : pair ∈ decl.ownedConstructors) :
    ∃ ctor : InductiveSignature.Constructor R.sourceSignatureHeader.families.size,
      R.sourceSignatureHeader.families[ctor.owner].name = pair.1.name ∧
      ctor.name = pair.2.name ∧
      R.headerVEnv.IsDefEqU decl.uvars []
        (R.sourceSignatureHeader.constructorType ctor) pair.2.type ∧
      (∀ k (hk : k < ctor.fields.length),
        SignatureFieldModel R.headerVEnv decl R.sourceSignatureHeader
          (((R.sourceSignatureHeader.fieldTypes ctor).take k).reverse ++
            R.sourceSignatureHeader.params.reverse) k ctor.fields[k]) ∧
      ∃ production ∈ indTypes.toList.flatMap (·.ctors),
        SourceConstructorReplay R.headerVEnv c.lparams R.parameterScope stats decl
          pair.1 production pair.2 R.sourceSignatureHeader ctor := by
  obtain ⟨family, hfamily, hmapped⟩ := List.mem_flatMap.mp hpair
  obtain ⟨ctor, hctor, rfl⟩ := List.mem_map.mp hmapped
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hfamily
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hctor
  exact R.sourceSignatureHeader_constructor i hi j hj

/-- Choose each constructor once, in the declaration's exact flattened
order. All later generation uses these same source-universe choices. -/
noncomputable def sourceSignatureConstructor
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) (i : Fin decl.ownedConstructors.length) :
    InductiveSignature.Constructor R.sourceSignatureHeader.families.size :=
  Classical.choose (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem i.isLt))

noncomputable def sourceSignature
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) : InductiveSignature :=
  { R.sourceSignatureHeader with
    constructors := Array.ofFn R.sourceSignatureConstructor }

theorem sourceSignatureConstructor_name
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) (i : Fin decl.ownedConstructors.length) :
    (R.sourceSignatureConstructor i).name = decl.ownedConstructors[i].2.name :=
  (Classical.choose_spec
    (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem i.isLt))).2.1

/-- The selected constructor keeps its source family's position, not just
its name. Distinct installed header names determine the owner index. -/
theorem sourceSignatureConstructor_owner
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) (i : Fin decl.ownedConstructors.length)
    (owner : Nat) (howner : owner < decl.types.length)
    (hfamily : decl.ownedConstructors[i].1 = decl.types[owner]) :
    (R.sourceSignatureConstructor i).owner.val = owner := by
  have hmodel := Classical.choose_spec
    (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem i.isLt))
  let ctor := R.sourceSignatureConstructor i
  have hsize : R.sourceSignatureHeader.families.size = decl.types.length :=
    R.sourceMaterialized.signatureFamilies_size
  have hc : ctor.owner.val < decl.types.length := by
    have := ctor.owner.isLt
    omega
  have hf := Lean4Lean.List.forall₂_getElem R.sourceSignatureHeader_families
    ctor.owner.val (by simpa using ctor.owner.isLt) hc
  have hname : decl.types[ctor.owner.val].name = decl.types[owner].name := by
    have hm : R.sourceSignatureHeader.families[ctor.owner].name =
        decl.ownedConstructors[i].1.name := hmodel.1
    exact hf.1.symm.trans (hm.trans (congrArg (fun family : VInductiveType => family.name) hfamily))
  have hnames : (decl.types.map (fun family => family.name)).Nodup := by
    simpa only [VInductDecl.typeConstants, List.map_map, Function.comp_def] using
      VEnv.addConstVals_names_nodup R.core.typesAdded
  apply (List.getElem_inj (h₀ := by simpa using hc)
    (h₁ := by simpa using howner) hnames).mp
  simpa only [List.getElem_map] using hname

theorem sourceSignature_fieldType
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) (field : Field R.sourceSignatureHeader.families.size) :
    R.sourceSignature.fieldType k field = R.sourceSignatureHeader.fieldType k field := by
  cases field <;> rfl

theorem sourceSignature_fieldTypes
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) (ctor : InductiveSignature.Constructor R.sourceSignatureHeader.families.size) :
    R.sourceSignature.fieldTypes ctor = R.sourceSignatureHeader.fieldTypes ctor := by
  unfold fieldTypes
  apply List.map_congr_left
  intro field _
  exact R.sourceSignature_fieldType field.1

theorem sourceSignature_constructorType
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) (ctor : InductiveSignature.Constructor R.sourceSignatureHeader.families.size) :
    R.sourceSignature.constructorType ctor = R.sourceSignatureHeader.constructorType ctor := by
  simp only [constructorType, sourceSignature_fieldTypes]
  rfl

theorem sourceSignature_fieldModel
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) (field : Field R.sourceSignatureHeader.families.size) :
    SignatureFieldModel env decl' R.sourceSignature ctx k field ↔
      SignatureFieldModel env decl' R.sourceSignatureHeader ctx k field := by
  cases field <;> rfl

/-- Every selected source constructor keeps its exact production replay,
including the literal tail used to determine fields and result indices. -/
theorem sourceSignatureConstructor_replay
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) (i : Fin decl.ownedConstructors.length) :
    ∃ production ∈ indTypes.toList.flatMap (·.ctors),
      SourceConstructorReplay R.headerVEnv c.lparams R.parameterScope stats decl
        decl.ownedConstructors[i].1 production decl.ownedConstructors[i].2
        R.sourceSignature (R.sourceSignatureConstructor i) := by
  have hmodel := Classical.choose_spec
    (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem i.isLt))
  obtain ⟨production, hproduction, tail, tailTarget, sourceDomains,
    hraw, hprefix, hcomparisons, htranslation, htail, hsynthesis, htype⟩ := hmodel.2.2.2.2
  refine ⟨production, hproduction, tail, tailTarget, sourceDomains,
    hraw, hprefix, hcomparisons, htranslation, htail, hsynthesis, ?_⟩
  rw [sourceSignature_constructorType]
  exact htype

/-- The selected replay belongs to the actual production constructor with
this name. Global constructor freshness rules out a different source
telescope hidden by the existential replay witness. -/
theorem sourceSignature_replay_of_source
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) (i : Fin decl.ownedConstructors.length)
    (source : Constructor) (hsource : source ∈ indTypes.toList.flatMap (·.ctors))
    (hname : source.name = decl.ownedConstructors[i].2.name) :
    SourceConstructorReplay R.headerVEnv c.lparams R.parameterScope stats decl
      decl.ownedConstructors[i].1 source decl.ownedConstructors[i].2
      R.sourceSignature (R.sourceSignatureConstructor i) := by
  obtain ⟨production, hproduction, hreplay⟩ := R.sourceSignatureConstructor_replay i
  have hraw := hreplay
  obtain ⟨_, _, _, hraw, _⟩ := hraw
  have heq : production = source := List.eq_of_mem_of_nodup_map
    R.productionConstructorNames_nodup hproduction hsource
    (hraw.name.symm.trans hname.symm)
  simpa only [heq] using hreplay

/-- Arity comes from the exact retained replay of each selected constructor,
not from comparing the types of a fully applied family. -/
theorem sourceSignature_constructorArity
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    ∀ ctor ∈ R.sourceSignature.constructors.toList,
      ctor.indices.length = R.sourceSignature.families[ctor.owner].indices.length := by
  intro ctor member
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp member
  have hi' : i < decl.ownedConstructors.length := by simpa [sourceSignature] using hi
  let position : Fin decl.ownedConstructors.length := ⟨i, hi'⟩
  have hget : R.sourceSignature.constructors.toList[i] = R.sourceSignatureConstructor position := by
    simp only [sourceSignature, Array.getElem_toList, Array.getElem_ofFn, position]
  rw [hget]
  obtain ⟨production, _, replay⟩ := R.sourceSignatureConstructor_replay position
  have chosen := Classical.choose_spec
    (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem hi'))
  have targetMember : decl.ownedConstructors[i].1 ∈ decl.types := by
    have member := List.getElem_mem hi'
    obtain ⟨family, hfamily, constructor⟩ := List.mem_flatMap.mp member
    obtain ⟨_, _, same⟩ := List.mem_map.mp constructor
    exact (congrArg Prod.fst same) ▸ hfamily
  have names : (decl.types.map (·.name)).Nodup := by
    simpa only [VInductDecl.typeConstants, List.map_map, Function.comp_def] using
      VEnv.addConstVals_names_nodup R.core.typesAdded
  have ownerBound : (R.sourceSignatureConstructor position).owner.val < decl.types.length := by
    have bound := (R.sourceSignatureConstructor position).owner.isLt
    simpa only [sourceSignatureHeader,
      checkInductiveTypes.loopInd.MaterializedHeaderResult.signatureHeader,
      checkInductiveTypes.loopInd.MaterializedHeaderResult.signatureFamilies_size] using bound
  have family := Lean4Lean.List.forall₂_getElem R.sourceSignatureHeader_families
    (R.sourceSignatureConstructor position).owner.val
    (by simpa using (R.sourceSignatureConstructor position).owner.isLt) ownerBound
  have same : decl.types[(R.sourceSignatureConstructor position).owner.val] =
      decl.ownedConstructors[i].1 :=
    List.eq_of_mem_of_nodup_map names (List.getElem_mem ownerBound) targetMember
      (family.1.symm.trans chosen.1)
  apply replay.constructorArity names targetMember R.sourceSignatureHeader_params_length
  simpa only [sourceSignature, Array.getElem_toList, Fin.getElem_fin, same, position] using family.2.1

/-- The complete checked source signature models the original declaration.
Its normalization choices are fixed before recursor generation begins. -/
private theorem sourceSignature_models_of_nonempty
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) (hnonempty : decl.types ≠ []) :
    R.sourceSignature.Models sourceEnv decl := by
  apply sourceModelsOfTables (s := R.sourceSignature)
    (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceWF R.core hnonempty
      (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core)) R.core.typesAdded rfl
    R.sourceSignatureHeader_params_length rfl
  · exact Lean4Lean.List.Forall₂.imp (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
      R.sourceSignatureHeader_families
  · apply Lean4Lean.List.forall₂_of_getElem (by simp [sourceSignature])
    intro i hi hi'
    have hmodel := Classical.choose_spec
      (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem hi'))
    have hget : R.sourceSignature.constructors.toList[i] =
        R.sourceSignatureConstructor ⟨i, hi'⟩ := by
      simp only [sourceSignature, Array.getElem_toList, Array.getElem_ofFn]
    rw [hget]
    refine ⟨hmodel.1, hmodel.2.1, ?_⟩
    have ht : R.headerVEnv.IsDefEqU decl.uvars []
        (R.sourceSignatureHeader.constructorType (R.sourceSignatureConstructor ⟨i, hi'⟩))
        decl.ownedConstructors[i].2.type := hmodel.2.2.1
    simpa only [sourceSignature_constructorType] using ht
  · intro ctor hctor k hk
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hctor
    have hi' : i < decl.ownedConstructors.length := by
      simpa [sourceSignature] using hi
    have hmodel := Classical.choose_spec
      (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem hi'))
    have hget : R.sourceSignature.constructors.toList[i] =
        R.sourceSignatureConstructor ⟨i, hi'⟩ := by
      simp only [sourceSignature, Array.getElem_toList, Array.getElem_ofFn]
    simp only [hget] at hk ⊢
    have hf : SignatureFieldModel R.headerVEnv decl R.sourceSignatureHeader
        (((R.sourceSignatureHeader.fieldTypes (R.sourceSignatureConstructor ⟨i, hi'⟩)).take k).reverse ++
          R.sourceSignatureHeader.params.reverse) k
        (R.sourceSignatureConstructor ⟨i, hi'⟩).fields[k] := hmodel.2.2.2.1 k hk
    apply (R.sourceSignature_fieldModel _).2
    rw [sourceSignature_fieldTypes]
    change SignatureFieldModel R.headerVEnv decl R.sourceSignatureHeader
      (((R.sourceSignatureHeader.fieldTypes (R.sourceSignatureConstructor ⟨i, hi'⟩)).take k).reverse ++
        R.sourceSignatureHeader.params.reverse) k
      (R.sourceSignatureConstructor ⟨i, hi'⟩).fields[k]
    exact hf
  · exact R.sourceSignature_constructorArity

/-- Source extraction is total even for an empty intermediate table; the
public installation boundary separately enforces declaration nonemptiness. -/
theorem sourceSignature_models
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) : R.sourceSignature.Models sourceEnv decl := by
  by_cases hempty : decl.types = []
  · have hfamilies : R.sourceSignature.families = #[] := by
      apply Array.eq_empty_of_size_eq_zero
      simp [sourceSignature, sourceSignatureHeader,
        checkInductiveTypes.loopInd.MaterializedHeaderResult.signatureHeader, hempty]
    have hctors : R.sourceSignature.constructors = #[] := by
      apply Array.eq_empty_of_size_eq_zero
      simp only [sourceSignature, Array.size_ofFn]
      simp [VInductDecl.ownedConstructors, hempty]
    refine ⟨rfl, R.sourceSignatureHeader_params_length, rfl, ?_,
      ⟨R.headerVEnv, R.core.typesAdded, ?_⟩,
      .inr ⟨R.headerVEnv, R.core.typesAdded, ?_⟩, ?_⟩
    all_goals simp [declaration, hfamilies, hctors, VInductDecl.constructorConstants, hempty]
  · exact R.sourceSignature_models_of_nonempty hempty

/-! ### The case eliminator certified at the constructor boundary -/

theorem headerWF
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    R.headerVEnv.WF :=
  Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF R.core
    (by rw [← R.sourceContextVEnv]; exact R.sourceContext.checking.tr.wf)

/-- The family applications of the source signature are typed in the header environment. -/
theorem sourceSignature_familyTypesWF_header
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    R.sourceSignature.FamilyTypesWF R.headerVEnv decl.uvars := by
  intro owner
  have henv := R.headerWF
  have hle : sourceEnv ≤ R.headerVEnv := VEnv.addConstVals_le R.core.typesAdded
  have hheader : owner.val < R.sourceSignatureHeader.families.size := owner.isLt
  have hdecl : owner.val < decl.types.length := by
    have := Lean4Lean.List.Forall₂.length_eq R.sourceSignatureHeader_families
    simp only [Array.length_toList] at this
    omega
  have hfam := Lean4Lean.List.forall₂_getElem R.sourceSignatureHeader_families owner.val
    (by simpa using hheader) hdecl
  simp only [Array.getElem_toList] at hfam
  obtain ⟨hname, _, _, hdefeq⟩ := hfam
  have hmem : decl.types[owner.val] ∈ decl.types := List.getElem_mem hdecl
  have hsourceWF := Lean4Lean.VerifyInductive.TrInductDeclCore.sourceWF R.core
    (List.ne_nil_of_mem hmem) (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core)
  have huvars : decl.types[owner.val].uvars = decl.uvars := hsourceWF.2.2.1 _ hmem
  have hlookup : R.headerVEnv.constants decl.types[owner.val].name =
      some decl.types[owner.val].toVConstant :=
    VEnv.addConstVals_get R.core.typesAdded (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  have hconst := VEnv.HasType.const0 hlookup (henv.ordered.constWF hlookup)
  change R.headerVEnv.HasType decl.types[owner.val].uvars [] (.const decl.types[owner.val].name
      (VLevel.params decl.types[owner.val].uvars)) decl.types[owner.val].type at hconst
  rw [huvars, ← hname] at hconst
  have hW := hconst.defeqU_r henv trivial (hdefeq.symm.mono hle)
  have hWT := hW.isType henv.ordered trivial
  have hctx := (VEnv.IsType.wrapForalls_inv henv.ordered (ctx := []) trivial hWT).1
  simp only [List.append_nil] at hctx
  have happ := VEnv.HasType.mkApps_bvarRange henv hW hctx trivial
  have hctx' : OnCtx (R.sourceSignatureHeader.families[owner.val].indices.reverse ++
      R.sourceSignatureHeader.params.reverse) (R.headerVEnv.IsType decl.uvars) := by
    simpa [List.reverse_append] using hctx
  refine ⟨hctx', ?_⟩
  change R.headerVEnv.HasType decl.uvars
    (R.sourceSignatureHeader.families[owner.val].indices.reverse ++
      R.sourceSignatureHeader.params.reverse)
    (VExpr.mkApps (.const R.sourceSignatureHeader.families[owner.val].name
      (VLevel.params decl.uvars))
      (InductiveSignature.vars R.sourceSignatureHeader.params.length
          R.sourceSignatureHeader.families[owner.val].indices.length ++
        InductiveSignature.vars R.sourceSignatureHeader.families[owner.val].indices.length 0))
    (.sort R.sourceSignatureHeader.families[owner.val].resultLevel)
  rw [InductiveSignature.vars_append_eq_bvarRange, ← List.length_append]
  simpa [List.reverse_append] using happ

/-- The key of the declaration's case eliminator: its first family. -/
noncomputable def caseKey
    (_R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) : Name :=
  (decl.types.head?.map (·.name)).getD default

/-- The declaration's case schema: the source signature, without restoration. -/
noncomputable def caseSchema
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    InductiveSignature.CaseSchema :=
  InductiveSignature.CaseSchema.ofCompilation decl R.sourceSignature []

open Classical in
/-- The declaration's case eliminators: none for an empty declaration (which has no
projections), its case schema under its key otherwise. -/
noncomputable def caseEliminators
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    List (Name × InductiveSignature.CaseSchema) :=
  if decl.types = [] then [] else [(R.caseKey, R.caseSchema)]

private theorem mapM_expr_empty (l : List VExpr) :
    l.mapM ({} : InductiveSignature.Restoration).expr = some l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.mapM_cons, ih]

/-- Every piece of the source signature projects only out of structures registered at the
constructor boundary. -/
theorem caseSchema_projNamesRegistered
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (hdeclNe : decl.types ≠ []) :
    R.caseSchema.ProjNamesRegistered R.ctorVEnv R.caseKey := by
  have hsrcWF : sourceEnv.WF := by
    rw [← R.sourceContextVEnv]; exact R.sourceContext.checking.tr.wf
  have hleH : sourceEnv ≤ R.headerVEnv := VEnv.addConstVals_le R.core.typesAdded
  have hleC : R.headerVEnv ≤ R.ctorVEnv := VEnv.addConstVals_le R.core.ctorsAdded
  have hokS : ∀ {e : VExpr}, e.ProjNamesOK (fun S => ∃ info, sourceEnv.projections S info) →
      e.ProjNamesOK (fun S => ∃ info, R.ctorVEnv.projections S info) :=
    VExpr.ProjNamesOK.mono fun _ ⟨info, h⟩ => ⟨info, (hleH.trans hleC).projections h⟩
  have hokH : ∀ {e : VExpr}, e.ProjNamesOK (fun S => ∃ info, R.headerVEnv.projections S info) →
      e.ProjNamesOK (fun S => ∃ info, R.ctorVEnv.projections S info) :=
    VExpr.ProjNamesOK.mono fun _ ⟨info, h⟩ => ⟨info, hleC.projections h⟩
  -- the header pieces
  have hheaders : ∀ f ∈ R.sourceSignatureHeader.families.toList,
      (VExpr.wrapForalls (R.sourceSignatureHeader.params ++ f.indices) (.sort f.resultLevel)).ProjNamesOK
        (fun S => ∃ info, sourceEnv.projections S info) := by
    intro f hf
    obtain ⟨src, _, h⟩ := Lean4Lean.List.Forall₂.forall_exists_l R.sourceSignatureHeader_families f hf
    obtain ⟨_, hd⟩ := h.2.2.2
    exact (hd.projNamesOK hsrcWF.ordered trivial).1
  have hfamNe : 0 < R.sourceSignatureHeader.families.size := by
    have := Lean4Lean.List.Forall₂.length_eq R.sourceSignatureHeader_families
    simp only [Array.length_toList] at this
    have : 0 < decl.types.length := List.length_pos_iff.mpr hdeclNe
    omega
  have hparams : ∀ e ∈ R.caseSchema.signature.params,
      e.ProjNamesOK (fun S => ∃ info, R.ctorVEnv.projections S info) := by
    intro e he
    have h := (VExpr.ProjNamesOK.wrapForalls_inv
      (hheaders _ (Array.getElem_mem_toList (i := 0) hfamNe))).1 e (List.mem_append_left _ he)
    exact hokS h
  have hindices : ∀ f ∈ R.caseSchema.signature.families.toList, ∀ e ∈ f.indices,
      e.ProjNamesOK (fun S => ∃ info, R.ctorVEnv.projections S info) := by
    intro f hf e he
    exact hokS ((VExpr.ProjNamesOK.wrapForalls_inv (hheaders f hf)).1 e (List.mem_append_right _ he))
  have hctor' : ∀ i : Fin decl.ownedConstructors.length,
      (R.sourceSignatureHeader.constructorType (R.sourceSignatureConstructor i)).ProjNamesOK
        (fun S => ∃ info, R.ctorVEnv.projections S info) := by
    intro i
    obtain ⟨_, _, hdef, _⟩ := Classical.choose_spec
      (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem i.isLt))
    obtain ⟨_, hd⟩ := hdef
    exact hokH (hd.projNamesOK R.headerWF.ordered trivial).1
  have hmem : ∀ c ∈ R.caseSchema.signature.constructors.toList,
      ∃ i, R.sourceSignatureConstructor i = c := by
    intro c hc
    have hc' : c ∈ (Array.ofFn R.sourceSignatureConstructor).toList := hc
    rw [Array.toList_ofFn] at hc'
    exact List.mem_ofFn.mp hc'
  have hfields : ∀ c ∈ R.caseSchema.signature.constructors.toList,
      ∀ e ∈ R.caseSchema.signature.fieldTypes c,
        e.ProjNamesOK (fun S => ∃ info, R.ctorVEnv.projections S info) := by
    intro c hc e he
    obtain ⟨i, rfl⟩ := hmem c hc
    have h := VExpr.ProjNamesOK.wrapForalls_inv (hctor' i)
    have he' : e ∈ R.sourceSignature.fieldTypes (R.sourceSignatureConstructor i) := he
    rw [R.sourceSignature_fieldTypes] at he'
    exact h.1 e (List.mem_append_right _ he')
  have hcindices : ∀ c ∈ R.caseSchema.signature.constructors.toList, ∀ e ∈ c.indices,
      e.ProjNamesOK (fun S => ∃ info, R.ctorVEnv.projections S info) := by
    intro c hc e he
    obtain ⟨i, rfl⟩ := hmem c hc
    have h := (VExpr.ProjNamesOK.wrapForalls_inv (hctor' i)).2
    exact (VExpr.ProjNamesOK.mkApps_inv h).2 e (List.mem_append_right _ he)
  have H := InductiveSignature.CaseSchema.projNamesOK_of_pieces (schema := R.caseSchema) rfl
    hparams hindices hfields hcindices R.caseKey
  exact ⟨H.1, H.2⟩

/-- The original families' declared headers are their normalized headers. -/
theorem caseSchema_headerAgreement
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    R.caseSchema.HeaderAgreement sourceEnv decl := by
  refine ⟨R.sourceSignatureHeader.params, mapM_expr_empty _, fun owner => ?_⟩
  refine ⟨(R.sourceSignatureHeader.families[owner.val]'owner.isLt).indices, mapM_expr_empty _,
    fun type htype hname => ⟨R.headerVEnv, R.core.typesAdded, ?_⟩⟩
  have hdecl : owner.val < decl.types.length := by
    have := Lean4Lean.List.Forall₂.length_eq R.sourceSignatureHeader_families
    simp only [Array.length_toList] at this
    have := owner.isLt
    change owner.val < R.sourceSignatureHeader.families.size at this
    omega
  have hown : owner.val < R.sourceSignatureHeader.families.size := owner.isLt
  have hfam := Lean4Lean.List.forall₂_getElem R.sourceSignatureHeader_families owner.val
    (by simpa using hown) hdecl
  simp only [Array.getElem_toList] at hfam
  obtain ⟨hname', _, _, hdefeq⟩ := hfam
  have hsame : type = decl.types[owner.val] := by
    have hnodup : (decl.types.map (·.name)).Nodup := by
      have := Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core
      simp only [VInductDecl.sourceNames, VInductDecl.typeConstants, List.map_map] at this
      exact (List.nodup_append.mp this).1
    exact List.eq_of_mem_of_nodup_map hnodup htype (List.getElem_mem hdecl)
      (hname.trans hname')
  subst hsame
  exact (hdefeq.mono (VEnv.addConstVals_le R.core.typesAdded)).symm

/-- **The declaration's case eliminator is certified at the constructor boundary.** -/
theorem caseEliminatorsWF
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    VInductBlock.EliminatorsWF sourceEnv decl (decl.caseBlock R.caseEliminators) := by
  refine ⟨R.headerVEnv, R.ctorVEnv, R.core.typesAdded, R.core.ctorsAdded, ?_⟩
  by_cases hne : decl.types = []
  · exact .inl ⟨hne, by simp [VInductDecl.caseBlock, caseEliminators, hne]⟩
  refine .inr ⟨R.caseKey, R.caseSchema, by simp [VInductDecl.caseBlock, caseEliminators, hne],
    ⟨?_, ?_, R.caseSchema_headerAgreement⟩, R.caseSchema_projNamesRegistered hne⟩
  · have hsource := Lean4Lean.VerifyInductive.TrInductDeclCore.sourceWF R.core hne
      (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core)
    exact InductiveSignature.CaseSchema.ofCaseCompilation_certified
      (InductiveSignature.CaseCompilationData.ofOrdinary hsource R.formation.formationWF
        R.sourceSignature_models R.core.typesAdded R.core.ctorsAdded
        (es := []) (fun _ h => by cases h)
        (R.sourceSignature_familyTypesWF_header.mono
          ((VEnv.addConstVals_le R.core.ctorsAdded).trans VEnv.addProjections_le))
        rfl rfl rfl) .nil InductiveSignature.recursorNamesFresh_nil
  · cases htypes : decl.types with
    | nil => exact absurd htypes hne
    | cons family families => simp [caseKey, htypes]

/-- The declaration's case eliminators, with the monotone ingredients of their certificate. -/
theorem caseEliminatorsOrdinary
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    decl.OrdinaryCaseEliminators sourceEnv R.caseEliminators := by
  by_cases hne : decl.types = []
  · exact .inl ⟨hne, by simp [caseEliminators, hne]⟩
  refine .inr ⟨R.sourceSignature, R.caseKey, by simp [caseEliminators, hne, caseSchema], ?_,
    Lean4Lean.VerifyInductive.TrInductDeclCore.sourceWF R.core hne
      (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core),
    R.formation.formationWF, R.sourceSignature_models, R.headerVEnv, R.ctorVEnv,
    R.core.typesAdded, R.core.ctorsAdded,
    R.sourceSignature_familyTypesWF_header.mono
      ((VEnv.addConstVals_le R.core.ctorsAdded).trans VEnv.addProjections_le),
    R.caseSchema_projNamesRegistered hne, R.caseSchema_headerAgreement⟩
  cases htypes : decl.types with
  | nil => exact absurd htypes hne
  | cons family families => simp [caseKey, htypes]

/-- The constructor stage with the declaration's case eliminators is well formed. -/
theorem casesWF
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    (R.ctorVEnv.addEliminators R.caseEliminators).WF := by
  have hsourceWF : sourceEnv.WF := by
    rw [← R.sourceContextVEnv]; exact R.sourceContext.checking.tr.wf
  obtain ⟨eT, eC, ht, hc, helim⟩ := R.caseEliminatorsWF
  obtain rfl : R.headerVEnv = eT := Option.some.inj (R.core.typesAdded.symm.trans ht)
  obtain rfl : R.ctorVEnv = eC := Option.some.inj (R.core.ctorsAdded.symm.trans hc)
  rcases helim with ⟨-, hE⟩ | ⟨key, schema, hE, hreg, hprojs⟩
  · rw [show R.caseEliminators = [] from hE]
    exact Lean4Lean.VerifyInductive.TrInductDeclCore.envCtorsWF R.core hsourceWF
  · rw [show R.caseEliminators = [(key, schema)] from hE]
    have := hreg.register_after_constructors hsourceWF ht hc hprojs
    simpa [VInductDecl.caseBlock, VEnv.addEliminators] using this

/-- The constructor stage with the declaration's case eliminators and projections is well
formed. -/
theorem projectedWF
    (R : ConstructorBoundary c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    ((R.ctorVEnv.addEliminators R.caseEliminators).addProjections decl.projectionEntries).WF := by
  have hsourceWF : sourceEnv.WF := by
    rw [← R.sourceContextVEnv]; exact R.sourceContext.checking.tr.wf
  have hcases := R.casesWF
  obtain ⟨_, _, ht, hc, helim⟩ := R.caseEliminatorsWF
  rcases helim with ⟨hT, -⟩ | ⟨key, schema, hE, hreg, -⟩
  · rw [VInductDecl.projectionEntries_eq_nil hT]
    exact hcases
  have hparams : decl.SourceParameterWF sourceEnv := R.formation.formationWF.sourceParameterWF
  exact VEnv.WF.inductProjections (base := sourceEnv) (envTypes := R.headerVEnv)
    (decl := decl) (block := decl.caseBlock R.caseEliminators)
    hsourceWF hcases ⟨key, schema, hE, hreg⟩
    (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core)
    (Lean4Lean.VerifyInductive.TrInductDeclCore.typeHeadersWF R.core)
    (Lean4Lean.VerifyInductive.TrInductDeclCore.constructorUvars R.core)
    (Lean4Lean.VerifyInductive.TrInductDeclCore.constructorsWF R.core)
    hparams hparams.rawCtorShape rfl rfl rfl R.core.typesAdded R.core.ctorsAdded

end ConstructorBoundary
end Lean4Lean.VerifyInductive
