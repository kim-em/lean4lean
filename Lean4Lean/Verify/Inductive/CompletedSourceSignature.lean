import Lean4Lean.Verify.Inductive.CompletedConstructorPhases
import Lean4Lean.Verify.Inductive.SourceModels
import Lean4Lean.Theory.Inductive.ConstructorArity

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
        SignatureFieldModel env decl.uvars s
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

namespace CompletedConstructorPhases
variable {isUnsafe : Bool}

/-- Constructor identities are unique in the actual production array as
well as in its translated table. This identifies retained replay witnesses
with the constructors visited by subsequent passes. -/
theorem productionConstructorNames
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
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
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    ((indTypes.toList.flatMap (·.ctors)).map Lean.Constructor.name).Nodup := by
  rw [R.productionConstructorNames]
  exact VEnv.addConstVals_names_nodup R.core.ctorsAdded

/-- Shared source-universe parameters and family choices, before the
eliminator's additional universe is introduced. -/
noncomputable def sourceSignatureHeader
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) : InductiveSignature :=
  R.sourceMaterialized.signatureHeader

theorem sourceSignatureHeader_params
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) : R.sourceSignatureHeader.params = R.params :=
  R.sourceHeaderParams

theorem sourceSignatureHeader_params_length
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) : R.sourceSignatureHeader.params.length = decl.nparams :=
  R.sourceMaterialized.signatureParams_length

theorem sourceSignatureHeader_families
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
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
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (i : Nat) (hi : i < decl.types.length)
    (j : Nat) (hj : j < decl.types[i].ctors.length) :
    ∃ ctor : InductiveSignature.Constructor R.sourceSignatureHeader.families.size,
      R.sourceSignatureHeader.families[ctor.owner].name = decl.types[i].name ∧
      ctor.name = decl.types[i].ctors[j].name ∧
      R.headerVEnv.IsDefEqU decl.uvars []
        (R.sourceSignatureHeader.constructorType ctor) decl.types[i].ctors[j].type ∧
      (∀ k (hk : k < ctor.fields.length),
        SignatureFieldModel R.headerVEnv decl.uvars R.sourceSignatureHeader
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
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (pair : VInductiveType × VConstVal) (hpair : pair ∈ decl.ownedConstructors) :
    ∃ ctor : InductiveSignature.Constructor R.sourceSignatureHeader.families.size,
      R.sourceSignatureHeader.families[ctor.owner].name = pair.1.name ∧
      ctor.name = pair.2.name ∧
      R.headerVEnv.IsDefEqU decl.uvars []
        (R.sourceSignatureHeader.constructorType ctor) pair.2.type ∧
      (∀ k (hk : k < ctor.fields.length),
        SignatureFieldModel R.headerVEnv decl.uvars R.sourceSignatureHeader
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
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) (i : Fin decl.ownedConstructors.length) :
    InductiveSignature.Constructor R.sourceSignatureHeader.families.size :=
  Classical.choose (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem i.isLt))

noncomputable def sourceSignature
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) : InductiveSignature :=
  { R.sourceSignatureHeader with
    constructors := Array.ofFn R.sourceSignatureConstructor }

theorem sourceSignatureConstructor_name
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) (i : Fin decl.ownedConstructors.length) :
    (R.sourceSignatureConstructor i).name = decl.ownedConstructors[i].2.name :=
  (Classical.choose_spec
    (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem i.isLt))).2.1

/-- The selected constructor keeps its source family's position, not just
its name. Distinct installed header names determine the owner index. -/
theorem sourceSignatureConstructor_owner
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) (i : Fin decl.ownedConstructors.length)
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
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) (field : Field R.sourceSignatureHeader.families.size) :
    R.sourceSignature.fieldType k field = R.sourceSignatureHeader.fieldType k field := by
  cases field <;> rfl

theorem sourceSignature_fieldTypes
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) (ctor : InductiveSignature.Constructor R.sourceSignatureHeader.families.size) :
    R.sourceSignature.fieldTypes ctor = R.sourceSignatureHeader.fieldTypes ctor := by
  unfold fieldTypes
  apply List.map_congr_left
  intro field _
  exact R.sourceSignature_fieldType field.1

theorem sourceSignature_constructorType
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) (ctor : InductiveSignature.Constructor R.sourceSignatureHeader.families.size) :
    R.sourceSignature.constructorType ctor = R.sourceSignatureHeader.constructorType ctor := by
  simp only [constructorType, sourceSignature_fieldTypes]
  rfl

theorem sourceSignature_fieldModel
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) (field : Field R.sourceSignatureHeader.families.size) :
    SignatureFieldModel env U R.sourceSignature ctx k field ↔
      SignatureFieldModel env U R.sourceSignatureHeader ctx k field := by
  cases field <;> rfl

/-- Every selected source constructor keeps its exact production replay,
including the literal tail used to determine fields and result indices. -/
theorem sourceSignatureConstructor_replay
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) (i : Fin decl.ownedConstructors.length) :
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

theorem sourceSignature_replay
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) (i : Fin decl.ownedConstructors.length) :
    ∃ production ∈ indTypes.toList.flatMap (·.ctors),
      SourceConstructorReplay R.headerVEnv c.lparams R.parameterScope stats decl
        decl.ownedConstructors[i].1 production decl.ownedConstructors[i].2
        R.sourceSignature (R.sourceSignature.constructors[i.val]'(by
          simp only [sourceSignature, Array.size_ofFn]; exact i.isLt)) := by
  simpa [sourceSignature] using R.sourceSignatureConstructor_replay i

/-- The selected replay belongs to the actual production constructor with
this name. Global constructor freshness rules out a different source
telescope hidden by the existential replay witness. -/
theorem sourceSignature_replay_of_source
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) (i : Fin decl.ownedConstructors.length)
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
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
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
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) (hnonempty : decl.types ≠ []) :
    R.sourceSignature.Models sourceEnv decl := by
  apply sourceModelsOfTables (s := R.sourceSignature)
    (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceWF R.core hnonempty
      (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core)) R.core.typesAdded rfl
    R.sourceSignatureHeader_params_length rfl
  · exact R.sourceSignatureHeader_families
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
    have hf : SignatureFieldModel R.headerVEnv decl.uvars R.sourceSignatureHeader
        (((R.sourceSignatureHeader.fieldTypes (R.sourceSignatureConstructor ⟨i, hi'⟩)).take k).reverse ++
          R.sourceSignatureHeader.params.reverse) k
        (R.sourceSignatureConstructor ⟨i, hi'⟩).fields[k] := hmodel.2.2.2.1 k hk
    apply (R.sourceSignature_fieldModel _).2
    rw [sourceSignature_fieldTypes]
    change SignatureFieldModel R.headerVEnv decl.uvars R.sourceSignatureHeader
      (((R.sourceSignatureHeader.fieldTypes (R.sourceSignatureConstructor ⟨i, hi'⟩)).take k).reverse ++
        R.sourceSignatureHeader.params.reverse) k
      (R.sourceSignatureConstructor ⟨i, hi'⟩).fields[k]
    exact hf
  · exact R.sourceSignature_constructorArity

/-- Source extraction is total even for an empty intermediate table; the
public installation boundary separately enforces declaration nonemptiness. -/
theorem sourceSignature_models
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) : R.sourceSignature.Models sourceEnv decl := by
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
      ⟨R.headerVEnv, R.core.typesAdded, ?_⟩, ⟨R.headerVEnv, R.core.typesAdded, ?_⟩,
      .inr ⟨R.headerVEnv, R.core.typesAdded, ?_⟩, .inr ?_, ?_⟩
    all_goals simp [declaration, hfamilies, hctors, VInductDecl.constructorConstants, hempty]
  · exact R.sourceSignature_models_of_nonempty hempty

end CompletedConstructorPhases
end Lean4Lean.VerifyInductive
