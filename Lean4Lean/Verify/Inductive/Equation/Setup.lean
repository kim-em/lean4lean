import Lean4Lean.Verify.Inductive.Nested.Compilation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Complete output of the executable recursor suffix, retaining the local
binder selections required for compilation and the final mutual-lookup
invariant required by subsequent nested restoration. -/
structure RecursorPhasesResult
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    (R : ConstructorPhasesResult Hheaders ctorEnv)
    (outEnv : Environment) where
  elimLevel : Level
  elimLevelAdmissible : AddInductive.AdmissibleElimLevel c.lparams elimLevel
  lparamsNodup : c.lparams.Nodup
  recInfos : Array AddInductive.RecInfo
  localContext : AddInductive.Context
  localWF : BindingContextWF localContext
  localExtends : BindingContextLE { c with env := ctorEnv } localContext
  recursorDepth : Nat
  recursorWF : RecursorContextWF localContext
    (AddInductive.getRecLevelParams elimLevel c.lparams)
  recursorEnv : recursorWF.venv = R.declared.context.venv
  parameterSuffix : RecursorParameterContextSuffix recursorWF stats
    recursorDepth
  parameterDecls : parameterSuffix.parameterDecls =
    (R.materialized.parameterSuffix.toRecursorContext
      elimLevelAdmissible).parameterDecls
  validStats : RecursorValidAppStatsWF recursorWF.venv
    (AddInductive.getRecLevelParams elimLevel c.lparams)
    recursorWF.mlctx.vlctx stats decl recursorDepth
  noIndConsts : VLCtx.NoIndConsts (decl.types.map (·.name))
    recursorWF.mlctx.vlctx
  fieldReplay : RecursorFieldDecisionReplayCompat
  loopUArgsReplay : RecursorLoopUArgsReplayCompat
  bindings : RecInfoBindings localContext recInfos
  origins : RecInfoTypeOrigins localContext recInfos
  minorSources : RecInfoMinorSourceAlignment stats indTypes origins
  minorSemantics : RecInfoMinorSemanticAlignment recursorWF origins
    parameterSuffix.parameterDecls
  majorTypes : RecursorTranslatedOriginTypes recursorWF origins.majorTypes
  majorShapes : RecInfoMajorTypeShapes stats recInfos origins.majorTypes
  motiveTypes : RecursorTranslatedOriginTypes recursorWF origins.motiveTypes
  motiveShapes : RecInfoMotiveTypeShapes localContext recInfos
    origins.motiveTypes elimLevel
  motiveTelescopes : RecInfoMotiveTelescopes recursorWF stats decl
    (R.materialized.parameterSuffix.toRecursorContext
      elimLevelAdmissible).parameterDecls.toCtx recInfos elimLevel
  indexRows : RecursorTranslatedOriginTypeRows recursorWF origins.indexTypes
  params : BoundFVarArray localContext stats.params
  noAlias : bindings.NoAlias params
  outerOrder : RecInfoOuterOrder recursorWF params bindings
  arities : RecInfoArities stats recInfos
  minorCounts : ∀ i, i < recInfos.size →
    recInfos[i]!.minors.size = indTypes[i]!.ctors.length
  cardinality : RecursorCardinalityCertificate stats recInfos decl
  outVEnv : VEnv
  entries : List (ConstantInfo × VConstVal)
  generated : GeneratedRecursors localContext.safety R.declared.venvCtors
    localContext.lparams elimLevel localContext stats indTypes recInfos entries
  ruleSemantics : GeneratedRecursorRuleSemanticsRange
    recursorWF decl stats indTypes recInfos elimLevel 0 entries
  installed : AddConstants localContext.safety localContext.env
    R.declared.venvCtors
    entries outEnv outVEnv
  closed : MutualInductivesClosed outEnv

/-- The exact `getElimLevel`/`mkRecInfos`/`declareRecursors` suffix of
`AddInductive.run`.  The executable `checkRecursorTypes` pass now supplies
translation of every freshly built telescope, while this theorem discharges
context conservation, installation, cardinality, and mutual lookup. -/
theorem ConstructorPhasesResult.recursorPhasesWF
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    (R : ConstructorPhasesResult Hheaders ctorEnv)
    (hclosed : MutualInductivesClosed ctorEnv)
    (hlparams : c.lparams.Nodup)
    (hwhnf : WhnfLParamsCompat)
    (hfieldReplay : RecursorFieldDecisionReplayCompat)
    (hloopUArgsReplay : RecursorLoopUArgsReplayCompat)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hnotPartial : c.safety ≠ .partial)
    (hnprim : c.allowPrimitive = true →
      ∀ owner (howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName indTypes[owner]!.name)) :
    ((AddInductive.getElimLevel stats indTypes >>= fun elimLevel =>
      AddInductive.isKTarget stats indTypes >>= fun kTarget =>
      AddInductive.mkRecInfos stats indTypes elimLevel fun recInfos =>
        AddInductive.declareRecursors stats indTypes elimLevel recInfos
          kTarget)
      { c with env := ctorEnv }).WF fun outEnv =>
        Nonempty (RecursorPhasesResult R outEnv) := by
  apply R.getElimLevelMkRecInfosWF hlparams hwhnf hconsume hlit hproj
    (Q := fun outEnv => Nonempty (RecursorPhasesResult R outEnv))
    (k := fun elimLevel kTarget recInfos =>
      AddInductive.declareRecursors stats indTypes elimLevel recInfos kTarget)
  intro elimLevel hElim kTarget localContext localDepth recInfos Rlocal henvLocal
    HsuffixLocal hparameterDeclsLocal HstatsLocal hctxLocal Hbindings
    Horigins HminorSources HminorSemantics HmajorTypes HmajorShapes
    HmotiveTypes HmotiveShapes
    Htelescopes HindexRows Hparams hnoalias houterOrder Harities HminorCounts
    Hcard Hle
  have Hvalid : CheckingEnv.Valid localContext.safety localContext.env
      R.declared.venvCtors := by
    rw [Hle.safety_eq, Hle.env_eq]
    rw [← R.declared.contextVEnv]
    exact R.declared.context.checking
  have Hcore : TrInductDeclCore sourceEnv localContext.lparams nparams
      indTypes.toList isUnsafe decl Hheaders.context.venv
      R.declared.venvCtors := by
    rw [Hle.lparams_eq]
    exact R.core
  have Hseed : ∀ owner (howner : owner < indTypes.size),
      ∀ ctor, ctor ∈ indTypes[owner]!.ctors →
        ∃ tail tailTarget introTarget,
          RecursorParamPrefix stats 0 ctor.type tail ∧
          Nonempty
            (CheckedConstructorOwnerNormalForm stats owner tail) ∧
          tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
          TrExprS Rlocal.venv
            (AddInductive.getRecLevelParams elimLevel c.lparams)
            Rlocal.mlctx.vlctx tail tailTarget ∧
          Rlocal.venv.IsType
            (AddInductive.getRecLevelParams elimLevel c.lparams).length
            Rlocal.mlctx.vlctx.toCtx tailTarget ∧
          TrExprS Rlocal.venv
            (AddInductive.getRecLevelParams elimLevel c.lparams)
            Rlocal.mlctx.vlctx
            (mkAppN (.const ctor.name stats.levels) stats.params)
            introTarget ∧
          Rlocal.venv.HasType
            (AddInductive.getRecLevelParams elimLevel c.lparams).length
            Rlocal.mlctx.vlctx.toCtx introTarget tailTarget := by
    intro owner howner ctor hctor
    have hownerBang : indTypes[owner]! = indTypes[owner] := by
      simp [Array.getElem!_eq_getD, Array.getD, howner]
    rw [hownerBang] at hctor
    rcases List.mem_iff_getElem.mp hctor with ⟨ctorIdx, hctorIdx, rfl⟩
    rcases R.checkedConstructorRuntimeSeedAt elimLevel hElim hlparams Rlocal
        henvLocal HsuffixLocal hparameterDeclsLocal owner howner ctorIdx
        hctorIdx with
      ⟨tail, tailTarget, introTarget, Hprefix, Hnormal, HtailFVars, Htail,
        HtailType, Hintro, HintroType⟩
    exact ⟨tail, tailTarget, introTarget, Hprefix, Hnormal, HtailFVars,
      Htail, HtailType, Hintro, HintroType⟩
  have Hrecursors := AddInductive.declareRecursors.bindingSemanticWF
    (elimLevel := elimLevel) kTarget Hvalid Rlocal.toBindingContextWF Rlocal
    HstatsLocal hwhnf hconsume hlit hctxLocal hproj Hcard Hcore Hbindings
    Hparams hnoalias HsuffixLocal.parameterFVarsUp Hseed (by
      rw [Hle.safety_eq]
      exact hnotPartial) (by
        intro hallow
        exact hnprim (Hle.allowPrimitive_eq ▸ hallow))
  have hclosedLocal : MutualInductivesClosed localContext.env := by
    rw [Hle.env_eq]
    exact hclosed
  exact Hrecursors.mono fun outEnv Hout => by
    rcases Hout with
      ⟨outVEnv, entries, ⟨Hgenerated⟩, ⟨HruleSemantics⟩, Hinstalled⟩
    exact ⟨{
      elimLevel := elimLevel
      elimLevelAdmissible := hElim
      lparamsNodup := hlparams
      recInfos := recInfos
      localContext := localContext
      localWF := Rlocal.toBindingContextWF
      localExtends := Hle
      recursorDepth := localDepth
      recursorWF := Rlocal
      recursorEnv := henvLocal
      parameterSuffix := HsuffixLocal
      parameterDecls := hparameterDeclsLocal
      validStats := HstatsLocal
      noIndConsts := hctxLocal
      fieldReplay := hfieldReplay
      loopUArgsReplay := hloopUArgsReplay
      bindings := Hbindings
      origins := Horigins
      minorSources := HminorSources
      minorSemantics := HminorSemantics
      majorTypes := HmajorTypes
      majorShapes := HmajorShapes
      motiveTypes := HmotiveTypes
      motiveShapes := HmotiveShapes
      motiveTelescopes := Htelescopes
      indexRows := HindexRows
      params := Hparams
      noAlias := hnoalias
      outerOrder := houterOrder
      arities := Harities
      minorCounts := HminorCounts
      cardinality := Hcard
      outVEnv := outVEnv
      entries := entries
      generated := Hgenerated
      ruleSemantics := HruleSemantics
      installed := Hinstalled
      closed := Hgenerated.closesMutuals Hinstalled Hvalid.tr.map_wf
        hclosedLocal }⟩

/-- The prefix length of the concrete minor rows is the constructor-prefix
offset used by rule generation.  Retaining this equality avoids treating the
flattened `RecInfo` array and the mutual constructor traversal as an informal
shared convention. -/
theorem RecursorPhasesResult.minorPrefixLength_eq
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv) (owner : Nat)
    (howner : owner ≤ H.recInfos.size) :
    ((H.recInfos.toList.take owner).flatMap
      (fun info => info.minors.toList)).length =
      recursorMinorOffset indTypes owner := by
  have hsizes : H.recInfos.size = indTypes.size := by
    calc
      H.recInfos.size = decl.types.length := H.cardinality.records
      _ = indTypes.toList.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core).symm
      _ = indTypes.size := by simp
  induction owner with
  | zero => simp [recursorMinorOffset]
  | succ owner ih =>
      have hrec : owner < H.recInfos.size := by omega
      have hind : owner < indTypes.size := by omega
      rw [recursorMinorOffset_step indTypes owner hind]
      simp [List.take_add_one, hrec, ih (by omega)]
      simpa [getElem!_pos H.recInfos owner hrec,
        getElem!_pos indTypes owner hind] using H.minorCounts owner hrec

def RecursorPhasesResult.staged
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv) :
    StagedBlock c.safety c.env sourceEnv Hheaders.entries R.declared.entries
      H.entries outEnv H.outVEnv where
  envTypes := headerEnv
  venvTypes := Hheaders.context.venv
  envCtors := ctorEnv
  venvCtors := R.declared.venvCtors
  typesAdded := Hheaders.installed
  ctorsAdded := R.declared.installed
  recursorsAdded := by
    simpa [H.localExtends.safety_eq, H.localExtends.env_eq] using H.installed

theorem RecursorPhasesResult.outVEnvWF
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv) : H.outVEnv.WF := by
  have hvalid : CheckingEnv.Valid H.localContext.safety
      H.localContext.env R.declared.venvCtors := by
    rw [← R.declared.contextVEnv, ← H.recursorEnv]
    exact H.recursorWF.checking
  exact (H.installed.valid hvalid).tr.wf

/-- The executable recursor phase supplies the binder-explicit translation
certificate for every owner in the mutual block.  Binder selections and
their no-alias proof are recovered from the retained `mkRecInfos` state. -/
theorem RecursorPhasesResult.generatedTelescopeTranslations
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv) :
    GeneratedRecursorTelescopeTranslations R.declared.venvCtors stats
      H.recInfos H.entries := by
  intro ownerIdx hentry
  have hrecInfo : ownerIdx < H.recInfos.size := by
    rw [← H.generated.length]
    exact hentry
  let E := H.generated.entry ownerIdx hentry
  let selections := H.bindings.toRecursorLocalSelections H.localWF H.params
    ownerIdx hrecInfo
  have hnoalias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias ownerIdx hrecInfo
  refine ⟨E.info, E.source_eq, ?_⟩
  exact E.telescopeTranslation selections hrecInfo hnoalias

/-- The concrete parameter/motive/minor binder domains are identical for
any two recursors generated from the same mutual block.  This is a
source-syntax fact about the three shared `mkForall` selections; neither
owner's index/major suffix participates. -/
theorem RecursorPhasesResult.generatedRecursorCommonPrefixBinderDomainAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (owner₁ : Nat) (howner₁ : owner₁ < H.entries.length)
    (owner₂ : Nat) (howner₂ : owner₂ < H.entries.length)
    (i : Nat)
    (hi : i < stats.params.size +
      (H.recInfos.map (·.motive)).size +
      (H.recInfos.flatMap (·.minors)).size)
    {domain₁ domain₂ : Expr}
    (Hbinder₁ : Expr.ForallBinderAt
      (H.generated.entry owner₁ howner₁).info.type i domain₁)
    (Hbinder₂ : Expr.ForallBinderAt
      (H.generated.entry owner₂ howner₂).info.type i domain₂) :
    domain₁ = domain₂ := by
  have hrecInfo₁ : owner₁ < H.recInfos.size := by
    simpa [H.generated.length] using howner₁
  have hrecInfo₂ : owner₂ < H.recInfos.size := by
    simpa [H.generated.length] using howner₂
  let E₁ := H.generated.entry owner₁ howner₁
  let E₂ := H.generated.entry owner₂ howner₂
  let S₁ := H.bindings.toRecursorLocalSelections H.localWF H.params
    owner₁ hrecInfo₁
  let S₂ := H.bindings.toRecursorLocalSelections H.localWF H.params
    owner₂ hrecInfo₂
  have hnoalias₁ : S₁.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias
      owner₁ hrecInfo₁
  have hnoalias₂ : S₂.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias
      owner₂ hrecInfo₂
  by_cases hparam : i < stats.params.size
  · rcases H.params.declarationAt H.localWF i hparam with ⟨D⟩
    have Hcanonical₁ := S₁.parameterBinderAt hnoalias₁ D
    have Hcanonical₂ := S₂.parameterBinderAt hnoalias₂ D
    dsimp only at Hcanonical₁ Hcanonical₂
    rw [← E₁.type] at Hcanonical₁
    rw [← E₂.type] at Hcanonical₂
    exact (Hbinder₁.unique Hcanonical₁).trans
      (Hbinder₂.unique Hcanonical₂).symm
  · let motiveIdx := i - stats.params.size
    by_cases hmotive : motiveIdx < (H.recInfos.map (·.motive)).size
    · rcases H.bindings.motives.declarationAt H.localWF motiveIdx hmotive with
        ⟨D⟩
      have Hcanonical₁ := S₁.motiveBinderAt hnoalias₁ D
      have Hcanonical₂ := S₂.motiveBinderAt hnoalias₂ D
      dsimp only at Hcanonical₁ Hcanonical₂
      have hiEq : stats.params.size + motiveIdx = i := by
        dsimp [motiveIdx]
        omega
      rw [hiEq, ← E₁.type] at Hcanonical₁
      rw [hiEq, ← E₂.type] at Hcanonical₂
      exact (Hbinder₁.unique Hcanonical₁).trans
        (Hbinder₂.unique Hcanonical₂).symm
    · let minorIdx := i - stats.params.size -
        (H.recInfos.map (·.motive)).size
      have hminor : minorIdx <
          (H.recInfos.flatMap (·.minors)).size := by
        dsimp [motiveIdx, minorIdx] at hmotive ⊢
        omega
      rcases H.bindings.flatMinors.declarationAt H.localWF minorIdx hminor with
        ⟨D⟩
      have Hcanonical₁ := S₁.minorBinderAt hnoalias₁ D
      have Hcanonical₂ := S₂.minorBinderAt hnoalias₂ D
      dsimp only at Hcanonical₁ Hcanonical₂
      have hiEq : stats.params.size +
          (H.recInfos.map (·.motive)).size + minorIdx = i := by
        dsimp [minorIdx]
        omega
      rw [hiEq, ← E₁.type] at Hcanonical₁
      rw [hiEq, ← E₂.type] at Hcanonical₂
      exact (Hbinder₁.unique Hcanonical₁).trans
        (Hbinder₂.unique Hcanonical₂).symm

/-- Header metadata installed at the start of the verified pipeline remains
retrievable, unchanged, after constructors and recursors are installed. -/
theorem RecursorPhasesResult.findHeaderOfMem
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (Hc : ContextWF c)
    (H : RecursorPhasesResult R outEnv)
    (hentry : (info, value) ∈ Hheaders.entries) :
    outEnv.find? info.name = some info := by
  have hheader := Hheaders.installed.findOfMem Hc.checking.tr.map_wf hentry
  have hctor := R.declared.installed.preservesFind
    Hheaders.context.checking.tr.map_wf hheader
  have hlocalWF : H.localContext.env.constants.WF := by
    rw [H.localExtends.env_eq]
    exact R.declared.context.checking.tr.map_wf
  apply H.installed.preservesFind hlocalWF
  rwa [H.localExtends.env_eq]

/-- Exact source-family metadata is present after the complete lowered
installation, including the constructor-name list used by restoration. -/
theorem RecursorPhasesResult.findSourceHeader
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (Hc : ContextWF c) (H : RecursorPhasesResult R outEnv)
    (howner : owner ∈ indTypes.toList) :
    ∃ info : InductiveVal,
      outEnv.find? owner.name = some (.inductInfo info) ∧
      info.ctors = owner.ctors.map (fun ctor => ctor.name) ∧
      info.all = indTypes.toList.map (fun type => type.name) := by
  rcases Hheaders.sourceAligned with ⟨numNested, Haligned⟩
  have htypesLength : indTypes.size = decl.types.length := by
    simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
      Hheaders.translation.types
  have hsize : stats.nindices.size = indTypes.size := by
    rw [Array.size_eq_length_toList, Hheaders.materialized.indices,
      List.length_map]
    exact htypesLength.symm
  rcases inductiveTypeInfos_source_mem stats nparams indTypes numNested
      isUnsafe c.lparams hsize howner with
    ⟨info, hinfo, hname, hctors, hall⟩
  rcases Haligned.findInfo hinfo with ⟨value, hentry⟩
  refine ⟨info, ?_, hctors, hall⟩
  rw [← hname]
  exact H.findHeaderOfMem Hc hentry

private theorem mkAuxRecNameMap_fold_recNames
    (names : List Name) (acc : Array Name × NameMap Name × Nat)
    (mainName : Name) :
    (names.foldl (fun b name =>
      (b.1.push (Lean.mkRecName name),
        b.2.1.insert (Lean.mkRecName name)
          ((Lean.mkRecName mainName).appendIndexAfter b.2.2),
        b.2.2 + 1)) acc).1.toList =
      acc.1.toList ++ names.map Lean.mkRecName := by
  induction names generalizing acc with
  | nil => simp
  | cons name names ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp

private theorem mkAuxRecNameMap_fold_find_none
    (names : List Name) (acc : Array Name × NameMap Name × Nat)
    (mainName query : Name)
    (hacc : acc.2.1.find? query = none)
    (hnot : query ∉ names.map Lean.mkRecName) :
    (names.foldl (fun b name =>
      (b.1.push (Lean.mkRecName name),
        b.2.1.insert (Lean.mkRecName name)
          ((Lean.mkRecName mainName).appendIndexAfter b.2.2),
        b.2.2 + 1)) acc).2.1.find? query = none := by
  induction names generalizing acc with
  | nil => simpa using hacc
  | cons name names ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    apply ih _ _ hnot.2
    change (show Std.TreeMap Name Name Name.quickCmp from acc.2.1)[query]? =
      none at hacc
    change (Std.TreeMap.insert
      (show Std.TreeMap Name Name Name.quickCmp from acc.2.1)
      (Lean.mkRecName name)
      ((Lean.mkRecName mainName).appendIndexAfter acc.2.2))[query]? = none
    rw [Std.TreeMap.getElem?_insert]
    split
    · rename_i heq
      have : Lean.mkRecName name = query := by simpa using heq
      exact False.elim (hnot.1 this.symm)
    · exact hacc

/-- The first component of the production auxiliary-recursor map is exactly
the recursor-name image of the extra family names recorded in the installed
main-family metadata. -/
theorem mkAuxRecNameMap_recNames
    (main : InductiveType) (rest : List InductiveType)
    (env : Environment) (info : InductiveVal)
    (hfind : env.find? main.name = some (.inductInfo info))
    (hlength : (main :: rest).length < info.all.length) :
    (Lean4Lean.mkAuxRecNameMap env (main :: rest)).1 =
      (info.all.drop (main :: rest).length).map Lean.mkRecName := by
  have hlength' : rest.length + 1 < info.all.length := by
    simpa using hlength
  simp [Lean4Lean.mkAuxRecNameMap, hfind, hlength',
    mkAuxRecNameMap_fold_recNames]

theorem mkAuxRecNameMap_recNames_mem
    (main : InductiveType) (rest : List InductiveType)
    (env : Environment) (info : InductiveVal)
    (hfind : env.find? main.name = some (.inductInfo info))
    (hmem : recName ∈
      (Lean4Lean.mkAuxRecNameMap env (main :: rest)).1) :
    ∃ name ∈ info.all, recName = Lean.mkRecName name := by
  by_cases hlength : (main :: rest).length < info.all.length
  · rw [mkAuxRecNameMap_recNames main rest env info hfind hlength] at hmem
    rcases List.mem_map.mp hmem with ⟨name, hname, rfl⟩
    exact ⟨name, List.mem_of_mem_drop hname, rfl⟩
  · have hlength' : ¬ rest.length + 1 < info.all.length := by
      simpa using hlength
    simp [Lean4Lean.mkAuxRecNameMap, hfind, hlength'] at hmem
    change recName ∈ ([] : List Name) at hmem
    simp at hmem

/-- The second component of the production auxiliary-recursor map has no
entry outside the exact recursor-name suffix used to build it. -/
theorem mkAuxRecNameMap_recMap_find_none
    (main : InductiveType) (rest : List InductiveType)
    (env : Environment) (info : InductiveVal)
    (hfind : env.find? main.name = some (.inductInfo info))
    (hnot : query ∉
      (info.all.drop (main :: rest).length).map Lean.mkRecName) :
    (Lean4Lean.mkAuxRecNameMap env (main :: rest)).2.find? query = none := by
  by_cases hlength : (main :: rest).length < info.all.length
  · have hlength' : rest.length + 1 < info.all.length := by
      simpa using hlength
    simpa [Lean4Lean.mkAuxRecNameMap, hfind, hlength'] using
      mkAuxRecNameMap_fold_find_none
        (info.all.drop (rest.length + 1)) (#[], {}, 1) main.name query
        (by rfl) (by simpa using hnot)
  · have hlength' : ¬ rest.length + 1 < info.all.length := by
      simpa using hlength
    simp [Lean4Lean.mkAuxRecNameMap, hfind, hlength']
    change ({} : NameMap Name).find? query = none
    rfl

theorem mkRecName_injective : Function.Injective Lean.mkRecName := by
  intro left right heq
  simpa [Lean.mkRecName, Lean.Name.getPrefix] using
    congrArg Lean.Name.getPrefix heq

/-- A recursor shape's existential owner position is the concrete generated
position whenever the declaration's source names are duplicate-free.  This
is the positional bridge needed before transporting a lowered shape back to
the corresponding source-family index. -/
theorem VInductDecl.NestedRecursorShape.ownerIdx_eq_of_name
    {decl : VInductDecl} {owner : VInductiveType} {recursor : VConstVal}
    (H : decl.NestedRecursorShape owner recursor)
    (ownerIdx : Nat) (howner : ownerIdx < decl.types.length)
    (hname : recursor.name = decl.recursorName decl.types[ownerIdx])
    (hnodup : decl.sourceNames.Nodup) :
    H.ownerIdx = ownerIdx := by
  have htypeNames : (decl.types.map (fun type => type.name)).Nodup := by
    have hprefix := (List.nodup_append.mp hnodup).1
    simpa [VInductDecl.sourceNames, VInductDecl.typeConstants,
      VInductiveType.toVConstVal, Function.comp_def] using hprefix
  have hshapeMap : H.ownerIdx <
      (decl.types.map (fun type => type.name)).length := by
    simpa using H.owner_lt
  have hownerMap : ownerIdx <
      (decl.types.map (fun type => type.name)).length := by
    simpa using howner
  apply (List.getElem_inj (h₀ := hshapeMap) (h₁ := hownerMap)
    htypeNames).mp
  rw [List.getElem_map, List.getElem_map, H.owner_eq]
  exact mkRecName_injective (H.name.symm.trans hname)

/-- Constructor metadata installed in the middle phase remains retrievable,
unchanged, after recursor installation. -/
theorem RecursorPhasesResult.findConstructorOfMem
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (hentry : (info, value) ∈ R.declared.entries) :
    outEnv.find? info.name = some info := by
  have hctor := R.declared.installed.findOfMem
    Hheaders.context.checking.tr.map_wf hentry
  have hlocalWF : H.localContext.env.constants.WF := by
    rw [H.localExtends.env_eq]
    exact R.declared.context.checking.tr.map_wf
  apply H.installed.preservesFind hlocalWF
  rwa [H.localExtends.env_eq]

/-- Source alignment identifies the exact concrete constructor metadata that
nested restoration will read from the final lowered environment. -/
theorem RecursorPhasesResult.findSourceConstructor
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (howner : owner ∈ indTypes.toList) (hctor : ctor ∈ owner.ctors) :
    ∃ info : ConstructorVal,
      outEnv.find? ctor.name = some (.ctorInfo info) ∧
      info.type = ctor.type := by
  rcases R.declared.sourceAligned.findSource howner hctor with
    ⟨info, value, hentry, hname, htype, _hlevels, _hunsafe⟩
  refine ⟨info, ?_, htype⟩
  rw [← hname]
  exact H.findConstructorOfMem hentry

/-- The concrete constructor read by an operational restoration step is the
positionally aligned lowered constructor installed by the verified producer.
Only equality of the fold item name is required; lookup functionality then
forces equality of the complete `ConstructorVal`, and hence of its type. -/
theorem RestoredConstructorStep.oldType_eq_ofInstalled
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (Hstep : RestoredConstructorStep result outEnv ctorName
      sourceProdEnv targetProdEnv)
    (H : RecursorPhasesResult R outEnv)
    (howner : owner ∈ indTypes.toList) (hctor : ctor ∈ owner.ctors)
    (hname : ctorName = ctor.name) :
    Hstep.oldInfo.type = ctor.type := by
  rcases H.findSourceConstructor howner hctor with
    ⟨info, hlookup, htype⟩
  have hstepLookup :
      outEnv.find? ctor.name = some (.ctorInfo Hstep.oldInfo) := by
    simpa [hname] using Hstep.lookup
  have hinfo : Hstep.oldInfo = info := by
    have heq : ConstantInfo.ctorInfo Hstep.oldInfo = .ctorInfo info :=
      Option.some.inj (hstepLookup.symm.trans hlookup)
    exact ConstantInfo.ctorInfo.inj heq
  rw [hinfo]
  exact htype

/-- Safety, universe parameters, and name of the constructor read by
restoration are all fixed by the verified lowered installation. -/
theorem RestoredConstructorStep.metadataOfInstalled
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (Hstep : RestoredConstructorStep result outEnv ctorName
      sourceProdEnv targetProdEnv)
    (H : RecursorPhasesResult R outEnv)
    (howner : owner ∈ indTypes.toList) (hctor : ctor ∈ owner.ctors)
    (hname : ctorName = ctor.name) :
    c.safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety ∧
      Hstep.oldInfo.levelParams = c.lparams ∧
      Hstep.oldInfo.name = ctor.name := by
  rcases R.declared.sourceAligned.findSource howner hctor with
    ⟨info, value, hentry, hinfoName, _hinfoType, hlevels, _hunsafe⟩
  have hlookup := H.findConstructorOfMem hentry
  have hstepLookup :
      outEnv.find? ctor.name = some (.ctorInfo Hstep.oldInfo) := by
    simpa [hname] using Hstep.lookup
  have hinfo : Hstep.oldInfo = info := by
    have hlookup' : outEnv.find? info.name = some (.ctorInfo info) := by
      simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using hlookup
    rw [hinfoName] at hlookup'
    have heq : ConstantInfo.ctorInfo Hstep.oldInfo = .ctorInfo info :=
      Option.some.inj (hstepLookup.symm.trans hlookup')
    exact ConstantInfo.ctorInfo.inj heq
  subst info
  exact ⟨R.declared.installed.entrySafety hentry, hlevels, hinfoName⟩

/-- The constructor fold nested inside an operational family restoration is
indexed by exactly the constructor-name list of the aligned installed lowered
family.  This is the family-level lookup bridge used before applying
`oldType_eq_ofInstalled` pointwise. -/
theorem RestoredInductiveStep.oldConstructors_eq_ofInstalled
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (Hstep : RestoredInductiveStep result outEnv auxRec allIndNames indType
      sourceProdEnv targetProdEnv)
    (Hc : ContextWF c) (H : RecursorPhasesResult R outEnv)
    (howner : owner ∈ indTypes.toList)
    (hname : indType.name = owner.name) :
    Hstep.oldInfo.ctors = owner.ctors.map (fun ctor => ctor.name) := by
  rcases H.findSourceHeader Hc howner with
    ⟨info, hlookup, hctors, _hall⟩
  have hstepLookup :
      outEnv.find? owner.name = some (.inductInfo Hstep.oldInfo) := by
    simpa [hname] using Hstep.lookup
  have hinfo : Hstep.oldInfo = info := by
    have heq : ConstantInfo.inductInfo Hstep.oldInfo = .inductInfo info :=
      Option.some.inj (hstepLookup.symm.trans hlookup)
    exact ConstantInfo.inductInfo.inj heq
  rw [hinfo]
  exact hctors

/-- Every generated primary recursor is retrievable with the exact production
metadata retained by the verified recursor phase. -/
theorem RecursorPhasesResult.findRecursorOfMem
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (hentry : (info, value) ∈ H.entries) :
    outEnv.find? info.name = some info := by
  have hlocalWF : H.localContext.env.constants.WF := by
    rw [H.localExtends.env_eq]
    exact R.declared.context.checking.tr.map_wf
  exact H.installed.findOfMem hlocalWF hentry

/-- The generated primary recursor for every lowered family is present in the
final environment and satisfies both telescope preconditions consumed by
nested restoration. -/
theorem RecursorPhasesResult.findSourceRecursor
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (ownerIdx : Nat) (howner : ownerIdx < indTypes.size) :
    ∃ info : RecursorVal,
      outEnv.find? (Lean.mkRecName indTypes[ownerIdx]!.name) =
        some (.recInfo info) ∧
      RestoreTelescope info.type nparams ∧
      ∀ rule ∈ info.rules, RestoreTelescope rule.rhs nparams := by
  have htypes : indTypes.size = decl.types.length := by
    simpa using Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
  have hrecInfo : ownerIdx < H.recInfos.size := by
    rw [H.cardinality.records, ← htypes]
    exact howner
  have hentry : ownerIdx < H.entries.length := by
    rw [H.generated.length]
    exact hrecInfo
  let E := H.generated.entry ownerIdx hentry
  let selections := H.bindings.toRecursorLocalSelections H.localWF H.params
    ownerIdx hrecInfo
  have hparams : nparams = stats.params.size :=
    R.core.nparams.symm.trans H.cardinality.params.symm
  have hlookup := H.findRecursorOfMem (List.getElem_mem hentry)
  refine ⟨E.info, ?_, E.typeRestoreTelescope selections.params hparams,
    E.rulesRestoreTelescope hparams⟩
  change outEnv.find? H.entries[ownerIdx].1.name =
    some H.entries[ownerIdx].1 at hlookup
  rw [E.source_eq] at hlookup
  change outEnv.find? E.info.name = some (.recInfo E.info) at hlookup
  rwa [E.name] at hlookup

/-- Assemble the complete per-family lookup/telescope premise consumed by
the operational nested-restoration fold. Constructor telescope syntax is the
only remaining source-side premise; header, constructor, and recursor lookups
and both generated recursor telescopes are derived from installation. -/
theorem RecursorPhasesResult.restorationSources
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (Hc : ContextWF c) (H : RecursorPhasesResult R outEnv)
    (HctorTelescope : ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors,
      RestoreTelescope ctor.type nparams) :
    ∀ owner, owner ∈ indTypes.toList →
      ∃ oldInfo : InductiveVal,
        outEnv.find? owner.name = some (.inductInfo oldInfo) ∧
        (∀ ctorName, ctorName ∈ oldInfo.ctors →
          ∃ ctorInfo : ConstructorVal,
            outEnv.find? ctorName = some (.ctorInfo ctorInfo) ∧
            RestoreTelescope ctorInfo.type nparams) ∧
        ∃ recInfo : RecursorVal,
          outEnv.find? (Lean.mkRecName owner.name) = some (.recInfo recInfo) ∧
          RestoreTelescope recInfo.type nparams ∧
          ∀ rule ∈ recInfo.rules,
            RestoreTelescope rule.rhs nparams := by
  intro owner howner
  rcases H.findSourceHeader Hc howner with
    ⟨oldInfo, hheader, hctors, _hall⟩
  rcases List.mem_iff_getElem.mp howner with ⟨ownerIdx, hownerIdx, rfl⟩
  rcases H.findSourceRecursor ownerIdx (by simpa using hownerIdx) with
    ⟨recInfo, hrecursor, hrecType, hrecRules⟩
  refine ⟨oldInfo, hheader, ?_, recInfo, ?_, hrecType, hrecRules⟩
  · intro ctorName hctorName
    rw [hctors] at hctorName
    rcases List.mem_map.mp hctorName with ⟨ctor, hctor, rfl⟩
    rcases H.findSourceConstructor (List.getElem_mem hownerIdx) hctor with
      ⟨ctorInfo, hlookup, htype⟩
    refine ⟨ctorInfo, hlookup, ?_⟩
    rw [htype]
    exact HctorTelescope _ (List.getElem_mem hownerIdx) ctor hctor
  · have hbang : indTypes[ownerIdx]! = indTypes[ownerIdx] := by
      have hownerArray : ownerIdx < indTypes.size := by simpa using hownerIdx
      simp [Array.getElem!_eq_getD, Array.getD, hownerArray]
    rw [hbang] at hrecursor
    exact hrecursor

/-- The installed generated entry fixes the universe arity of the old
recursor metadata read by primary restoration. -/
theorem RecursorPhasesResult.restoredPrimaryRecursorMetadata
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (ownerIdx : Nat) (hentry : ownerIdx < H.entries.length)
    (Hstep : RestoredRecursorStep result outEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (holdRecName : oldRecName = Lean.mkRecName indTypes[ownerIdx]!.name) :
    c.safety ≤ (ConstantInfo.recInfo Hstep.oldInfo).safety ∧
      Hstep.oldInfo.levelParams.length =
        (H.entries[ownerIdx]'hentry).2.uvars := by
  let E := H.generated.entry ownerIdx hentry
  have hlookup := H.findRecursorOfMem (List.getElem_mem hentry)
  have hlookupE : outEnv.find? (Lean.mkRecName indTypes[ownerIdx]!.name) =
      some (.recInfo E.info) := by
    change outEnv.find? H.entries[ownerIdx].1.name =
      some H.entries[ownerIdx].1 at hlookup
    rw [E.source_eq] at hlookup
    change outEnv.find? E.info.name = some (.recInfo E.info) at hlookup
    rwa [E.name] at hlookup
  have holdInfo : Hstep.oldInfo = E.info := by
    have hstepLookup : outEnv.find?
        (Lean.mkRecName indTypes[ownerIdx]!.name) =
          some (.recInfo Hstep.oldInfo) := by
      simpa [holdRecName] using Hstep.lookup
    exact ConstantInfo.recInfo.inj (Option.some.inj
      (hstepLookup.symm.trans hlookupE))
  constructor
  · rw [← H.localExtends.safety_eq, holdInfo]
    exact E.translated.1.1
  · rw [holdInfo]
    simpa [ConstantInfo.levelParams, ConstantInfo.toConstantVal] using
      E.translated.1.2.1

/-- Identify an operational primary-restoration step with its exact generated
recursor entry and expose the complete old/restored telescope alignment.  In
particular, callers do not choose an unrelated generated entry or reconstruct
the local binder selection: installation, the restoration lookup, and the
retained `mkRecInfos` state determine all of them. -/
theorem RecursorPhasesResult.restoredPrimaryTelescopeAlignment
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (ownerIdx : Nat) (hentry : ownerIdx < H.entries.length)
    (Hstep : RestoredRecursorStep result outEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (holdRecName : oldRecName =
      Lean.mkRecName indTypes[ownerIdx]!.name)
    (hresultNparams : result.nparams = nparams)
    (hresultParams : result.params.size = result.nparams) :
    Nonempty (GeneratedRecursorRestorationTelescopeAlignment result outEnv
      auxRec Hstep.restored.newInfo (H.generated.entry ownerIdx hentry)) := by
  have hrecInfo : ownerIdx < H.recInfos.size := by
    simpa [H.generated.length] using hentry
  let E := H.generated.entry ownerIdx hentry
  have hlookup := H.findRecursorOfMem (List.getElem_mem hentry)
  have hlookupE : outEnv.find? (Lean.mkRecName indTypes[ownerIdx]!.name) =
      some (.recInfo E.info) := by
    change outEnv.find? H.entries[ownerIdx].1.name =
      some H.entries[ownerIdx].1 at hlookup
    rw [E.source_eq] at hlookup
    change outEnv.find? E.info.name = some (.recInfo E.info) at hlookup
    rwa [E.name] at hlookup
  have holdInfo : Hstep.oldInfo = E.info := by
    have hstepLookup : outEnv.find?
        (Lean.mkRecName indTypes[ownerIdx]!.name) =
          some (.recInfo Hstep.oldInfo) := by
      simpa [holdRecName] using Hstep.lookup
    exact ConstantInfo.recInfo.inj (Option.some.inj
      (hstepLookup.symm.trans hlookupE))
  let selections := H.bindings.toRecursorLocalSelections H.localWF H.params
    ownerIdx hrecInfo
  have hselectionNoAlias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias ownerIdx hrecInfo
  have hrestoration : RecursorRestoration result outEnv auxRec allIndNames
      oldRecName Hstep.restored.newRecName E.info Hstep.restored.newInfo := by
    simpa [holdInfo] using Hstep.restored.restoration
  have hparams : result.nparams = stats.params.size :=
    hresultNparams.trans <| R.core.nparams.symm.trans
      H.cardinality.params.symm
  exact hrestoration.generatedTelescopeAlignment E selections hrecInfo
    hselectionNoAlias hparams hresultParams

/-- A primary restoration step inherits one of the two source-declaration
universe arities admitted for generated recursors.  This packages the lookup
argument identifying the step's old metadata with the exact generated entry,
so later source-restoration proofs do not need to repeat it. -/
theorem RecursorPhasesResult.restoredPrimaryRecursorUvars
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (ownerIdx : Nat) (hentry : ownerIdx < H.entries.length)
    (Hstep : RestoredRecursorStep result outEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (holdRecName : oldRecName = Lean.mkRecName indTypes[ownerIdx]!.name)
    (sourceDecl : VInductDecl)
    (hsourceUvars : sourceDecl.uvars = c.lparams.length) :
    Hstep.oldInfo.levelParams.length = sourceDecl.uvars ∨
      Hstep.oldInfo.levelParams.length = sourceDecl.uvars + 1 := by
  let E := H.generated.entry ownerIdx hentry
  have hlookup := H.findRecursorOfMem (List.getElem_mem hentry)
  have hlookupE : outEnv.find? (Lean.mkRecName indTypes[ownerIdx]!.name) =
      some (.recInfo E.info) := by
    change outEnv.find? H.entries[ownerIdx].1.name =
      some H.entries[ownerIdx].1 at hlookup
    rw [E.source_eq] at hlookup
    change outEnv.find? E.info.name = some (.recInfo E.info) at hlookup
    rwa [E.name] at hlookup
  have holdInfo : Hstep.oldInfo = E.info := by
    have hstepLookup : outEnv.find?
        (Lean.mkRecName indTypes[ownerIdx]!.name) =
          some (.recInfo Hstep.oldInfo) := by
      simpa [holdRecName] using Hstep.lookup
    exact ConstantInfo.recInfo.inj (Option.some.inj
      (hstepLookup.symm.trans hlookupE))
  rw [holdInfo, E.levels, H.localExtends.lparams_eq]
  rw [hsourceUvars]
  exact AddInductive.getRecLevelParams_length

/-- The installed ordinary recursor phase already realizes the independent
source-recursion specification for the declaration it compiled.  This is the
pointwise form useful to later restoration proofs; for a genuinely nested
source declaration, that declaration is still the expanded lowered one. -/
theorem RecursorPhasesResult.sourcePrimaryRecursorSemantics
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (ownerIdx : Nat) (hentry : ownerIdx < H.entries.length) :
    Nonempty (SourcePrimaryRecursorSemantics decl
      (decl.types[ownerIdx]'(by
        have howner : ownerIdx < H.recInfos.size := by
          simpa [H.generated.length] using hentry
        simpa [H.cardinality.records] using howner))
      R.declared.venvCtors) := by
  have Hcore : TrInductDeclCore sourceEnv H.localContext.lparams nparams
      indTypes.toList isUnsafe decl Hheaders.context.venv
      R.declared.venvCtors := by
    rw [H.localExtends.lparams_eq]
    exact R.core
  exact H.generated.sourcePrimaryRecursorSemantics H.localWF H.bindings
    H.params H.noAlias H.cardinality Hcore ownerIdx hentry

/-- Turn the actual generated recursor entry selected by a primary
restoration step into specification-facing semantics.  Installation fixes
the old metadata and the independent recursor certificate fixes the abstract
shape; callers supply only translation of the restored concrete telescope
and the (separately audited) primary-name preservation fact. -/
def RecursorPhasesResult.restoredPrimaryRecursorSemantics
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (ownerIdx : Nat) (howner : ownerIdx < indTypes.size)
    (hentry : ownerIdx < H.entries.length)
    (hdecl : ownerIdx < decl.types.length)
    (Hstep : RestoredRecursorStep result outEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (holdRecName : oldRecName =
      Lean.mkRecName indTypes[ownerIdx]!.name)
    (canonicalEnv : VEnv)
    (Htype : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
      Hstep.restored.newInfo.type (H.entries[ownerIdx]'hentry).2.type)
    (hname : (H.entries[ownerIdx]'hentry).2.name =
      Hstep.restored.newRecName)
    (Hwf : (H.entries[ownerIdx]'hentry).2.toVConstant.WF canonicalEnv) :
    RestoredPrimaryRecursorSemantics decl (decl.types[ownerIdx]'hdecl) c.safety
      Hstep
      canonicalEnv := by
  have hrecInfo : ownerIdx < H.recInfos.size := by
    rw [H.cardinality.records]
    have htypes : indTypes.size = decl.types.length := by
      simpa using Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
    rwa [← htypes]
  let E := H.generated.entry ownerIdx hentry
  have hlookup := H.findRecursorOfMem (List.getElem_mem hentry)
  have hlookupE : outEnv.find? (Lean.mkRecName indTypes[ownerIdx]!.name) =
      some (.recInfo E.info) := by
    change outEnv.find? H.entries[ownerIdx].1.name =
      some H.entries[ownerIdx].1 at hlookup
    rw [E.source_eq] at hlookup
    change outEnv.find? E.info.name = some (.recInfo E.info) at hlookup
    rwa [E.name] at hlookup
  have holdInfo : Hstep.oldInfo = E.info := by
    have hstepLookup : outEnv.find?
        (Lean.mkRecName indTypes[ownerIdx]!.name) =
          some (.recInfo Hstep.oldInfo) := by
      simpa [holdRecName] using Hstep.lookup
    exact ConstantInfo.recInfo.inj (Option.some.inj
      (hstepLookup.symm.trans hlookupE))
  have Hcore : TrInductDeclCore sourceEnv H.localContext.lparams nparams
      indTypes.toList isUnsafe decl Hheaders.context.venv
        R.declared.venvCtors := by
    rw [H.localExtends.lparams_eq]
    exact R.core
  have Hcertificate := H.generated.recursorCertificate H.localWF H.bindings
    H.params H.noAlias H.cardinality Hcore
  have hrecursor : ownerIdx < (H.entries.map Prod.snd).length := by
    simpa using hentry
  have Hshape := Hcertificate.shapes ownerIdx hdecl hrecursor
  refine {
    recursor := (H.entries[ownerIdx]'hentry).2
    safety_le := ?_
    uvars := ?_
    type := Htype
    name := hname
    wf := Hwf
    shape := ?_ }
  · rw [← H.localExtends.safety_eq]
    rw [holdInfo]
    exact E.translated.1.1
  · rw [holdInfo]
    simpa [ConstantInfo.levelParams, ConstantInfo.toConstantVal] using
      E.translated.1.2.1
  · rcases Hshape with ⟨Hshape⟩
    exact ⟨by simpa only [List.getElem_map] using Hshape.toNested⟩

/-- Direct executable-to-source realization for a restored primary recursor.
Unlike `restoredPrimaryRecursorSemantics`, this theorem does not transport a
shape from the expanded abstract declaration.  It derives the source shape
from the generated concrete binder selections, operational restoration, and
translation of the restored type in the canonical source environment. -/
def RecursorPhasesResult.restoredSourcePrimaryRecursorRealization
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (ownerIdx : Nat) (hentry : ownerIdx < H.entries.length)
    (Hstep : RestoredRecursorStep result outEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (holdRecName : oldRecName =
      Lean.mkRecName indTypes[ownerIdx]!.name)
    (sourceDecl : VInductDecl)
    (hsourceOwner : ownerIdx < sourceDecl.types.length)
    (recursor : VConstVal) (canonicalEnv : VEnv)
    (hname : recursor.name = sourceDecl.recursorName
      (sourceDecl.types[ownerIdx]'hsourceOwner))
    (huvars : recursor.uvars = sourceDecl.uvars ∨
      recursor.uvars = sourceDecl.uvars + 1)
    (huvarArity : Hstep.oldInfo.levelParams.length = recursor.uvars)
    (hresultNparams : result.nparams = nparams)
    (hnparams : sourceDecl.nparams = result.nparams)
    (hmotives : sourceDecl.types.length ≤
      (H.recInfos.map (·.motive)).size)
    (hminors : sourceDecl.ownedConstructors.length ≤
      (H.recInfos.flatMap (·.minors)).size)
    (hindices : (sourceDecl.types[ownerIdx]'hsourceOwner).numIndices =
      H.recInfos[ownerIdx]!.indices.size)
    (Htype : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
      Hstep.restored.newInfo.type recursor.type) :
    SourcePrimaryRecursorRealization sourceDecl
      (sourceDecl.types[ownerIdx]'hsourceOwner) Hstep canonicalEnv recursor := by
  have hrecInfo : ownerIdx < H.recInfos.size := by
    simpa [H.generated.length] using hentry
  let E := H.generated.entry ownerIdx hentry
  have hlookup := H.findRecursorOfMem (List.getElem_mem hentry)
  have hlookupE : outEnv.find? (Lean.mkRecName indTypes[ownerIdx]!.name) =
      some (.recInfo E.info) := by
    change outEnv.find? H.entries[ownerIdx].1.name =
      some H.entries[ownerIdx].1 at hlookup
    rw [E.source_eq] at hlookup
    change outEnv.find? E.info.name = some (.recInfo E.info) at hlookup
    rwa [E.name] at hlookup
  have holdInfo : Hstep.oldInfo = E.info := by
    have hstepLookup : outEnv.find?
        (Lean.mkRecName indTypes[ownerIdx]!.name) =
          some (.recInfo Hstep.oldInfo) := by
      simpa [holdRecName] using Hstep.lookup
    exact ConstantInfo.recInfo.inj (Option.some.inj
      (hstepLookup.symm.trans hlookupE))
  let selections := H.bindings.toRecursorLocalSelections H.localWF H.params
    ownerIdx hrecInfo
  have hselectionNoAlias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias ownerIdx hrecInfo
  have hrestoration : RecursorRestoration result outEnv auxRec allIndNames
      oldRecName Hstep.restored.newRecName E.info
        Hstep.restored.newInfo := by
    simpa [holdInfo] using Hstep.restored.restoration
  have hparams : result.nparams = stats.params.size :=
    hresultNparams.trans <| R.core.nparams.symm.trans
      H.cardinality.params.symm
  have Htype' : TrExprS canonicalEnv E.info.levelParams []
      Hstep.restored.newInfo.type recursor.type := by
    simpa [holdInfo] using Htype
  have Hshape := hrestoration.nestedRecursorShape E selections hrecInfo
    hselectionNoAlias hparams sourceDecl
    (sourceDecl.types[ownerIdx]'hsourceOwner) hsourceOwner rfl recursor hname
    huvars hnparams hmotives hminors hindices Htype'
  have HisType := hrestoration.translatedTypeIsType E selections hrecInfo
    hselectionNoAlias hparams Htype'
  have huvarArity' : E.info.levelParams.length = recursor.uvars := by
    simpa [holdInfo] using huvarArity
  rw [huvarArity'] at HisType
  refine {
    source := {
      recursor := recursor
      name := hname
      isType := HisType
      shape := Hshape }
    recursor_eq := rfl
    refinement := ⟨huvarArity, Htype⟩ }

theorem DeclaredHeadersResult.typesWF
    (H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv) :
    ∀ ci ∈ H.entries.map Prod.snd, ci.toVConstant.WF sourceEnv := by
  rw [H.values]
  intro ci hci
  simp only [VInductDecl.typeConstants] at hci
  rcases List.mem_map.mp hci with ⟨target, htarget, rfl⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r H.translation.types target
      htarget with ⟨source, _, Htarget⟩
  exact Htarget.header.wf

theorem DeclaredConstructorsResult.ctorsWF
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv outEnv : Environment}
    {H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : DeclaredConstructorsResult H outEnv) :
    ∀ ci ∈ R.entries.map Prod.snd,
      ci.toVConstant.WF H.context.venv := by
  rw [R.values]
  intro ci hci
  simp only [VInductDecl.constructorConstants, List.mem_flatMap] at hci
  rcases hci with ⟨target, htarget, hci⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r R.translation.types target
      htarget with ⟨source, _, Htarget⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r Htarget ci hci with
    ⟨ctor, _, Hctor⟩
  exact Hctor.wf

def RecursorPhasesResult.blockCertificate
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv) :
    BlockCertificate c.safety c.env sourceEnv Hheaders.entries
      R.declared.entries H.entries rules outEnv H.outVEnv := by
  let Hgenerated : GeneratedRecursors c.safety R.declared.venvCtors
      c.lparams H.elimLevel H.localContext stats indTypes H.recInfos
      H.entries := by
    simpa [H.localExtends.safety_eq, H.localExtends.lparams_eq] using
      H.generated
  exact Hgenerated.toBlockCertificate H.staged H.localWF H.bindings H.params
    Hheaders.typesWF R.declared.ctorsWF hrules

def RecursorPhasesResult.generatedCertificate
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv) :
    GeneratedRecursors c.safety R.declared.venvCtors c.lparams H.elimLevel
      H.localContext stats indTypes H.recInfos H.entries := by
  simpa [H.localExtends.safety_eq, H.localExtends.lparams_eq] using H.generated

/-- The semantic batch retained by the installer is the batch stored in the
corresponding generated recursor entry.  Source-info equality, rather than a
second indexing convention, identifies the two rule lists. -/
theorem RecursorPhasesResult.generatedRuleSemantics
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    SemanticBoundGeneratedRecursorRules indTypes stats
      (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
      (AddInductive.getRecLevels H.elimLevel stats.levels)
      H.recursorWF decl owner indTypes[owner]!.ctors
      (recursorMinorOffset indTypes owner)
      (H.generated.entry owner howner).info.rules := by
  rcases H.ruleSemantics.entry owner howner with
    ⟨info, hsource, Hsemantic⟩
  let E := H.generated.entry owner howner
  have hinfo : info = E.info := by
    have heq : ConstantInfo.recInfo info = .recInfo E.info :=
      hsource.symm.trans E.source_eq
    injection heq
  subst info
  simpa [E] using Hsemantic

/-- Pointwise projection used by abstract iota reconstruction.  It exposes
the exact generated source rule together with the semantic trace from the
same executable constructor iteration. -/
theorem RecursorPhasesResult.generatedRuleSemantic
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    (i : Nat) (hctor : i < indTypes[owner]!.ctors.length)
    (hrule : i < (H.generated.entry owner howner).info.rules.length) :
    ∃ Hrule : BoundGeneratedRecursorRule indTypes stats
        (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
        (AddInductive.getRecLevels H.elimLevel stats.levels)
        indTypes[owner]!.ctors[i]
        (recursorMinorOffset indTypes owner + i)
        (H.generated.entry owner howner).info.rules[i],
      Nonempty (Hrule.Semantics
        H.recursorWF decl owner) :=
  (H.generatedRuleSemantics owner howner).entry i hctor hrule

/-- The family selected from the generated residual is exactly the outer
owner whose constructor batch is being traversed. -/
theorem RecursorPhasesResult.generatedRuleSemanticOwner
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    (i : Nat) (hctor : i < indTypes[owner]!.ctors.length)
    (hrule : i < (H.generated.entry owner howner).info.rules.length) :
    ∃ Hrule : BoundGeneratedRecursorRule indTypes stats
        (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
        (AddInductive.getRecLevels H.elimLevel stats.levels)
        indTypes[owner]!.ctors[i]
        (recursorMinorOffset indTypes owner + i)
        (H.generated.entry owner howner).info.rules[i],
      ∃ Hsemantic : Hrule.Semantics
          H.recursorWF decl owner,
        Hsemantic.ownerIdx = owner := by
  rcases H.generatedRuleSemantic owner howner i hctor hrule with
    ⟨Hrule, ⟨Hsemantic⟩⟩
  have htypeNames : (decl.types.map (·.name)).Nodup := by
    have hprefix := (List.nodup_append.mp
      (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup
        R.core)).1
    simpa [VInductDecl.sourceNames, VInductDecl.typeConstants,
      VInductiveType.toVConstVal, Function.comp_def] using hprefix
  exact ⟨Hrule, Hsemantic, Hsemantic.owner_eq Hrule htypeNames⟩

/-- Complete source alignment for one rule emitted by the mutual recursor
loop.  The entry index selects the same concrete family in `indTypes`, the
same abstract family in `decl.types`, and the same abstract constructor in
that family's constructor list.  The semantic target selected while building
the rule is additionally identified with this owner.  Keeping these facts in
one dependent record prevents later iota reconstruction from silently mixing
the three independent indexing conventions. -/
structure RecursorPhasesResult.GeneratedRuleAlignment
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    (i : Nat) (hctor : i < indTypes[owner]!.ctors.length) where
  sourceOwner_lt : owner < indTypes.size
  sourceCtor_lt : i < indTypes[owner].ctors.length
  abstractOwner_lt : owner < decl.types.length
  abstractCtor_lt : i < decl.types[owner].ctors.length
  ownerTranslation : TrInductiveType sourceEnv Hheaders.context.venv
    c.lparams indTypes[owner] decl.types[owner]
  ctorTranslation : TrSourceConst Hheaders.context.venv c.lparams
    indTypes[owner].ctors[i].name indTypes[owner].ctors[i].type
    decl.types[owner].ctors[i]
  sourceRule_lt : i < (H.generated.entry owner howner).info.rules.length
  rule : BoundGeneratedRecursorRule indTypes stats
    (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
    (AddInductive.getRecLevels H.elimLevel stats.levels)
    indTypes[owner]!.ctors[i]
    (recursorMinorOffset indTypes owner + i)
    (H.generated.entry owner howner).info.rules[i]
  semantics : rule.Semantics
    H.recursorWF decl owner
  semantic_owner : semantics.ownerIdx = owner

/-- Select the fully aligned pointwise rule package directly from the
completed recursor phase.  All bounds not supplied by the caller follow from
the generated-recursors cardinality and the source-declaration translation. -/
theorem RecursorPhasesResult.generatedRuleAlignment
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    (i : Nat) (hctor : i < indTypes[owner]!.ctors.length) :
    Nonempty (H.GeneratedRuleAlignment owner howner i hctor) := by
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have habstractOwner : owner < decl.types.length := by
    simpa [H.cardinality.records] using hrecInfo
  have hsourceOwner : owner < indTypes.size := by
    have htypes : indTypes.size = decl.types.length := by
      simpa using
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
    omega
  have hsourceCtor : i < indTypes[owner].ctors.length := by
    simpa [Array.getElem!_eq_getD, Array.getD, hsourceOwner] using hctor
  have Howner := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt R.core
    owner (by simpa using hsourceOwner) habstractOwner
  rw [Array.getElem_toList] at Howner
  have habstractCtor : i < decl.types[owner].ctors.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Howner]
    exact hsourceCtor
  let Hctor := Lean4Lean.VerifyInductive.TrInductiveType.ctorAt Howner i
    hsourceCtor
    habstractCtor
  let E := H.generated.entry owner howner
  have hsourceRule : i < E.info.rules.length := by
    rw [E.rules.length]
    exact hctor
  rcases H.generatedRuleSemanticOwner owner howner i hctor hsourceRule with
    ⟨Hrule, Hsemantic, hsemanticOwner⟩
  exact ⟨{
    sourceOwner_lt := hsourceOwner
    sourceCtor_lt := hsourceCtor
    abstractOwner_lt := habstractOwner
    abstractCtor_lt := habstractCtor
    ownerTranslation := Howner
    ctorTranslation := Hctor
    sourceRule_lt := hsourceRule
    rule := Hrule
    semantics := Hsemantic
    semantic_owner := hsemanticOwner }⟩

/-- The recursor selected by a generated rule carries the exact five-part,
binder-typed telescope recovered from the production `.recInfo`.  This is
the canonical source of the parameter, motive, and minor domains used when
typing the corresponding equation; it does not reconstruct those domains
from the rule RHS. -/
theorem RecursorPhasesResult.recursorTelescopeTranslationAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    Nonempty (GeneratedRecursorTelescopeTranslation R.declared.venvCtors
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) := by
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  let E := H.generated.entry owner howner
  rcases H.generatedTelescopeTranslations owner howner with
    ⟨info, hinfo, ⟨T⟩⟩
  have hinfoEq : info = E.info := by
    have heq : ConstantInfo.recInfo info = .recInfo E.info :=
      hinfo.symm.trans E.source_eq
    injection heq
  subst info
  refine ⟨?_⟩
  simpa [E.levels, H.localExtends.lparams_eq] using T

theorem RecursorPhasesResult.finalRecursorTelescopeTranslationAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    Nonempty (GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) := by
  rcases H.recursorTelescopeTranslationAt owner howner with ⟨T⟩
  exact ⟨T.mono H.installed.le⟩

/-- The translated common prefixes of any two installed mutual recursors
are definitionally equal.  The proof is deliberately factored through the
concrete generated source binders, so it does not assume that independently
translated abstract domain lists are syntactically identical. -/
theorem RecursorPhasesResult.finalRecursorCommonPrefixContextAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (owner₁ : Nat) (howner₁ : owner₁ < H.entries.length)
    (owner₂ : Nat) (howner₂ : owner₂ < H.entries.length)
    (T₁ : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner₁ howner₁).info.type
      H.entries[owner₁].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner₁]!.indices.size owner₁)
    (T₂ : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner₂ howner₂).info.type
      H.entries[owner₂].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner₂]!.indices.size owner₂) :
    VEnv.IsDefEqCtx H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
      (T₁.params ++ T₁.motives ++ T₁.minors).reverse
      (T₂.params ++ T₂.motives ++ T₂.minors).reverse := by
  apply T₁.commonPrefixDefEqCtx H.outVEnvWF T₂
  intro i hi _hi₁ _hi₂ domain₁ domain₂ Hbinder₁ Hbinder₂
  exact H.generatedRecursorCommonPrefixBinderDomainAt
    owner₁ howner₁ owner₂ howner₂ i hi Hbinder₁ Hbinder₂

theorem RecursorPhasesResult.GeneratedRuleAlignment.recursorTelescopeTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (_A : H.GeneratedRuleAlignment owner howner i hctor) :
    Nonempty (GeneratedRecursorTelescopeTranslation R.declared.venvCtors
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) := by
  exact H.recursorTelescopeTranslationAt owner howner

theorem RecursorPhasesResult.GeneratedRuleAlignment.finalRecursorTelescopeTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    Nonempty (GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) := by
  exact H.finalRecursorTelescopeTranslationAt owner howner

/-- The parameter domains recovered from the installed generated recursor
are definitionally equal to the independently checked cached parameter
scope.  This is the canonical equation-context bridge: it compares contexts,
not syntax, and is derived from translation of the same concrete `mkForall`
prefix on both sides. -/
theorem
    RecursorPhasesResult.finalRecursorParameterContextAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        T.params.reverse parameterDecls.toCtx := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases H.finalRecursorTelescopeTranslationAt owner howner with ⟨T⟩
  let E := H.generated.entry owner howner
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  let selections := H.bindings.toRecursorLocalSelections H.localWF H.params
    owner hrecInfo
  have hselectionNoAlias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner hrecInfo
  let inner : Expr :=
    H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) <|
    H.localContext.lctx.mkForall (H.recInfos.flatMap (·.minors)) <|
    H.localContext.lctx.mkForall H.recInfos[owner]!.indices <|
    H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
      (.app (mkAppN H.recInfos[owner]!.motive
        H.recInfos[owner]!.indices) H.recInfos[owner]!.major)
  have Hraw : TrExprS H.outVEnv Us []
      (H.localContext.lctx.mkForall stats.params inner)
      H.entries[owner].2.type := by
    have Htranslated := T.typed.translation
    rw [E.type] at Htranslated
    simpa [E.levels, H.localExtends.lparams_eq, inner, Us] using
      TrExprS.of_inferImplicit Htranslated
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv, R.declared.contextVEnv]
    exact H.installed.le
  have Hsort : TrExprS H.outVEnv Us []
      (H.localContext.lctx.mkForall stats.params
        (.sort (.zero : Level)))
      (VExpr.wrapForalls H.parameterSuffix.parameterDecls.toCtx.reverse
        (.sort (.zero : VLevel))) := by
    have HsortBase := H.parameterSuffix.closedSortTranslation
    rw [H.recursorWF.lctx_eq] at HsortBase
    exact HsortBase.mono hbase
  have Hsame : Expr.SameForallPrefix stats.params.size
      (H.localContext.lctx.mkForall stats.params inner)
      (H.localContext.lctx.mkForall stats.params
        (.sort (.zero : Level))) := by
    exact selections.params.sameForallPrefix
      hselectionNoAlias.parts.params inner (.sort (.zero : Level))
  have hnil : VLCtx.IsDefEq H.outVEnv Us.length ([] : VLCtx) [] :=
    .refl H.outVEnvWF.ordered (by trivial)
  rcases Hsame.translatedContexts H.outVEnvWF hnil Hraw Hsort with
    ⟨leftDomains, leftResidual, rightDomains, rightResidual,
      hleftLength, hrightLength, hleftTarget, hrightTarget, hcontexts⟩
  have hleftEq : leftDomains = T.params := by
    apply VExpr.wrapForalls_prefix_domains_eq hleftLength T.params_length
    calc
      VExpr.wrapForalls leftDomains leftResidual = H.entries[owner].2.type :=
        hleftTarget.symm
      _ = VExpr.wrapForalls
          (T.params ++ (T.motives ++ T.minors ++ T.indices ++ T.major))
          T.result := by
        simpa [List.append_assoc] using T.target_eq
  have hparameterCtxLength : H.parameterSuffix.parameterDecls.toCtx.length =
      stats.params.size := by
    calc
      H.parameterSuffix.parameterDecls.toCtx.length =
          H.parameterSuffix.parameterDecls.length :=
        checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
          H.parameterSuffix.cached
      _ = stats.params.size := H.parameterSuffix.parameterDecls_length
  have hrightEq : rightDomains =
      H.parameterSuffix.parameterDecls.toCtx.reverse := by
    apply VExpr.wrapForalls_prefix_domains_eq hrightLength
      (by simpa using hparameterCtxLength)
    calc
      VExpr.wrapForalls rightDomains rightResidual =
          VExpr.wrapForalls H.parameterSuffix.parameterDecls.toCtx.reverse
            (.sort (.zero : VLevel)) := hrightTarget.symm
      _ = VExpr.wrapForalls
          (H.parameterSuffix.parameterDecls.toCtx.reverse ++ [])
          (.sort (.zero : VLevel)) := by simp
  refine ⟨T, ?_⟩
  simpa only [hleftEq, hrightEq, parameterDecls, ← H.parameterDecls,
    VLCtx.toCtx, List.append_nil, List.reverse_reverse] using hcontexts

/-- Translate the common parameter prefix of a generated recursor without
using the generated recursor translation itself.  The dummy sort telescope
comes from the pre-installation header certificate, so it can be weakened
into an independently compiled source environment even when the production
recursor suffix mentions lowered nested auxiliaries.  `SameForallDomains`
records the exact concrete-domain agreement after `inferImplicit`, while
deliberately forgetting the residual-dependent binder annotations. -/
theorem RecursorPhasesResult.sourceRecursorParameterTemplateAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    {newEnv : VEnv} (hsourceLE : sourceEnv ≤ newEnv) :
    let E := H.generated.entry owner howner
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let sourceSuffix :=
      Hheaders.sourceMaterialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible
    let template :=
      (c.lctx.mkForall stats.params
        (.sort (.zero : Level))).inferImplicit 1000 false
    Expr.ForallTelescope template stats.params.size
        (.sort (.zero : Level)) ∧
      Expr.SameForallDomains stats.params.size template E.info.type ∧
      TrExprS newEnv Us [] template
        (VExpr.wrapForalls sourceSuffix.parameterDecls.toCtx.reverse
          (.sort (.zero : VLevel))) := by
  let E := H.generated.entry owner howner
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let sourceSuffix :=
    Hheaders.sourceMaterialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible
  let template :=
    (c.lctx.mkForall stats.params
      (.sort (.zero : Level))).inferImplicit 1000 false
  let sourceParams :=
    Hheaders.sourceMaterialized.parameterSuffix.paramsBound
  let sourceSelection := sourceParams.toLocalForallSelection
    Hheaders.sourceContext.toBindingContextWF
  have HtemplateRaw := sourceSelection.forallTelescope
    (.sort (.zero : Level))
  have htemplateResidual :
      (Expr.sort (.zero : Level)).abstractList sourceSelection.fvars =
        .sort (.zero : Level) := by
    induction sourceSelection.fvars with
    | nil => rfl
    | cons fv fvars ih =>
      simp only [Expr.abstractList]
      rw [show (Expr.sort (.zero : Level)).abstract1 fv =
        .sort (.zero : Level) by rfl]
      exact ih
  rw [htemplateResidual] at HtemplateRaw
  have HtemplateTelescope : Expr.ForallTelescope template stats.params.size
      (.sort (.zero : Level)) := by
    simpa [template] using
      HtemplateRaw.inferImplicit_sameResidual (by rfl) 1000 false
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  let selections := H.bindings.toRecursorLocalSelections H.localWF H.params
    owner hrecInfo
  have hselectionNoAlias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner hrecInfo
  let inner : Expr :=
    H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) <|
    H.localContext.lctx.mkForall (H.recInfos.flatMap (·.minors)) <|
    H.localContext.lctx.mkForall H.recInfos[owner]!.indices <|
    H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
      (.app (mkAppN H.recInfos[owner]!.motive
        H.recInfos[owner]!.indices) H.recInfos[owner]!.major)
  have HrawPrefix : Expr.SameForallPrefix stats.params.size
      (H.localContext.lctx.mkForall stats.params
        (.sort (.zero : Level)))
      (H.localContext.lctx.mkForall stats.params inner) :=
    selections.params.sameForallPrefix
      hselectionNoAlias.parts.params (.sort (.zero : Level)) inner
  have hsourceMkForall :
      H.localContext.lctx.mkForall stats.params
          (.sort (.zero : Level)) =
        c.lctx.mkForall stats.params (.sort (.zero : Level)) := by
    let sourceParamsAtCtor : BoundFVarArray { c with env := ctorEnv }
        stats.params := sourceParams.monoFVars (by
          intro fv hfv
          exact hfv)
    exact sourceParamsAtCtor.mkForall_mono H.localExtends
      (.sort (.zero : Level))
  have Hdomains : Expr.SameForallDomains stats.params.size template
      E.info.type := by
    have Himplicit := HrawPrefix.sameForallDomains.inferImplicit 1000 false
    rw [hsourceMkForall] at Himplicit
    rw [E.type]
    simpa [template, inner] using Himplicit
  have HsourceTranslation : TrExprS sourceEnv Us []
      (c.lctx.mkForall stats.params (.sort (.zero : Level)))
      (VExpr.wrapForalls sourceSuffix.parameterDecls.toCtx.reverse
        (.sort (.zero : VLevel))) := by
    have Hbase := sourceSuffix.closedSortTranslation
    let sourceRecContext :=
      Hheaders.sourceContext.toAdmissibleRecursorContextWF
        H.elimLevelAdmissible
    have hlctx : sourceRecContext.mlctx.lctx = c.lctx :=
      sourceRecContext.lctx_eq
    have hvenv : sourceRecContext.venv = sourceEnv :=
      (ContextWF.toAdmissibleRecursorContextWF_venv
        Hheaders.sourceContext H.elimLevelAdmissible).trans
          Hheaders.sourceContextVEnv
    rw [hlctx, hvenv] at Hbase
    simpa [Us, sourceSuffix] using Hbase
  have HtemplateTranslation : TrExprS newEnv Us [] template
      (VExpr.wrapForalls sourceSuffix.parameterDecls.toCtx.reverse
        (.sort (.zero : VLevel))) := by
    exact TrExprS.inferImplicit (HsourceTranslation.mono hsourceLE) 1000 false
  exact ⟨HtemplateTelescope, Hdomains, HtemplateTranslation⟩

/-- Rule-local specialization of `finalRecursorParameterContextAt`. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalRecursorParameterContext
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (_A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        T.params.reverse parameterDecls.toCtx := by
  exact H.finalRecursorParameterContextAt owner howner

/-- Every retained translation of the installed generated recursor has the
same canonical parameter context.  The existential witness selected by
`finalRecursorParameterContextAt` is immaterial because the five retained
telescope groups are uniquely determined by the common source and target. -/
theorem
    RecursorPhasesResult.finalRecursorParameterContextFor
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    {owner : Nat} (howner : owner < H.entries.length)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) :
    VEnv.IsDefEqCtx H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
      T.params.reverse
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls.toCtx := by
  rcases H.finalRecursorParameterContextAt owner howner with
    ⟨T₀, Hparams⟩
  have hparams : T.params = T₀.params :=
    (T.groupsResult_eq T₀).1
  simpa only [hparams] using Hparams

/-- The original production constructor type has exactly the common
parameter prefix replayed by `mkRecInfos`, followed by the genuine field
suffix opened while generating this rule.  This is a source-syntax fact: it
does not identify the rule's larger retained local context with the canonical
equation context. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.sourceConstructorTelescope
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    ∃ residual,
      Expr.ForallTelescope
        ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).type
        (stats.params.size + A.rule.allArgs.size) residual := by
  rcases A.semantics.parameterPrefix.toNestedParamOpening
      A.rule.params_bound with ⟨parameterLctx, Hparams⟩
  have Hsource := Hparams.reflectForallTelescope
    A.semantics.fieldOpening.telescope
  simpa [Array.getElem!_eq_getD, Array.getD, A.sourceOwner_lt] using Hsource

/-- Inverting the independently checked source-constant translation along
the exact combined parameter/field telescope exposes a typed abstract
constructor telescope in the final environment.  Its universe names are
still the declaration names; recursor-level reindexing is a separate step. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSourceConstructorTelescope
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    ∃ residual,
      Expr.ForallTelescope
        ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).type
        (stats.params.size + A.rule.allArgs.size) residual ∧
      Expr.ForallTelescopeTypeTranslation H.outVEnv c.lparams []
        ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).type
        (stats.params.size + A.rule.allArgs.size)
        ((decl.types[owner]'A.abstractOwner_lt).ctors[i]'A.abstractCtor_lt).type := by
  rcases A.sourceConstructorTelescope with ⟨residual, Htelescope⟩
  have henv : Hheaders.context.venv ≤ H.outVEnv :=
    R.declared.installed.le.trans H.installed.le
  have Htranslation := A.ctorTranslation.type.mono henv
  have Htype : H.outVEnv.IsType c.lparams.length []
      ((decl.types[owner]'A.abstractOwner_lt).ctors[i]'A.abstractCtor_lt).type := by
    simpa [VConstant.WF, A.ctorTranslation.uvars] using
      A.ctorTranslation.wf.mono henv
  exact ⟨residual, Htelescope,
    Expr.ForallTelescopeTypeTranslation.ofTrExprS Htelescope
      Htranslation Htype⟩

/-- Parameter/field decomposition of the original constructor telescope.
The field certificate is now checked under precisely the abstract parameter
prefix, with no motives, minors, mutual indices, or majors retained from the
executable reader context. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSourceConstructorFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    ∃ parameterDomains fieldSource fieldTarget,
      parameterDomains.length = stats.params.size ∧
      Expr.ForallTelescope
        ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).type
        stats.params.size fieldSource ∧
      ((decl.types[owner]'A.abstractOwner_lt).ctors[i]'A.abstractCtor_lt).type =
        VExpr.wrapForalls parameterDomains fieldTarget ∧
      Expr.ForallTelescopeTypeTranslation H.outVEnv c.lparams
        (abstractForallContext parameterDomains []) fieldSource
        A.rule.allArgs.size fieldTarget := by
  rcases A.finalSourceConstructorTelescope with
    ⟨_residual, _Htelescope, Htyped⟩
  exact Htyped.dropPrefix

/-- Re-select the constructor-checking synthesis for this exact source
position and transport it across recursor installation.  Unlike
`finalSourceConstructorFrame`, this certificate is already rebased to the
recursor universe list and uses the materialized canonical parameter scope. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCheckedConstructorSynthesis
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ ctorVal tailTarget,
      ctorVal ∈ (decl.types[owner]'A.abstractOwner_lt).ctors ∧
      ctorVal.name =
        ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name ∧
      Nonempty
        (checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          H.outVEnv Us
          (recursorConstructorTelescopeTarget ctorVal
            H.elimLevelAdmissible)
          parameterDecls tailTarget stats.params.size 0) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases R.checkedConstructorPrefixSeedAt H.elimLevelAdmissible
      H.lparamsNodup owner A.sourceOwner_lt i A.sourceCtor_lt with
    ⟨ctorVal, _tail, tailTarget, _introTarget, hctorMem, hctorName,
      _Hprefix, _Htail, _HtailType, _Hintro, _HintroShape,
      _HintroType, ⟨Hsynthesis⟩⟩
  refine ⟨ctorVal, tailTarget, ?_, hctorName, ⟨?_⟩⟩
  · simpa using hctorMem
  · have hbaseLE :
        (R.declared.context.toAdmissibleRecursorContextWF
          H.elimLevelAdmissible).venv ≤ H.outVEnv := by
      rw [ContextWF.toAdmissibleRecursorContextWF_venv,
        R.declared.contextVEnv]
      exact H.installed.le
    simpa [Us, parameterDecls] using Hsynthesis.mono hbaseLE

/-- The independently checked constructor application transports into the
actual generated recursor parameter context.  The translated term and its
residual type are retained from constructor checking; only the ambient
context changes, via `finalRecursorParameterContext`. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCheckedConstructorApplication
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (tailTarget introTarget : VExpr),
        TrExprS H.outVEnv Us parameterDecls
          (mkAppN
            (.const
              ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
              stats.levels)
            stats.params) introTarget ∧
        introTarget = VExpr.mkApps
          (.const
            ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
            (recursorDeclarationAbstractLevels c.lparams
              H.elimLevelAdmissible))
          (recursorCanonicalVars stats.params.size) ∧
        H.outVEnv.HasType Us.length T.params.reverse
          introTarget tailTarget := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.finalRecursorParameterContext with ⟨T, hparams⟩
  rcases R.checkedConstructorPrefixSeedAt H.elimLevelAdmissible
      H.lparamsNodup owner A.sourceOwner_lt i A.sourceCtor_lt with
    ⟨_ctorVal, _tail, tailTarget, introTarget, _hctorMem, _hctorName,
      _Hprefix, _Htail, _HtailType, Hintro, HintroShape,
      HintroType, _Hsynthesis⟩
  have hbaseLE :
      (R.declared.context.toAdmissibleRecursorContextWF
        H.elimLevelAdmissible).venv ≤ H.outVEnv := by
    rw [ContextWF.toAdmissibleRecursorContextWF_venv,
      R.declared.contextVEnv]
    exact H.installed.le
  have Hintro' : TrExprS H.outVEnv Us parameterDecls
      (mkAppN (.const
          ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
          stats.levels)
        stats.params) introTarget := by
    simpa [Us, parameterDecls] using Hintro.mono hbaseLE
  have HintroType' : H.outVEnv.HasType Us.length parameterDecls.toCtx
      introTarget tailTarget := by
    simpa [Us, parameterDecls] using HintroType.mono hbaseLE
  refine ⟨T, tailTarget, introTarget, Hintro', HintroShape, ?_⟩
  exact HintroType'.defeqDFC H.outVEnvWF.ordered
    (hparams.symm H.outVEnvWF.ordered)

/-- Decompose the independently checked constructor tail along the genuine
field telescope retained by rule generation.  This joins the constructor
checker and recursor generator only through their common source tail; the
abstract parameter contexts are related by conversion, not by syntactic
equality. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCheckedConstructorFieldFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (fieldDomains : List VExpr) (fieldResult introTarget : VExpr),
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          T.params.reverse parameterDecls.toCtx ∧
        fieldDomains.length = A.rule.allArgs.size ∧
        TrExprS H.outVEnv Us parameterDecls
          A.semantics.parameterTail
          (VExpr.wrapForalls fieldDomains fieldResult) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext fieldDomains parameterDecls)
          (A.rule.target.abstractList A.semantics.fieldOpening.fvars)
          fieldResult ∧
        H.outVEnv.IsType Us.length parameterDecls.toCtx
          (VExpr.wrapForalls fieldDomains fieldResult) ∧
        H.outVEnv.IsType Us.length T.params.reverse
          (VExpr.wrapForalls fieldDomains fieldResult) ∧
        OnCtx (fieldDomains.reverse ++ T.params.reverse)
          (H.outVEnv.IsType Us.length) ∧
        H.outVEnv.HasType Us.length T.params.reverse introTarget
          (VExpr.wrapForalls fieldDomains fieldResult) ∧
        TrExprS H.outVEnv Us parameterDecls
          (mkAppN
            (.const
              ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
              stats.levels)
            stats.params) introTarget ∧
        introTarget = VExpr.mkApps
          (.const
            ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
            (recursorDeclarationAbstractLevels c.lparams
              H.elimLevelAdmissible))
          (recursorCanonicalVars stats.params.size) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.finalRecursorParameterContext with ⟨T, hparams⟩
  rcases R.checkedConstructorPrefixSeedAt H.elimLevelAdmissible
      H.lparamsNodup owner A.sourceOwner_lt i A.sourceCtor_lt with
    ⟨_ctorVal, tail, tailTarget, introTarget, _hctorMem, _hctorName,
      Hprefix, Htail, HtailType, Hintro, HintroShape,
      HintroType, _Hsynthesis⟩
  have HsemanticPrefix : RecursorParamPrefix stats 0
      ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).type
      A.semantics.parameterTail := by
    simpa [Array.getElem!_eq_getD, Array.getD, A.sourceOwner_lt] using
      A.semantics.parameterPrefix
  have htail : tail = A.semantics.parameterTail :=
    Hprefix.tail_eq HsemanticPrefix
  subst tail
  have hbaseLE :
      (R.declared.context.toAdmissibleRecursorContextWF
        H.elimLevelAdmissible).venv ≤ H.outVEnv := by
    rw [ContextWF.toAdmissibleRecursorContextWF_venv,
      R.declared.contextVEnv]
    exact H.installed.le
  have Htail' : TrExprS H.outVEnv Us parameterDecls
      A.semantics.parameterTail tailTarget := by
    simpa [Us, parameterDecls] using Htail.mono hbaseLE
  have HtailType' : H.outVEnv.IsType Us.length parameterDecls.toCtx
      tailTarget := by
    simpa [Us, parameterDecls] using HtailType.mono hbaseLE
  have Hintro' : TrExprS H.outVEnv Us parameterDecls
      (mkAppN
        (.const
          ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
          stats.levels)
        stats.params) introTarget := by
    simpa [Us, parameterDecls] using Hintro.mono hbaseLE
  have HintroType' : H.outVEnv.HasType Us.length T.params.reverse
      introTarget tailTarget := by
    have Htyped : H.outVEnv.HasType Us.length parameterDecls.toCtx
        introTarget tailTarget := by
      simpa [Us, parameterDecls] using HintroType.mono hbaseLE
    exact Htyped.defeqDFC H.outVEnvWF.ordered
      (hparams.symm H.outVEnvWF.ordered)
  have Hfields := Expr.ForallTelescopeTypeTranslation.ofTrExprS
    A.semantics.fieldOpening.telescope Htail' HtailType'
  rcases Hfields.toWrapForalls with
    ⟨fieldDomains, sourceResidual, fieldResult, hfields,
      HsourceTelescope, htarget, Hresult, _HresultType⟩
  have hsourceResidual :
      sourceResidual = A.semantics.fieldOpening.residual :=
    HsourceTelescope.residual_eq A.semantics.fieldOpening.telescope
  have HfieldResidual : TrExprS H.outVEnv Us
      (abstractForallContext fieldDomains parameterDecls)
      (A.rule.target.abstractList A.semantics.fieldOpening.fvars)
      fieldResult := by
    rw [A.semantics.fieldOpening.closed, ← hsourceResidual]
    exact Hresult
  subst tailTarget
  have HtailTypeT : H.outVEnv.IsType Us.length T.params.reverse
      (VExpr.wrapForalls fieldDomains fieldResult) :=
    HtailType'.defeqDFC H.outVEnvWF.ordered
      (hparams.symm H.outVEnvWF.ordered)
  have HfieldContext : OnCtx
      (fieldDomains.reverse ++ T.params.reverse)
      (H.outVEnv.IsType Us.length) :=
    (VEnv.IsType.wrapForalls_inv H.outVEnvWF.ordered
      hparams.isType HtailTypeT).1
  exact ⟨T, fieldDomains, fieldResult, introTarget, hparams, hfields,
    Htail', HfieldResidual, HtailType', HtailTypeT, HfieldContext,
    HintroType', Hintro', HintroShape⟩

/-- Close the cached common parameters around a constructor result already
translated below its genuine field telescope.  Keeping this lemma
parameterized by the field-frame witnesses lets later equation proofs retain
the very same recursor telescope witness. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.cachedConstructorTargetOfFieldFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (fieldDomains : List VExpr) (fieldResult : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (HfieldResidual : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext fieldDomains
        (R.materialized.parameterSuffix.toRecursorContext
          H.elimLevelAdmissible).parameterDecls)
      (A.rule.target.abstractList A.semantics.fieldOpening.fvars)
      fieldResult) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    TrExprS H.outVEnv Us
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ fieldDomains) [])
      (A.rule.target.abstractList
        (A.rule.params_bound.fvars ++
          A.semantics.fieldOpening.fvars))
      fieldResult := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  dsimp only
  have hparamExprs : stats.params.toList.reverse =
      (A.rule.params_bound.fvars.reverse.map Expr.fvar) := by
    have h := congrArg Array.toList A.rule.params_bound.expressions
    simpa [List.map_reverse] using congrArg List.reverse h
  have Hcached : List.Forall₂
      checkInductiveTypes.loopType.CachedParameterDecl
      (A.rule.params_bound.fvars.reverse.map Expr.fvar) parameterDecls := by
    have Hbase := H.parameterSuffix.cached
    rw [hparamExprs] at Hbase
    simpa [parameterDecls, H.parameterDecls] using Hbase
  have Hdecls : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type))
      A.rule.params_bound.fvars.reverse parameterDecls := by
    rw [List.forall₂_map_left_iff] at Hcached
    exact Lean4Lean.List.Forall₂.imp (fun fv entry hentry => by
      rcases hentry with ⟨actual, deps, type, hparam, hentry⟩
      cases Expr.fvar.inj hparam
      exact ⟨deps, type, hentry⟩) Hcached
  have hparamsNodup : A.rule.params_bound.fvars.reverse.Nodup :=
    List.nodup_reverse.mpr <|
      (List.nodup_append.mp
        (List.nodup_append.mp A.rule.outer_binders_nodup).1).1
  have Hclosed :=
    Lean4Lean.VerifyInductive.TrExprS.abstractFVarLambdaSuffix
      Hdecls hparamsNodup HfieldResidual
  have hparamsFields :
      (A.rule.params_bound.fvars ++
        A.semantics.fieldOpening.fvars).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨List.nodup_reverse.mp hparamsNodup,
      A.semantics.fieldOpening.nodup, ?_⟩
    intro param hparam field hfield heq
    subst field
    rw [A.semantics.fieldOpening.fvars_eq_bound
      A.rule.all_args_bound] at hfield
    exact A.rule.all_args_outer_fresh param hfield
      (List.mem_append_left _ (List.mem_append_left _ hparam))
  have hfieldLength : A.semantics.fieldOpening.fvars.length =
      fieldDomains.length := by
    rw [A.semantics.fieldOpening.fvars_eq_bound
      A.rule.all_args_bound, hfields]
    have h := congrArg Array.size A.rule.all_args_bound.expressions
    simpa using h.symm
  have hsource := Expr.abstractList_after_inner
    (e := A.rule.target) (outer := A.rule.params_bound.fvars)
    (inner := A.semantics.fieldOpening.fvars) (k := 0) hparamsFields
  have hsource' :
      ((A.rule.target.abstractList A.semantics.fieldOpening.fvars).abstractList
          A.rule.params_bound.fvars fieldDomains.length) =
        A.rule.target.abstractList
          (A.rule.params_bound.fvars ++
            A.semantics.fieldOpening.fvars) := by
    simpa [hfieldLength] using hsource
  simp only [List.reverse_reverse] at Hclosed
  rw [hsource'] at Hclosed
  simpa [parameterDecls, List.reverse_reverse] using Hclosed

/-- Close the cached common parameters around the already closed constructor
field target.  This preserves the exact strict target translation, including
indices containing projections, while replacing every production free
variable by its canonical de Bruijn binder. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCachedConstructorTarget
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (fieldDomains : List VExpr) (fieldResult : VExpr),
        fieldDomains.length = A.rule.allArgs.size ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            (parameterDecls.toCtx.reverse ++ fieldDomains) [])
          (A.rule.target.abstractList
            (A.rule.params_bound.fvars ++
              A.semantics.fieldOpening.fvars))
          fieldResult := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.finalCheckedConstructorFieldFrame with
    ⟨T, fieldDomains, fieldResult, _introTarget, _hparams, hfields,
      _Htail, HfieldResidual, _HtailType, _HtailTypeT, _HfieldContext,
      _HintroType, _Hintro, _HintroShape⟩
  exact ⟨T, fieldDomains, fieldResult, hfields,
    A.cachedConstructorTargetOfFieldFrame fieldDomains fieldResult hfields
      HfieldResidual⟩

/-- The lift introduced between parameters and fields is exactly simultaneous
abstraction over the rule's complete parameter/motive/minor/field binder list.
This follows from strict-translation scoping: the constructor result can only
mention parameters and genuine fields, hence motives and minors merely shift
the already abstracted parameter variables. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.canonicalTargetBinderLift_eq
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr) (fieldResult : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (Htarget : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (((R.materialized.parameterSuffix.toRecursorContext
            H.elimLevelAdmissible).parameterDecls.toCtx.reverse) ++
          fieldDomains) [])
      (A.rule.target.abstractList
        (A.rule.params_bound.fvars ++
          A.semantics.fieldOpening.fvars))
      fieldResult) :
    ((A.rule.target.abstractList
        (A.rule.params_bound.fvars ++
          A.semantics.fieldOpening.fvars)).liftLooseBVars'
      A.rule.allArgs.size (T.motives ++ T.minors).length) =
      A.rule.target.abstractList A.rule.binders := by
  let params := A.rule.params_bound.fvars
  let motives := A.rule.motives_bound.fvars
  let minors := A.rule.minors_bound.fvars
  let fields := A.semantics.fieldOpening.fvars
  let middle := motives ++ minors
  let parameterDecls :=
    (R.materialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  have hparamsLength : params.length = stats.params.size := by
    have h := congrArg Array.size A.rule.params_bound.expressions
    simpa [params] using h.symm
  have hfieldsLength : fields.length = A.rule.allArgs.size := by
    change A.semantics.fieldOpening.fvars.length = A.rule.allArgs.size
    rw [A.semantics.fieldOpening.fvars_eq_bound
      A.rule.all_args_bound]
    have h := congrArg Array.size A.rule.all_args_bound.expressions
    simpa using h.symm
  have hparameterDeclsLength : parameterDecls.toCtx.length =
      stats.params.size := by
    have hcached := H.parameterSuffix.cached
    have h :=
      checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
        hcached
    calc
      parameterDecls.toCtx.length = parameterDecls.length := by
        simpa [parameterDecls, H.parameterDecls] using h
      _ = stats.params.size := by
        simpa [parameterDecls, H.parameterDecls] using
          H.parameterSuffix.parameterDecls_length
  have hparamsFields : (params ++ fields).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨(List.nodup_append.mp
        (List.nodup_append.mp A.rule.outer_binders_nodup).1).1,
      A.semantics.fieldOpening.nodup, ?_⟩
    intro param hparam field hfield heq
    subst field
    have hfield' : param ∈ A.rule.all_args_bound.fvars := by
      simpa [fields, A.semantics.fieldOpening.fvars_eq_bound
        A.rule.all_args_bound] using hfield
    exact A.rule.all_args_outer_fresh param hfield'
      (List.mem_append_left _ (List.mem_append_left _ hparam))
  have hsourceClosed : Closed
      (A.rule.target.abstractList (params ++ fields))
      (params ++ fields).length := by
    have hclosed := Htarget.closed
    simpa [params, fields, VLCtx.bvars,
      parameterDecls, hparamsLength, hfieldsLength, hfields,
      hparameterDeclsLength] using hclosed
  have htargetClosed : Closed A.rule.target 0 :=
    Expr.closed_of_abstractList (e := A.rule.target)
      (fvars := params ++ fields) (depth := 0) (by
        simpa using hsourceClosed)
  have hsourceFVars :
      (A.rule.target.abstractList (params ++ fields)).FVarsIn
        (fun _ => False) := by
    have hfvars := Htarget.fvarsIn
    simpa [abstractForallContext, VLCtx.fvars, params, fields,
      parameterDecls] using hfvars
  have htargetFVars : A.rule.target.FVarsIn
      (fun fv => fv ∈ params ++ fields) := by
    exact (FVarsIn.of_abstractList hsourceFVars).mono fun fv h => by
      simpa using h
  have houterSplit := List.nodup_append.mp A.rule.outer_binders_nodup
  have hparamsMotivesSplit :=
    List.nodup_append.mp houterSplit.1
  have htargetAvoidsMiddle : A.rule.target.FVarsIn
      (fun fv => fv ∉ middle) := by
    apply htargetFVars.mono
    intro fv hfv hmiddle
    rcases List.mem_append.mp hfv with hparam | hfield
    · rcases List.mem_append.mp hmiddle with hmotive | hminor
      · exact hparamsMotivesSplit.2.2 fv hparam fv hmotive rfl
      · exact houterSplit.2.2 fv
          (List.mem_append_left _ hparam) fv hminor rfl
    · have hfield' : fv ∈ A.rule.all_args_bound.fvars := by
        simpa [fields, A.semantics.fieldOpening.fvars_eq_bound
          A.rule.all_args_bound] using hfield
      apply A.rule.all_args_outer_fresh fv hfield'
      rcases List.mem_append.mp hmiddle with hmotive | hminor
      · exact List.mem_append_left _
          (List.mem_append_right _ hmotive)
      · exact List.mem_append_right _ hminor
  have hmiddleAbstract : A.rule.target.abstractList middle = A.rule.target :=
    htargetAvoidsMiddle.abstractList_eq_self htargetClosed
  let targetFields := A.rule.target.abstractList fields
  have hparamsFieldsShape :
      targetFields.abstractList params fields.length =
        A.rule.target.abstractList (params ++ fields) := by
    simpa [targetFields] using Expr.abstractList_after_inner
      (e := A.rule.target) (outer := params) (inner := fields) (k := 0)
      hparamsFields
  have htargetFieldsClosed : Closed targetFields fields.length := by
    apply Expr.closed_of_abstractList
    rw [hparamsFieldsShape]
    simpa [List.length_append, Nat.add_comm] using hsourceClosed
  have hshift := Expr.abstractList_add_eq_liftLooseBVars
    (e := targetFields) (fvars := params) (depth := fields.length)
    (extra := middle.length) htargetFieldsClosed
    (List.nodup_append.mp
      (List.nodup_append.mp A.rule.outer_binders_nodup).1).1
  have hfullShape := Expr.abstractList_after_inner
    (e := A.rule.target) (outer := params)
    (inner := middle ++ fields) (k := 0) (by
      simpa [params, motives, minors, fields, middle,
        A.semantics.fieldOpening.fvars_eq_bound A.rule.all_args_bound,
        BoundGeneratedRecursorRule.binders, List.append_assoc] using
        A.rule.binders_nodup)
  rw [Expr.abstractList_append, hmiddleAbstract] at hfullShape
  have hmiddleLength : middle.length =
      (T.motives ++ T.minors).length := by
    have hm : motives.length = (H.recInfos.map (·.motive)).size := by
      have h := congrArg Array.size A.rule.motives_bound.expressions
      simpa [motives] using h.symm
    have hmi : minors.length =
        (H.recInfos.flatMap (·.minors)).size := by
      have h := congrArg Array.size A.rule.minors_bound.expressions
      simpa [minors] using h.symm
    simp [middle, hm, hmi, T.motives_length, T.minors_length]
  have hfullShape' :
      targetFields.abstractList params (fields.length + middle.length) =
        A.rule.target.abstractList (params ++ (middle ++ fields)) := by
    simpa [targetFields, List.length_append, Nat.add_comm,
      List.append_assoc] using hfullShape
  calc
    (A.rule.target.abstractList (params ++ fields)).liftLooseBVars'
        A.rule.allArgs.size (T.motives ++ T.minors).length =
        (targetFields.abstractList params fields.length).liftLooseBVars'
          fields.length middle.length := by
            rw [hparamsFieldsShape, hfieldsLength, hmiddleLength]
    _ = targetFields.abstractList params (fields.length + middle.length) :=
      hshift.symm
    _ = A.rule.target.abstractList (params ++ (middle ++ fields)) :=
      hfullShape'
    _ = A.rule.target.abstractList A.rule.binders := by
      simp [BoundGeneratedRecursorRule.binders, params, motives, minors,
        fields, middle,
        A.semantics.fieldOpening.fvars_eq_bound A.rule.all_args_bound,
        List.append_assoc]

/-- Insert motives and minors beneath the closed constructor fields while
retaining a strict translation of the constructor result.  The source lift
is the precise de Bruijn effect of the otherwise unused generated binders. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCachedConstructorEquationTarget
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (fieldDomains : List VExpr) (fieldResult : VExpr),
        fieldDomains.length = A.rule.allArgs.size ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
              fieldDomains) [])
          (A.rule.target.abstractList A.rule.binders)
          (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.finalCachedConstructorTarget with
    ⟨T, originalDomains, fieldResult, hfields, Htarget⟩
  let inserted := T.motives ++ T.minors
  let fieldDomains :=
    (liftContextPrefix inserted.length originalDomains.reverse).reverse
  have W := abstractForallContext.bvInsertBeforeInner
    parameterDecls.toCtx.reverse inserted originalDomains
  have Hweak := Htarget.weakBV H.outVEnvWF.ordered W
  have hsource := A.canonicalTargetBinderLift_eq
    T originalDomains fieldResult hfields Htarget
  have hsource' :
      ((A.rule.target.abstractList
          (A.rule.params_bound.fvars ++
            A.semantics.fieldOpening.fvars)).liftLooseBVars'
        originalDomains.length inserted.length) =
        A.rule.target.abstractList A.rule.binders := by
    simpa [inserted, hfields] using hsource
  rw [hsource'] at Hweak
  have hfieldDomains : fieldDomains.length = A.rule.allArgs.size := by
    simp [fieldDomains, hfields]
  exact ⟨T, fieldDomains, fieldResult, hfieldDomains, by
    simpa [parameterDecls, inserted, fieldDomains, hfields,
      List.append_assoc] using Hweak⟩

/-- Invert a cached constructor target belonging to a fixed recursor
telescope.  Keeping `T` explicit is essential when the resulting index spine
is consumed by the matching recursor suffix. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.cachedConstructorIndexSpineOfTarget
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr) (fieldResult : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (Htarget :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let parameterDecls :=
        (R.materialized.parameterSuffix.toRecursorContext
          H.elimLevelAdmissible).parameterDecls
      TrExprS H.outVEnv Us
        (abstractForallContext
          ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
            fieldDomains) [])
        (A.rule.target.abstractList A.rule.binders)
        (fieldResult.liftN
          (T.motives ++ T.minors).length A.rule.allArgs.size)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ (levels : List VLevel) (parameterTargets indexTargets : List VExpr),
        (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size).getAppFnArgs =
          (.const (decl.types[owner]'A.abstractOwner_lt).name levels,
            parameterTargets ++ indexTargets) ∧
        stats.levels.mapM (VLevel.ofLevel Us) = some levels ∧
        List.Forall₂
          (TrExprS H.outVEnv Us
            (abstractForallContext
              ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
                fieldDomains) []))
          ((stats.params.map fun arg =>
            arg.abstractList A.rule.binders).toList)
          parameterTargets ∧
        indexTargets.length = T.indices.length ∧
        List.Forall₂
          (TrExprS H.outVEnv Us
            (abstractForallContext
              ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
                fieldDomains) []))
          (((AddInductive.getIIndices stats A.rule.target).2.map fun arg =>
            arg.abstractList A.rule.binders).toList)
          indexTargets := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  dsimp only at Htarget
  have hvalid : AddInductive.isValidIndAppIdx stats A.rule.target owner =
      true := by
    have h := (checkPositivityStep.isValidIndApp?_some
      A.semantics.target_valid).2
    simpa [A.semantic_owner] using h
  have hconst := A.semantics.validStats.indConstAt A.abstractOwner_lt
  have hhead : A.rule.target.getAppFn =
      .const (decl.types[owner]'A.abstractOwner_lt).name stats.levels :=
    checkPositivityStep.isValidIndAppIdx.constHead hvalid hconst
  have hheadAbstract :
      (A.rule.target.abstractList A.rule.binders).getAppFn =
        .const (decl.types[owner]'A.abstractOwner_lt).name stats.levels := by
    rw [Expr.getAppFn_abstractList, hhead]
    induction A.rule.binders <;> simp_all [Expr.abstractList, Expr.abstract1]
  rcases checkPositivityStep.TrExprS.constAppSpine Htarget hheadAbstract with
    ⟨levels, translatedArgs, hspine, hlevels, Hargs⟩
  let indices := (AddInductive.getIIndices stats A.rule.target).2
  have hsourcePrefix := A.semantics.validStats.sourceParameterPrefix hvalid
  have hsourceArgs :
      (A.rule.target.abstractList A.rule.binders).getAppArgsList =
        (stats.params.map fun arg =>
            arg.abstractList A.rule.binders).toList ++
          (indices.map fun arg =>
            arg.abstractList A.rule.binders).toList := by
    rw [Expr.getAppArgsList_abstractList]
    have hsplit : A.rule.target.getAppArgsList =
        stats.params.toList ++ indices.toList := by
      calc
        A.rule.target.getAppArgsList =
            A.rule.target.getAppArgsList.take stats.params.size ++
              A.rule.target.getAppArgsList.drop stats.params.size :=
          (List.take_append_drop _ _).symm
        _ = stats.params.toList ++ indices.toList := by
          rw [hsourcePrefix]
          congr 1
          have hsuffix :
              (A.rule.target.getAppArgs[stats.params.size:]).toList =
                A.rule.target.getAppArgs.toList.drop stats.params.size := by
            rw [List.drop_eq_drop_min]
            simp only [Subarray.toList_eq, Array.array_toSubarray,
              Array.start_toSubarray, Array.stop_toSubarray, Nat.min_self,
              Array.toList_extract, List.extract_eq_take_drop,
              Array.length_toList]
            apply List.take_of_length_le
            simp
          simpa [indices, AddInductive.getIIndices,
            Expr.getAppArgs_toList] using hsuffix.symm
    rw [hsplit]
    simp
  rw [hsourceArgs] at Hargs
  rcases checkPositivityStep.List.Forall₂.split_left Hargs with
    ⟨parameterTargets, indexTargets, htranslatedArgs,
      HparameterTargets, HindexTargets⟩
  have hindicesLength : indices.size = stats.nindices[owner]! := by
    exact checkPositivityStep.getIIndices.index_arity
      A.semantics.target_valid |>.trans (by simp [A.semantic_owner])
  have hindexTargetsLength : indexTargets.length = T.indices.length := by
    have htranslated :=
      Lean4Lean.VerifyInductive.List.Forall₂.length_eq' HindexTargets
    have harity := H.arities owner (by
      simpa [H.generated.length] using howner)
    rw [T.indices_length, harity, ← hindicesLength]
    simpa [indices] using htranslated.symm
  refine ⟨levels, parameterTargets, indexTargets, ?_, hlevels,
    HparameterTargets, hindexTargetsLength, ?_⟩
  · simpa [htranslatedArgs] using hspine
  · simpa [indices] using HindexTargets

/-- Invert the fully abstracted constructor result at its validated family
head.  This exposes the exact translated index suffix in the equation
context, without imposing any syntactic restriction on index expressions. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCachedConstructorIndexSpine
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (fieldDomains : List VExpr) (fieldResult : VExpr)
          (levels : List VLevel) (parameterTargets indexTargets : List VExpr),
        fieldDomains.length = A.rule.allArgs.size ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
              fieldDomains) [])
          (A.rule.target.abstractList A.rule.binders)
          (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size) ∧
        (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size).getAppFnArgs =
          (.const (decl.types[owner]'A.abstractOwner_lt).name levels,
            parameterTargets ++ indexTargets) ∧
        stats.levels.mapM (VLevel.ofLevel Us) = some levels ∧
        List.Forall₂
          (TrExprS H.outVEnv Us
            (abstractForallContext
              ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
                fieldDomains) []))
          ((stats.params.map fun arg =>
            arg.abstractList A.rule.binders).toList)
          parameterTargets ∧
        indexTargets.length = T.indices.length ∧
        List.Forall₂
          (TrExprS H.outVEnv Us
            (abstractForallContext
              ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
                fieldDomains) []))
          (((AddInductive.getIIndices stats A.rule.target).2.map fun arg =>
            arg.abstractList A.rule.binders).toList)
          indexTargets := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.finalCachedConstructorEquationTarget with
    ⟨T, fieldDomains, fieldResult, hfields, Htarget⟩
  rcases A.cachedConstructorIndexSpineOfTarget
      T fieldDomains fieldResult hfields Htarget with
    ⟨levels, parameterTargets, indexTargets, hspine, hlevels,
      HparameterTargets, hindexLength, HindexTargets⟩
  exact ⟨T, fieldDomains, fieldResult, levels, parameterTargets,
    indexTargets, hfields, Htarget, hspine, hlevels, HparameterTargets,
    hindexLength, HindexTargets⟩

/-- Apply the checked constructor to the canonical variables of its genuine
field telescope.  This is done before inserting motives and minors, avoiding
any pointwise formula for lifting dependent field domains. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCheckedConstructorFieldApplication
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (fieldDomains : List VExpr) (fieldResult introTarget : VExpr),
        fieldDomains.length = A.rule.allArgs.size ∧
        H.outVEnv.HasType Us.length
          (fieldDomains.reverse ++ T.params.reverse)
          (VExpr.mkApps (introTarget.liftN fieldDomains.length 0)
            (recursorCanonicalVars fieldDomains.length))
          fieldResult := by
  rcases A.finalCheckedConstructorFieldFrame with
    ⟨T, fieldDomains, fieldResult, introTarget, _hparams, hfields,
      _Htail, _HfieldResidual, _HtailType, _HtailTypeT, _HfieldContext,
      HintroType, _Hintro, _HintroShape⟩
  have Happ := VEnv.HasType.mkApps_wrapForalls_canonical
    H.outVEnvWF.ordered HintroType
  exact ⟨T, fieldDomains, fieldResult, introTarget, hfields, by
    simpa [recursorCanonicalVars] using Happ⟩

/-- Insert the generated motive/minor block beneath the genuine constructor
fields.  `fieldDomains` is rebuilt from the lifted context prefix, so the
resulting canonical equation context remains valid for dependent fields. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCheckedConstructorEquationContextWithFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (originalDomains fieldDomains : List VExpr)
          (fieldResult introTarget : VExpr),
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          T.params.reverse parameterDecls.toCtx ∧
        originalDomains.length = A.rule.allArgs.size ∧
        fieldDomains =
          (liftContextPrefix (T.motives ++ T.minors).length
            originalDomains.reverse).reverse ∧
        TrExprS H.outVEnv Us parameterDecls
          A.semantics.parameterTail
          (VExpr.wrapForalls originalDomains fieldResult) ∧
        OnCtx (originalDomains.reverse ++ T.params.reverse)
          (H.outVEnv.IsType Us.length) ∧
        fieldDomains.length = A.rule.allArgs.size ∧
        OnCtx
          (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
          (H.outVEnv.IsType Us.length) ∧
        H.outVEnv.HasType Us.length
          (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
          ((VExpr.mkApps
              (introTarget.liftN A.rule.allArgs.size 0)
              (recursorCanonicalVars A.rule.allArgs.size)).liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size)
          (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
              fieldDomains) [])
          (A.rule.target.abstractList A.rule.binders)
          (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size) ∧
        introTarget = VExpr.mkApps
          (.const
            ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
            (recursorDeclarationAbstractLevels c.lparams
              H.elimLevelAdmissible))
          (recursorCanonicalVars stats.params.size) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.finalCheckedConstructorFieldFrame with
    ⟨T, originalDomains, fieldResult, introTarget, hparams, hfields,
      Htail, HfieldResidual, _HtailType, HtailTypeT, HfieldContext,
      HintroType, _Hintro, HintroShape⟩
  have HcachedTarget := A.cachedConstructorTargetOfFieldFrame
    originalDomains fieldResult hfields HfieldResidual
  let inserted := T.motives ++ T.minors
  have Wtarget := abstractForallContext.bvInsertBeforeInner
    parameterDecls.toCtx.reverse inserted originalDomains
  have HtargetWeak := HcachedTarget.weakBV H.outVEnvWF.ordered Wtarget
  have hsource := A.canonicalTargetBinderLift_eq
    T originalDomains fieldResult hfields HcachedTarget
  have hsource' :
      ((A.rule.target.abstractList
          (A.rule.params_bound.fvars ++
            A.semantics.fieldOpening.fvars)).liftLooseBVars'
        originalDomains.length inserted.length) =
        A.rule.target.abstractList A.rule.binders := by
    simpa [inserted, hfields] using hsource
  rw [hsource'] at HtargetWeak
  have Happ := VEnv.HasType.mkApps_wrapForalls_canonical
    H.outVEnvWF.ordered HintroType
  let added := inserted.reverse
  let liftedPrefix := liftContextPrefix inserted.length originalDomains.reverse
  let fieldDomains := liftedPrefix.reverse
  have W : Ctx.LiftN inserted.length originalDomains.reverse.length
      (originalDomains.reverse ++ T.params.reverse)
      (liftedPrefix ++ added ++ T.params.reverse) := by
    simpa [liftedPrefix, added] using
      Ctx.LiftN.insertAfterPrefix originalDomains.reverse added T.params.reverse
  have Hweak := Happ.weakN H.outVEnvWF.ordered W
  have W0 : Ctx.LiftN inserted.length 0 T.params.reverse
      (added ++ T.params.reverse) := by
    exact .zero added (by simp [added])
  have HliftedType := HtailTypeT.weakN H.outVEnvWF.ordered W0
  rw [VExpr.liftN_wrapForalls] at HliftedType
  have hbase : OnCtx (added ++ T.params.reverse)
      (H.outVEnv.IsType Us.length) := by
    simpa [added, inserted, List.reverse_append, List.append_assoc] using
      T.prefixContext H.outVEnvWF.ordered
  have Hcontext : OnCtx
      (liftedPrefix ++ added ++ T.params.reverse)
      (H.outVEnv.IsType Us.length) := by
    have Hopened := VEnv.IsType.wrapForalls_inv H.outVEnvWF.ordered
      hbase HliftedType
    simpa [liftedPrefix, liftContextPrefix] using Hopened.1
  have hfieldDomains : fieldDomains.length = A.rule.allArgs.size := by
    simp [fieldDomains, liftedPrefix, hfields]
  refine ⟨T, originalDomains, fieldDomains, fieldResult, introTarget,
    hparams, hfields, ?_, Htail, HfieldContext, hfieldDomains, ?_, ?_, ?_,
    HintroShape⟩
  · simp [fieldDomains, liftedPrefix, inserted]
  · simpa [fieldDomains, liftedPrefix, added, inserted, List.reverse_append,
      List.append_assoc] using Hcontext
  · simpa [fieldDomains, liftedPrefix, added, inserted, hfields, List.reverse_append,
      List.append_assoc, Nat.add_comm, recursorCanonicalVars] using Hweak
  · simpa [parameterDecls, inserted, fieldDomains, liftedPrefix, added,
      hfields, List.append_assoc] using HtargetWeak

/-- Compatibility projection of
`finalCheckedConstructorEquationContextWithFrame` for clients that only need
the installed equation context. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCheckedConstructorEquationContext
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (fieldDomains : List VExpr) (fieldResult introTarget : VExpr),
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          T.params.reverse parameterDecls.toCtx ∧
        fieldDomains.length = A.rule.allArgs.size ∧
        OnCtx
          (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
          (H.outVEnv.IsType Us.length) ∧
        H.outVEnv.HasType Us.length
          (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
          ((VExpr.mkApps
              (introTarget.liftN A.rule.allArgs.size 0)
              (recursorCanonicalVars A.rule.allArgs.size)).liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size)
          (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
              fieldDomains) [])
          (A.rule.target.abstractList A.rule.binders)
          (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size) ∧
        introTarget = VExpr.mkApps
          (.const
            ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
            (recursorDeclarationAbstractLevels c.lparams
              H.elimLevelAdmissible))
          (recursorCanonicalVars stats.params.size) := by
  rcases A.finalCheckedConstructorEquationContextWithFrame with
    ⟨T, _originalDomains, fieldDomains, fieldResult, introTarget,
      hparams, _horiginal, _hlifted, _Htail, _HoriginalCtx, hfields, Hctx, Hmajor,
      Htarget, HintroShape⟩
  exact ⟨T, fieldDomains, fieldResult, introTarget, hparams, hfields,
    Hctx, Hmajor, Htarget, HintroShape⟩

/-- Weaken the checked constructor major below the generated motive/minor
prefix.  The explicit lift is the de Bruijn shift later field and equation
terms must share; retaining it here prevents an implicit context-extension
assumption from entering iota typing. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCheckedConstructorPrefixApplication
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (tailTarget introTarget : VExpr),
        TrExprS H.outVEnv Us parameterDecls
          (mkAppN
            (.const
              ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
              stats.levels)
            stats.params) introTarget ∧
        H.outVEnv.HasType Us.length
          (T.params ++ T.motives ++ T.minors).reverse
          (introTarget.liftN (T.motives ++ T.minors).length 0)
          (tailTarget.liftN (T.motives ++ T.minors).length 0) := by
  rcases A.finalCheckedConstructorApplication with
    ⟨T, tailTarget, introTarget, Hintro, _HintroShape, HintroType⟩
  let added := (T.motives ++ T.minors).reverse
  have W0 : Ctx.LiftN added.length 0 T.params.reverse
      (added ++ T.params.reverse) := .zero added
  have W : Ctx.LiftN added.length 0 T.params.reverse
      ((T.params ++ T.motives ++ T.minors).reverse) := by
    simpa [added, List.reverse_append, List.append_assoc] using W0
  refine ⟨T, tailTarget, introTarget, Hintro, ?_⟩
  simpa [added, Nat.add_comm] using
    HintroType.weakN H.outVEnvWF.ordered W

/-- The terminal inductive application retained by rule generation consumes
the same index telescope as the motive introduced by the first recursor
pass.  The exact root-to-constructor context extension is retained in the
semantic rule package, so this statement does not reconstruct motive
bindings or rerun positivity validation. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.semanticMotiveTelescopeEvidence
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    ∃ binding : RecursorMotiveBinding A.semantics.context
        H.recInfos[owner]! H.elimLevel,
      Nonempty (RecursorMotiveTelescopeEvidence A.semantics.context stats
        H.recInfos[owner]! binding A.rule.target
        A.semantics.targetTarget) := by
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  let Hext : RecursorContextExtension H.recursorWF A.semantics.context :=
    A.semantics.fieldRootExtension.trans
      A.semantics.fieldsRecent.contextExtension
  rcases H.motiveShapes.motiveBindingAtMono
      (Rcurrent := A.semantics.context) H.bindings H.origins
      Hext.contextLE owner hrecInfo with ⟨Hbinding⟩
  let binding : RecursorMotiveBinding A.semantics.context
      H.recInfos[owner]! H.elimLevel := Hbinding.toBinding
  have Hvalidated := A.semantics.validated
  rw [A.semantic_owner] at Hvalidated
  refine ⟨binding, ?_⟩
  exact H.motiveTelescopes.telescope owner hrecInfo A.semantics.context
    Hext binding A.semantics.target_translation A.semantics.target_type
    Hvalidated

/-- The permutation-free first-pass motive telescope is retained through the
complete mutual and constructor passes and transported to the final constant
environment.  Its only ambient binders are the common parameters, matching
the grouped prefix of `GeneratedRecursorTelescopeTranslation`. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalPairedMotiveSeed
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (_A : H.GeneratedRuleAlignment owner howner i hctor) :
    let parameterCtx :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls.toCtx
    ∃ S : RecursorMotiveTelescopeSeed H.recursorWF stats decl owner
        H.recInfos[owner]! H.elimLevel,
      VEnv.IsDefEqCtx H.recursorWF.venv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
        S.canonical.params.reverse parameterCtx := by
  dsimp only
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  exact H.motiveTelescopes.seed owner hrecInfo

/-- Final-environment form of the retained paired motive seed.  The concrete
source is exactly the production index/major telescope, while the two target
expressions remain linked by the independently proved first-pass
definitional equality. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalPairedMotiveTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterCtx :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls.toCtx
    ∃ S : RecursorMotiveTelescopeSeed H.recursorWF stats decl owner
        H.recInfos[owner]! H.elimLevel,
      VEnv.IsDefEqCtx H.outVEnv Us.length []
          S.canonical.params.reverse parameterCtx ∧
      TrExprS H.outVEnv Us H.recursorWF.mlctx.vlctx
        (H.localContext.lctx.mkForall H.recInfos[owner]!.indices
          (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
            (.sort H.elimLevel)))
        S.motiveActualType ∧
      H.outVEnv.IsDefEqU Us.length H.recursorWF.mlctx.vlctx.toCtx
        S.motiveActualType S.motiveType := by
  dsimp only
  rcases A.finalPairedMotiveSeed with ⟨S, hparams⟩
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv, R.declared.contextVEnv]
    exact H.installed.le
  exact ⟨S, hparams.mono hbase, S.motiveTypeTr.mono hbase,
    S.motiveTypeDefEq.mono hbase⟩

theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalMotiveTelescope
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (_A : H.GeneratedRuleAlignment owner howner i hctor) :
    let parameterCtx :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls.toCtx
    ∃ C : RecursorCanonicalMotiveTelescope H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams) stats
        decl owner H.recInfos[owner]! H.elimLevel,
      VEnv.IsDefEqCtx H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
        C.params.reverse parameterCtx := by
  dsimp only
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  rcases H.motiveTelescopes.seed owner hrecInfo with ⟨S, hparams⟩
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv, R.declared.contextVEnv]
    exact H.installed.le
  exact ⟨S.canonical.mono hbase, hparams.mono hbase⟩

/-- Owner-indexed form of `finalCanonicalMotiveTelescope`, independent of a
particular generated equation rule. -/
theorem RecursorPhasesResult.finalCanonicalMotiveTelescopeAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    let parameterCtx :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls.toCtx
    ∃ C : RecursorCanonicalMotiveTelescope H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams) stats
        decl owner H.recInfos[owner]! H.elimLevel,
      VEnv.IsDefEqCtx H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
        C.params.reverse parameterCtx := by
  dsimp only
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  rcases H.motiveTelescopes.seed owner hrecInfo with ⟨S, hparams⟩
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv, R.declared.contextVEnv]
    exact H.installed.le
  exact ⟨S.canonical.mono hbase, hparams.mono hbase⟩

/-- Compose two context conversions over the empty base.  The domain proof
of the second conversion is transported back across the already composed
prefix before transitivity is applied, so dependent domains remain in the
correct context. -/
theorem VEnv.IsDefEqCtx.transEmpty
    (henv : env.WF)
    (H₁ : VEnv.IsDefEqCtx env U [] Γ₁ Γ₂)
    (H₂ : VEnv.IsDefEqCtx env U [] Γ₂ Γ₃) :
    VEnv.IsDefEqCtx env U [] Γ₁ Γ₃ := by
  induction H₁ generalizing Γ₃ with
  | zero => exact H₂
  | @succ Γ₁ Γ₂ A₁ A₂ u H₁ hdom ih =>
    cases H₂ with
    | succ H₂ hdom₂ =>
      have Hprefix := ih H₂
      have hdom₂' := hdom₂.defeqDFC henv.ordered (H₁.symm henv.ordered)
      exact .succ Hprefix
        (hdom.trans_r henv H₁.isType hdom₂')

/-- Rebase a conversion between two dependent prefixes along a conversion
of their common suffix.  Both prefix contexts are known well formed from the
original conversion, so changing the suffix on each side is admissible even
when the two dependent prefixes use different representatives. -/
theorem VEnv.IsDefEqCtx.rebaseCommonSuffix
    (henv : env.WF)
    (Hsuffix : VEnv.IsDefEqCtx env U [] outer inner)
    (Hprefix : VEnv.IsDefEqCtx env U []
      (left ++ inner) (right ++ inner)) :
    VEnv.IsDefEqCtx env U []
      (left ++ outer) (right ++ outer) := by
  have HleftToOuter :=
    VEnv.IsDefEqCtx.extendSamePrefix
      (Hsuffix.symm henv.ordered) Hprefix.isType
  have HrightInner := (Hprefix.symm henv.ordered).isType
  have HrightToOuter :=
    VEnv.IsDefEqCtx.extendSamePrefix
      (Hsuffix.symm henv.ordered) HrightInner
  exact VEnv.IsDefEqCtx.transEmpty henv
    (HleftToOuter.symm henv.ordered) <|
      VEnv.IsDefEqCtx.transEmpty henv Hprefix HrightToOuter

/-- Cancel a common free-variable weakening from two dependent telescope
prefixes.  Closing the context conversion around a harmless sort exposes a
definitional equality of forall telescopes; inverse weakening then applies
to the whole telescope at once, avoiding binder-by-binder bookkeeping. -/
theorem VEnv.IsDefEqCtx.cancelLiftForallDomains
    (henv : env.WF)
    (W : Ctx.Lift' shift outer expanded)
    (Hprefix : VEnv.IsDefEqCtx env U []
      ((liftForallDomains left shift).reverse ++ expanded)
      ((liftForallDomains right shift).reverse ++ expanded)) :
    VEnv.IsDefEqCtx env U []
      (left.reverse ++ outer) (right.reverse ++ outer) := by
  have hexpanded : OnCtx expanded (env.IsType U) :=
    OnCtx.append_right Hprefix.isType
  have houter : OnCtx outer (env.IsType U) :=
    hexpanded.weak'_inv henv W
  have hlength : left.length = right.length := by
    have h := Hprefix.length_eq
    simp only [List.length_append, List.length_reverse,
      liftForallDomains_length] at h
    omega
  have Hsort : env.IsDefEq U
      ((liftForallDomains left shift).reverse ++ expanded)
      (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
    VEnv.HasType.sort (by trivial)
  rcases VEnv.IsDefEqCtx.closeHeads Hprefix
      (liftForallDomains left shift).length (by simp) Hsort with
    ⟨closedLevel, Hclosed⟩
  have HclosedU : env.IsDefEqU U expanded
      (VExpr.wrapForalls (liftForallDomains left shift) (.sort .zero))
      (VExpr.wrapForalls (liftForallDomains right shift) (.sort .zero)) := by
    refine ⟨.sort closedLevel, ?_⟩
    simpa [hlength] using Hclosed
  have Hweakened : env.IsDefEqU U expanded
      ((VExpr.wrapForalls left (.sort .zero)).lift' shift)
      ((VExpr.wrapForalls right (.sort .zero)).lift' shift) := by
    simpa [VExpr.lift'_wrapForalls_exact] using HclosedU
  have Hnarrow : env.IsDefEqU U outer
      (VExpr.wrapForalls left (.sort .zero))
      (VExpr.wrapForalls right (.sort .zero)) :=
    (VEnv.IsDefEqU.weak'_iff henv hexpanded W).1 Hweakened
  have Hbase : VEnv.IsDefEqCtx env U [] outer outer :=
    VEnv.IsDefEqCtx.refl houter
  exact VEnv.IsDefEqU.wrapForalls_context henv Hbase hlength Hnarrow


end VerifyInductive
end Lean4Lean
