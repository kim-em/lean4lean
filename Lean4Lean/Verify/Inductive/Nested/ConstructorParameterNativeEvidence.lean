import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterEvidence
import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterValidationRun
import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterValidationSoundness

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

private theorem NestedInstalledProduction.reindexForNativeParameters
    (P : NestedInstalledProduction loweredEnv)
    {c' : AddInductive.Context} {nparams' : Nat} {isUnsafe' : Bool}
    {initialEnv' : VEnv} {indTypes' : Array InductiveType}
    (hc : P.c = c') (hnparams : P.nparams = nparams')
    (hunsafe : P.isUnsafe = isUnsafe')
    (henv : P.initialEnv = initialEnv')
    (htypes : P.indTypes = indTypes') :
    ∃ Hheaders : DeclaredHeadersResult c' P.stats P.loweredDecl nparams'
        isUnsafe' P.depth initialEnv' indTypes' P.headerEnv,
      ∃ Hconstructors : ConstructorPhasesResult Hheaders P.ctorEnv,
        Nonempty (RecursorPhasesResult Hconstructors loweredEnv) := by
  subst c'
  subst nparams'
  subst isUnsafe'
  subst initialEnv'
  subst indTypes'
  exact ⟨P.headers, P.constructors, ⟨P.production⟩⟩

/-- Constructor parameter coherence derived from the exact lowering run and
the retained source-shaped validation pass.  The lowering-produced parameter
MLCtx is compared with the first restored family, then the already verified
block-wide cached parameter scope transports that result to every mutual
family.  No replay-locality or environment-restriction premise is used. -/
theorem NestedExactFinalRunResult.nativeRestoredConstructorParameterDomains
    (E : NestedExactFinalRunResult result sourceProdEnv sourceTypes sourceEnv
      decl lparams nparams isUnsafe
        (if isUnsafe then .unsafe else .safe) outEnv)
    (Hlower : NestedLoweringResultClosed E.productionContext.env fuel nparams
      sourceTypes
      { ({ lvls := lparams.map .param, newTypes := #[] } :
          Lean4Lean.ElimNestedInductive.State) with
        newTypes := sourceTypes.toArray } result) :
    NestedRestoredConstructorParameterDomains E.assembly := by
  let Hsource : TrInductDeclCore sourceEnv lparams nparams sourceTypes
      isUnsafe decl E.assembly.canonical.venvTypes
        E.assembly.canonical.venvCtors :=
    E.assembly.sourceSemantics.core E.assembly.typesSource E.assembly.uvars
      E.assembly.numParams E.assembly.unsafeEq E.assembly.typesAdded
      E.assembly.constructorsAdded
  have hsourceWF : sourceEnv.WF := by
    have hwf := E.production.headers.sourceContext.checking.tr.wf
    rw [E.production.headers.sourceContextVEnv] at hwf
    simpa only [E.production_initialEnv] using hwf
  have hcanonicalWF : E.assembly.canonical.venvCtors.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envCtorsWF Hsource hsourceWF
  have HlowerProduction : NestedLoweringResultClosed E.production.c.env fuel
      nparams sourceTypes
      { ({ lvls := lparams.map .param, newTypes := #[] } :
          Lean4Lean.ElimNestedInductive.State) with
        newTypes := sourceTypes.toArray } result := by
    simpa only [E.production_c] using Hlower
  have HproductionContext : ContextWF E.production.c := by
    simpa only [E.production_c] using E.productionContextWF
  have hisUnsafe : E.production.isUnsafe = isUnsafe := by
    rw [E.production_isUnsafe, E.productionContext_safety]
    cases isUnsafe <;> decide
  obtain ⟨Hheaders, Hconstructors, ⟨Hproduction⟩⟩ :=
    E.production.reindexForNativeParameters rfl E.production_nparams
      hisUnsafe E.production_initialEnv E.production_indTypes
  have hvisible : E.production.c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe) := by
    rw [E.production_c, E.productionContext_safety]
    cases isUnsafe <;> decide
  have hsourceValid : CheckingEnv.Valid
      (if isUnsafe then .unsafe else .safe) sourceProdEnv sourceEnv := by
    have Hvalid := E.production.headers.sourceContext.checking
    rw [E.production.headers.sourceContextVEnv] at Hvalid
    simpa only [E.production_c, E.productionContext_env,
      E.productionContext_safety, E.production_initialEnv] using Hvalid
  have hvalidationValid : CheckingEnv.Valid
      (if isUnsafe then .unsafe else .safe) E.validationEnv
      E.assembly.canonical.venvCtors := by
    apply E.validationEnvironment.valid hsourceValid
      E.assembly.sourceSemantics
    · intro indType stepSource stepTarget owner Hstep hmem Hheader
      rcases List.mem_iff_getElem.mp hmem with ⟨familyIdx, hfamily, heq⟩
      subst indType
      have Hheader' : TrSourceConst sourceEnv
          E.production.c.lparams sourceTypes[familyIdx].name
          sourceTypes[familyIdx].type owner.toVConstVal := by
        simpa only [E.production_c, E.productionContext_lparams] using Hheader
      have Htranslated := Hstep.restoredHeaderTranslationAtFresh HlowerProduction
        HproductionContext Hproduction rfl familyIdx hfamily
        Hheader' hvisible
      simpa only [E.production_initialEnv, E.production_c,
        E.productionContext_lparams, E.productionContext_safety] using
          Htranslated
    · exact E.assembly.canonical.typesAdded
    · simpa [VInductDecl.typeConstants, E.assembly.typesSource] using
        E.assembly.typeValues
    · exact E.assembly.canonical.ctorsAdded
    · simpa [VInductDecl.constructorConstants, E.assembly.typesSource] using
        E.assembly.constructorValues
  have Hfamilies : NestedRestoredFamilyParameterScopes E :=
    E.restoredFamilyParameterScopes Hlower rfl
  rcases Hlower with ⟨finalState, Hrun, Hcache, HparamsNodup⟩
  rcases Hrun.source with
    ⟨first, rest, sourceTail, paramsState, sourceLCtx, sourceParams,
      hsourceTypes, Hopening, _hnewTypes, _hnestedAux, _hnextIdx,
      _hprefix, _Hbinding, _Hselection, Hqueue⟩
  have hfirstSource : 0 < sourceTypes.length := by
    rw [hsourceTypes]
    simp
  have hfirstTarget : 0 < decl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource]
    exact hfirstSource
  have HfirstType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hsource
    0 hfirstSource hfirstTarget
  have HfirstTranslation : TrExprS E.assembly.canonical.venvCtors lparams []
      first.type decl.types[0].toVConstVal.type := by
    have Hfirst := HfirstType.header.type.mono
      ((VEnv.addConstVals_le E.assembly.typesAdded).trans
        (VEnv.addConstVals_le E.assembly.constructorsAdded))
    simpa [hsourceTypes] using Hfirst
  have HopeningResult : NestedParamOpening {} #[] first.type nparams
      result.lctx sourceTail result.params := by
    rcases Hqueue.resultContext with ⟨hlctx, hparams⟩
    rw [hlctx, hparams]
    exact Hopening
  have hresultLCtxWF : result.lctx.WF := Hrun.resultContextWF
  have hresultFresh : ∀ fv ∈ result.lctx.fvars,
      ({} : TypeChecker.State).ngen.Reserves fv :=
    Hrun.resultContextKernelFresh rfl
  rcases Hfamilies 0 hfirstTarget with ⟨HfirstFamily⟩
  intro familyIdx hfamily ctorIdx hctor
  have hsourceFamily : familyIdx < sourceTypes.length := by
    rw [Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource]
    exact hfamily
  have Htype := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hsource
    familyIdx hsourceFamily hfamily
  have hsourceCtor : ctorIdx < sourceTypes[familyIdx].ctors.length := by
    rw [Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Htype]
    exact hctor
  have HsourceCtor := Lean4Lean.VerifyInductive.TrInductiveType.ctorAt Htype
    ctorIdx hsourceCtor hctor
  have hsourceTypeMem : sourceTypes[familyIdx] ∈ sourceTypes :=
    List.getElem_mem hsourceFamily
  have hsourceCtorMem : sourceTypes[familyIdx].ctors[ctorIdx] ∈
      sourceTypes[familyIdx].ctors := List.getElem_mem hsourceCtor
  have hparameterRun :=
    validateRestoredConstructorParameters.loop_eq_ok_of_run
      E.parameterValidation hsourceTypeMem hsourceCtorMem
  have HconstructorTranslation : TrExprS
      E.assembly.canonical.venvCtors lparams []
      sourceTypes[familyIdx].ctors[ctorIdx].type
      decl.types[familyIdx].ctors[ctorIdx].toVConstant.type :=
    HsourceCtor.type.mono
      (VEnv.addConstVals_le E.assembly.constructorsAdded)
  have HprefixZero : CheckedConstructorParameterPrefix
      E.assembly.canonical.venvCtors lparams
      { E.production.stats with params := result.params }
      sourceTypes[familyIdx].ctors[ctorIdx].type 0
      sourceTypes[familyIdx].ctors[ctorIdx].type [] [] := .zero
  rcases HopeningResult.validateRestoredConstructorPrefix E.production.stats
      hvalidationValid hresultLCtxWF hresultFresh .nil rfl trivial nofun
      HfirstTranslation HconstructorTranslation HprefixZero hparameterRun with
    ⟨parameterMLCtx, constructorTail, constructorSourceDomains,
      nativeFamilyDomains, nativeFamilyTail, hparameterLCtx,
      hparameterWF, hnativeFamilyTarget, hnativeFamilyLength,
      hparameterContext, Hchecked⟩
  have hparameterContext' : parameterMLCtx.vlctx.toCtx =
      nativeFamilyDomains.reverse := by
    simpa [VLCtx.toCtx] using hparameterContext
  have hnativeScope : E.assembly.canonical.venvCtors.IsDefEqCtx
      lparams.length [] nativeFamilyDomains.reverse
      parameterMLCtx.vlctx.toCtx := by
    rw [← hparameterContext']
    exact .refl hparameterWF.tr.wf.toCtx
  have Hchecked' : CheckedConstructorParameterPrefix
      E.assembly.canonical.venvCtors lparams
      { E.production.stats with params := result.params }
      sourceTypes[familyIdx].ctors[ctorIdx].type decl.nparams constructorTail
      parameterMLCtx.vlctx constructorSourceDomains := by
    simpa only [Array.size_empty, Nat.zero_add, E.assembly.numParams] using
      Hchecked
  have HctorShape : decl.CtorParameterShape
      E.assembly.canonical.venvCtors nativeFamilyDomains
      decl.types[familyIdx].ctors[ctorIdx] := by
    apply Hchecked'.ctorParameterShape hcanonicalWF hparameterWF.tr.wf
      HconstructorTranslation E.assembly.uvars hnativeScope
  have HnativeFirst : E.assembly.canonical.venvCtors.IsDefEqU
      lparams.length []
      (VExpr.wrapForalls nativeFamilyDomains nativeFamilyTail)
      (VExpr.wrapForalls HfirstFamily.domains HfirstFamily.tail) := by
    rw [← hnativeFamilyTarget]
    exact HfirstFamily.target_defeq
  have HnativeFirstContext : E.assembly.canonical.venvCtors.IsDefEqCtx
      lparams.length [] nativeFamilyDomains.reverse
      HfirstFamily.domains.reverse := by
    have Hcontexts := VEnv.IsDefEqU.wrapForalls_context hcanonicalWF
      (VEnv.IsDefEqCtx.refl (by trivial))
      (hnativeFamilyLength.trans HfirstFamily.length.symm) HnativeFirst
    simpa using Hcontexts
  have HnativeCached : E.assembly.canonical.venvCtors.IsDefEqCtx
      lparams.length [] nativeFamilyDomains.reverse
      E.production.headers.materialized.parameterScope.toCtx :=
    VEnv.IsDefEqCtx.transEmpty hcanonicalWF HnativeFirstContext
      HfirstFamily.context
  rcases Hfamilies familyIdx hfamily with ⟨Hfamily⟩
  exact Hfamily.constructorDomains hcanonicalWF HctorShape E.assembly.uvars
    E.assembly.numParams HnativeCached

end VerifyInductive
end Lean4Lean
