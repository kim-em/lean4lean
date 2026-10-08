import Lean4Lean.Verify.Inductive.Recursor.Binders.ParameterPrefixes

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

namespace checkConstructors.loopCtors

/-- Replay-retaining form of `refinesType`.  It follows the same executable
constructor loop while accumulating the exact checked common-parameter tail
beside the existing abstract shape/type prefix. -/
theorem refinesTypeWithReplay
    {decl : VInductDecl} {target : VInductiveType}
    {sourceEnv envTypes : VEnv} {params : List VExpr}
    {source : InductiveType}
    (Q : Unit → Prop)
    (Hc : ContextWF c)
    (Htarget : TrInductiveTypeHeaders sourceEnv envTypes c.lparams source target)
    (Hprefix : ConstructorTypePrefix envTypes decl params target ctorIdx)
    (Hreplay : ConstructorParamPrefixRow stats source.ctors ctorIdx)
    {tailScope : VLCtx}
    (Htails : ConstructorTailReplayRow Hc.venv c.lparams tailScope stats
      decl target source.ctors ctorIdx)
    (Hshape : ∀ i (hsource : i < source.ctors.length)
      (htarget : i < target.ctors.length),
      TrSourceConstRaw envTypes c.lparams source.ctors[i].name
        source.ctors[i].type target.ctors[i] →
      ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        source.ctors[i].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        source.ctors[i].name targetIdx source.ctors[i].type 0
        c.fuel.inductiveFuel c).WF fun _ => ∃ tail tailTarget,
          RecursorParamPrefix stats 0 source.ctors[i].type tail ∧
          ∃ sourceDomains,
          CheckedConstructorParameterPrefix Hc.venv c.lparams stats
            source.ctors[i].type stats.params.size tail tailScope
            sourceDomains ∧
          TrExprS Hc.venv c.lparams tailScope tail tailTarget ∧
          ConstructorTailCertificate Hc.venv decl target
            tailScope.toCtx 0 tailTarget ∧
          TrSourceConstRaw Hc.venv c.lparams source.ctors[i].name
            source.ctors[i].type target.ctors[i] ∧
          Nonempty
            (checkInductiveTypes.loopType.ScopedHeaderTelescope
              Hc.venv c.lparams
              (constructorTelescopeTarget target.ctors[i]) tailScope
              tailTarget stats.params.size 0) ∧
          decl.CtorShape envTypes params target target.ctors[i] ∧
          envTypes.IsType decl.uvars [] target.ctors[i].type ∧
          ∃ k, Expr.ForallSpine source.ctors[i].type k)
    (Hfinish : ConstructorTypePrefix envTypes decl params target
        target.ctors.length →
      ConstructorParamPrefixRow stats source.ctors source.ctors.length →
      ConstructorTailReplayRow Hc.venv c.lparams tailScope stats decl target
        source.ctors source.ctors.length →
      Q ()) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      source.ctors ctorIdx foundCtors c).WF Q := by
  by_cases hidx : ctorIdx < source.ctors.length
  · have htarget : ctorIdx < target.ctors.length := by
      rw [← Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctors_length Htarget]
      exact hidx
    have Hctor := Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctorAt
      Htarget ctorIdx hidx htarget
    apply stepPrefix.checkedWF (stats := stats) (isUnsafe := isUnsafe)
      (targetIdx := targetIdx) (Q := Q) Hc hidx
    intro checkedType type' checkedType' hchecked
    have Hchecked := Hshape ctorIdx hidx htarget Hctor checkedType type'
      checkedType' hchecked
    exact Hchecked.mono fun _ HcheckedCtor => by
      rcases HcheckedCtor with
        ⟨tail, tailTarget, Hparam, sourceDomains, Hcomparisons,
          Htranslated, Htail, HctorNarrow,
          Hsynthesis, HctorShape, HctorType, Hspine⟩
      have HtailReplay : CheckedConstructorTailReplayAt Hc.venv c.lparams
          tailScope stats decl target source.ctors[ctorIdx] :=
        ⟨target.ctors[ctorIdx], tail, tailTarget, sourceDomains,
          List.getElem_mem htarget, HctorNarrow, Hparam, Hcomparisons,
          Htranslated, Htail, Hsynthesis⟩
      exact refinesTypeWithReplay Q Hc Htarget
        (Hprefix.push htarget HctorShape HctorType)
        (Hreplay.push hidx Hparam Hspine) (Htails.push hidx HtailReplay)
        Hshape Hfinish
  · have heq : ctorIdx = source.ctors.length := by
      have := Hprefix.covered
      rw [← Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctors_length Htarget]
        at this
      omega
    apply result.WF (Q := Q) hidx
    have Hcomplete : ConstructorTypePrefix envTypes decl params target
        target.ctors.length := by
      simpa [heq,
        Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctors_length Htarget] using
          Hprefix
    have HreplayComplete : ConstructorParamPrefixRow stats source.ctors
        source.ctors.length := by simpa [heq] using Hreplay
    have HtailsComplete : ConstructorTailReplayRow Hc.venv c.lparams
        tailScope stats decl target source.ctors source.ctors.length := by
      simpa [heq] using Htails
    exact Hfinish Hcomplete HreplayComplete HtailsComplete
termination_by source.ctors.length - ctorIdx

end checkConstructors.loopCtors

namespace checkConstructors.loopTypes

/-- Mutual-family fold retaining every concrete constructor parameter replay. -/
theorem refinesBlockWithReplay
    {decl : VInductDecl} {sourceEnv envTypes : VEnv}
    {params : List VExpr}
    (Q : Unit → Prop)
    (Hc : ContextWF c)
    (Htypes : List.Forall₂
      (TrInductiveTypeHeaders sourceEnv envTypes c.lparams)
      indTypes.toList decl.types)
    (Hprefix : ConstructorTypesPrefix envTypes decl params targetIdx)
    (Hreplays : ConstructorParamPrefixRows stats indTypes targetIdx)
    {tailScope : VLCtx}
    (Htails : ConstructorTailReplayRows Hc.venv c.lparams tailScope stats
      decl indTypes targetIdx)
    (Hshape : ∀ targetIdx (hsource : targetIdx < indTypes.size)
      (htarget : targetIdx < decl.types.length)
      i (hctorSource : i < indTypes[targetIdx].ctors.length)
      (hctorTarget : i < decl.types[targetIdx].ctors.length),
      TrSourceConstRaw envTypes c.lparams indTypes[targetIdx].ctors[i].name
        indTypes[targetIdx].ctors[i].type decl.types[targetIdx].ctors[i] →
      ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        indTypes[targetIdx].ctors[i].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        indTypes[targetIdx].ctors[i].name targetIdx
        indTypes[targetIdx].ctors[i].type 0 c.fuel.inductiveFuel c).WF
        fun _ => ∃ tail tailTarget,
          RecursorParamPrefix stats 0 indTypes[targetIdx].ctors[i].type tail ∧
          ∃ sourceDomains,
          CheckedConstructorParameterPrefix Hc.venv c.lparams stats
            indTypes[targetIdx].ctors[i].type stats.params.size tail
            tailScope sourceDomains ∧
          TrExprS Hc.venv c.lparams tailScope tail tailTarget ∧
          ConstructorTailCertificate Hc.venv decl decl.types[targetIdx]
            tailScope.toCtx 0 tailTarget ∧
          TrSourceConstRaw Hc.venv c.lparams
            indTypes[targetIdx].ctors[i].name
            indTypes[targetIdx].ctors[i].type
            decl.types[targetIdx].ctors[i] ∧
          Nonempty
            (checkInductiveTypes.loopType.ScopedHeaderTelescope
              Hc.venv c.lparams
              (constructorTelescopeTarget
                decl.types[targetIdx].ctors[i]) tailScope tailTarget
              stats.params.size 0) ∧
          decl.CtorShape envTypes params decl.types[targetIdx]
            decl.types[targetIdx].ctors[i] ∧
          envTypes.IsType decl.uvars [] decl.types[targetIdx].ctors[i].type ∧
          ∃ k, Expr.ForallSpine indTypes[targetIdx].ctors[i].type k)
    (Hfinish : ConstructorTypesPrefix envTypes decl params
        decl.types.length →
      ConstructorParamPrefixRows stats indTypes indTypes.size →
      ConstructorTailReplayRows Hc.venv c.lparams tailScope stats decl
        indTypes indTypes.size →
      Q ()) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
      targetIdx c).WF Q := by
  by_cases hidx : targetIdx < indTypes.size
  · have htarget : targetIdx < decl.types.length := by
      have hlength : indTypes.size = decl.types.length := by
        simpa using List.Forall₂.length_eq Htypes
      omega
    have Htarget : TrInductiveTypeHeaders sourceEnv envTypes c.lparams
        indTypes[targetIdx] decl.types[targetIdx] := by
      have Htarget' := List.forall₂_getElem Htypes
        targetIdx (by simpa using hidx) htarget
      rw [Array.getElem_toList] at Htarget'
      exact Htarget'
    apply step.WF (Q := Q) hidx
    apply checkConstructors.loopCtors.refinesTypeWithReplay
      (Q := fun _ =>
        (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
          (targetIdx + 1) c).WF Q)
      Hc Htarget
      (ConstructorTypePrefix.empty envTypes decl params decl.types[targetIdx])
      (ConstructorParamPrefixRow.empty stats indTypes[targetIdx].ctors)
      (ConstructorTailReplayRow.empty Hc.venv c.lparams tailScope stats decl
        decl.types[targetIdx] indTypes[targetIdx].ctors)
    · intro i hsource htarget' Hctor checkedType type' checkedType' hchecked
      exact Hshape targetIdx hidx htarget i hsource htarget' Hctor
        checkedType type' checkedType' hchecked
    · intro Htype Hrow HtailRow
      exact refinesBlockWithReplay Q Hc Htypes
        (Hprefix.push htarget Htype) (Hreplays.push hidx Hrow)
        (Htails.push hidx HtailRow)
        Hshape Hfinish
  · have heq : targetIdx = indTypes.size := by
      have hlength : indTypes.size = decl.types.length := by
        simpa using List.Forall₂.length_eq Htypes
      have := Hprefix.covered
      omega
    apply result.WF (Q := Q) hidx
    apply Hfinish
    · have hlength : indTypes.size = decl.types.length := by
        simpa using List.Forall₂.length_eq Htypes
      simpa [heq, hlength] using Hprefix
    · simpa [heq] using Hreplays
    · simpa [heq] using Htails
termination_by indTypes.size - targetIdx

end checkConstructors.loopTypes

/-- Constructor-checking output needed by both declaration installation and
recursor replay.  The first component is the abstract formation certificate;
the second retains the exact concrete parameter tails for production
constructors. -/
structure CheckedConstructors
    (sourceEnv : VEnv) (decl : VInductDecl) (envTypes : VEnv)
    (params : List VExpr) (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (Us : List Name)
    (scope : VLCtx) : Prop where
  checked : CheckedConstructorCertificate sourceEnv decl envTypes params
  parameterPrefixes : CheckedRecursorParameterPrefixes stats indTypes
  constructorTails : CheckedRecursorConstructorTails envTypes Us scope stats
    decl indTypes

/-- Fold the end-to-end constructor theorem over the production's nested
family/constructor loops.  This is the constructor-formation result consumed
by `FormationCertificate`; environment installation is intentionally a
separate staging obligation. -/
theorem checkConstructors.loopTypes.refinesMaterialized
    {decl : VInductDecl} {sourceEnv : VEnv}
    {params : List VExpr}
    (Hc : ContextWF c)
    (Htypes : List.Forall₂
      (TrInductiveTypeHeaders sourceEnv Hc.venv c.lparams)
      indTypes.toList decl.types)
    (htypesAdded : sourceEnv.addConstVals decl.typeConstants = some Hc.venv)
    (Hmaterialized :
      checkInductiveTypes.loopInd.HeaderStatsWF
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hparams : Hmaterialized.headers.params = params)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length
      Hmaterialized.parameterScope Hc.chk.vlctx)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint
      Hc.venv stats.indConsts)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ targetIdx (hi : targetIdx < decl.types.length)
      fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      decl.types[targetIdx].resultLevel ≈ .zero ∨
        fieldLevel' ≤ decl.types[targetIdx].resultLevel)
    (hlparams : c.lparams.Nodup) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0 c).WF
      (fun _ => CheckedConstructors sourceEnv decl Hc.venv
        params stats indTypes c.lparams Hmaterialized.parameterScope) := by
  have hlevels := Hmaterialized.levelParamsTranslation hlparams
  let Hsuffix := Hmaterialized.parameterSuffix
  let Hstats :=
    checkPositivityStep.ValidAppStatsWF.ofMaterializedHeaderNarrow
      Hmaterialized
  have hparamsCtx : VEnv.IsDefEqCtx Hc.venv decl.uvars []
      params.reverse Hsuffix.parameterDecls.toCtx := by
    change VEnv.IsDefEqCtx Hc.venv decl.uvars []
      params.reverse Hmaterialized.parameterScope.toCtx
    subst params
    simpa [Hmaterialized.uvars] using Hmaterialized.paramsContext
  have hindTypesSize : indTypes.size = decl.types.length := by
    simpa using List.Forall₂.length_eq Htypes
  apply checkConstructors.loopTypes.refinesBlockWithReplay
    (Q := fun _ => CheckedConstructors sourceEnv decl Hc.venv
      params stats indTypes c.lparams Hmaterialized.parameterScope)
    Hc Htypes (ConstructorTypesPrefix.empty Hc.venv decl params)
    (ConstructorParamPrefixRows.empty stats indTypes)
    (ConstructorTailReplayRows.empty Hc.venv c.lparams
      Hmaterialized.parameterScope stats decl indTypes hindTypesSize)
  · intro targetIdx hsource htarget ctorIdx hctorSource hctorTarget
      Hctor checkedType fullType checkedType' hchecked
    have Htarget : TrInductiveTypeHeaders sourceEnv Hc.venv c.lparams
        indTypes[targetIdx] decl.types[targetIdx] := by
      have Htarget' := List.forall₂_getElem Htypes
        targetIdx (by simpa using hsource) htarget
      rw [Array.getElem_toList] at Htarget'
      exact Htarget'
    have htargetUvars : decl.types[targetIdx].uvars = decl.uvars := by
      exact Htarget.header.uvars.trans Hstats.uvars
    have htargetLookup : Hc.venv.constants decl.types[targetIdx].name =
        some decl.types[targetIdx].toVConstant := by
      apply VEnv.addConstVals_get htypesAdded
      exact List.mem_map.mpr
        ⟨decl.types[targetIdx], List.getElem_mem htarget, rfl⟩
    have htargetWF : decl.types[targetIdx].toVConstant.WF Hc.venv :=
      Htarget.header.wf.mono (VEnv.addConstVals_le htypesAdded)
    have htargetShape : decl.TypeShape Hc.venv params
        decl.types[targetIdx] := by
      rw [← hparams]
      exact Hmaterialized.headers.typeShapes _ (List.getElem_mem htarget)
    have Hchecked := checkConstructors.loopCtor.refinesCtorShape
      (fuel := c.fuel.inductiveFuel) Hc Hsuffix Hstats halign hparamsCtx
      Hctor hchecked htarget rfl htargetUvars htargetLookup htargetWF
      htargetShape hconsume hlit hunsafe (hbound targetIdx htarget) hlevels
    exact Hchecked.mono fun _ Hresult => by
      rcases Hresult with
        ⟨tail, tailTarget, Hprefix, sourceDomains, Hcomparisons,
          Htranslated, HtailCertificate,
          Hsynthesis, Hshape, Htype, Hspine⟩
      have Hcomparisons' : CheckedConstructorParameterPrefix Hc.venv
          c.lparams stats indTypes[targetIdx].ctors[ctorIdx].type
          stats.params.size tail Hmaterialized.parameterScope
          sourceDomains := by
        change CheckedConstructorParameterPrefix Hc.venv c.lparams stats
          indTypes[targetIdx].ctors[ctorIdx].type stats.params.size tail
          Hsuffix.parameterDecls sourceDomains
        simpa [Hstats.params_size] using Hcomparisons
      exact ⟨tail, tailTarget, Hprefix, sourceDomains, Hcomparisons',
        Htranslated, HtailCertificate, Hctor, Hsynthesis, Hshape, Htype,
        Hspine⟩
  · intro Hcomplete Hreplays Htails
    exact {
      checked := Hcomplete.checkedComplete (env := sourceEnv)
      parameterPrefixes := Hreplays.complete
      constructorTails := Htails.complete }

end VerifyInductive
end Lean4Lean
