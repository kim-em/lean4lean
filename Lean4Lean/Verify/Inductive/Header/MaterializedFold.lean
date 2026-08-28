import Lean4Lean.Verify.Inductive.Header.RawMaterialization

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
namespace VerifyInductive
namespace checkInductiveTypes.loopInd

/-- Fold the noninitial mutual headers while retaining full, rather than raw,
source translations.  Forall-headed headers are upgraded before recursion;
the terminal non-forall branch is upgraded by the successful `ensureSort`.
Thus no abstract header target is supplied by the caller. -/
theorem laterLoopIndChecked
    {baseEnv : VEnv} {baseUs : List Name}
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {indTypes : Array InductiveType} {nparams dIdx depth : Nat}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {depth' : Nat},
      (Hc' : ContextWF c') →
      MaterializedSourceHeaderAccumulator Hc'.venv c'.lparams
        indTypes.toList →
      stats'.indConsts.isEmpty = false →
      stats'.params.size = nparams →
      checkInductiveTypes.loopType.ParameterContextSuffix
        Hc' stats' depth' →
      (k stats' c').WF Q)
    (Hc : ContextWF c)
    (hvenv : Hc.venv = baseEnv)
    (hlparams : c.lparams = baseUs)
    (Htraversal : MaterializedSourceHeaderTraversal
      baseEnv baseUs indTypes dIdx)
    (hdone : dIdx ≤ indTypes.size)
    (hlevels : stats.levels.length = baseUs.length)
    (hindices : stats.nindices.size = dIdx)
    (hconsts : stats.indConsts.size = dIdx)
    (hnonempty : stats.indConsts.isEmpty = false)
    (hparams : stats.params.size = nparams)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth) :
    (AddInductive.checkInductiveTypes.loopInd nparams indTypes dIdx
      stats k c).WF Q := by
  by_cases hidx : dIdx < indTypes.size
  · have Hprefix : CheckedSourceHeaderAccumulator Hc.venv c.lparams
        (indTypes.toList.take dIdx) := by
      simpa [hvenv, hlparams] using Htraversal.raw.accumulator
    apply stepPrefix.accumulatesRawHeaders
      (nparams := nparams) (stats := stats) (k := k) (Q := Q)
      Hc Hprefix hidx
    intro checkedType Hchecked _Hraw normalized hbelow htype
    by_cases hforall : ∃ name dom body bi,
        normalized = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      have hnormalizedNoFVars : FVarsIn (fun _ => False)
          (.forallE name dom body bi) := by
        have hsourceNoFVars : FVarsIn (fun _ => False)
            indTypes[dIdx].type :=
          Hchecked.source.type.fvarsIn.mono fun fv hfv => by
            simpa [VLCtx.fvars] using hfv
        have hfalseUpSet : IsFVarUpSet (fun _ => False)
            Hc.mlctx.vlctx := by
          have hsuffix := IsFVarUpSet.suffixFVars ([] : VLCtx)
            Hc.mlctx.vlctx (by simpa using Hc.mlctx_wf.tr.wf)
          simpa [VLCtx.fvars] using hsuffix
        exact hbelow _ hfalseUpSet hsourceNoFVars
      have Htarget :=
        CheckedSourceHeaderTranslation.checkedLaterForall
          Hchecked htype hnormalizedNoFVars
      let Htraversal' : MaterializedSourceHeaderTraversal
          baseEnv baseUs indTypes (dIdx + 1) := by
        apply Htraversal.next hidx Hchecked.target
        simpa [hvenv, hlparams] using Htarget
      apply checkInductiveTypes.loopType.laterHeader.accumulateContextWF
        hconsume (baseEnv := baseEnv) (baseUs := baseUs)
        (depth := depth)
        (k := fun type stats nindices => show AddInductive.M α from do
          let type ← TypeChecker.ensureSort type
          let mut stats := stats
          let resultLevel := type.sortLevel!
          if stats.indConsts.isEmpty then
            let lctx := (← read).lctx
            stats := { stats with
              lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
          else if !resultLevel.isEquiv stats.resultLevel then
            throw <| .other
              "mutually inductive types must live in the same universe"
          stats := { stats with
            nindices := stats.nindices.push nindices
            indConsts := stats.indConsts.push
              (.const indTypes[dIdx].name stats.levels) }
          AddInductive.checkInductiveTypes.loopInd nparams indTypes
            (dIdx + 1) stats k)
        (Q := Q)
        (Hresult := by
          intro c' Hc' hvenv' hlparams' type' current' nindices hnotforall
            htype' Hsuffix'
          rcases htype' with ⟨current'', htype'', _hcurrentEq⟩
          apply laterResult.WF
            (nparams := nparams) (indTypes := indTypes) (dIdx := dIdx)
            (indName := indTypes[dIdx].name) (nindices := nindices)
            k Q Hc' hnonempty htype''
          intro resultSort _hguard _hsorted
          apply laterLoopIndChecked k Q hconsume Hfinish Hc'
            hvenv' hlparams' Htraversal'
            (dIdx := dIdx + 1) (depth := depth + nindices)
            (stats := updatedStats stats stats.lctx resultSort false nindices
              indTypes[dIdx].name)
          · omega
          · simpa [updatedStats] using hlevels
          · simp [updatedStats, hindices]
          · simp [updatedStats, hconsts]
          · simp [updatedStats]
          · simpa [updatedStats] using hparams
          · exact Hsuffix'.reindexUpdatedStats stats.lctx resultSort false
              nindices indTypes[dIdx].name)
        Hc hvenv hlparams hnonempty Hsuffix hparams Hchecked.source
        hbelow htype
    · cases hfuel : c.fuel.inductiveFuel with
      | zero => exact checkInductiveTypes.loopType.zero.WF
      | succ fuel =>
        by_cases hzero : 0 = nparams
        · apply checkInductiveTypes.loopType.result.WF
            (Q := Q) hforall hzero
          rcases htype with ⟨current', htype', hcurrentEq⟩
          apply laterResult.WF
            (nparams := nparams) (indTypes := indTypes) (dIdx := dIdx)
            (indName := indTypes[dIdx].name) (nindices := 0)
            k Q Hc hnonempty htype'
          intro resultSort _hguard hsorted
          have hsorted' := TrExpr.defeq Hc.checking.tr.wf
            Hc.mlctx_wf.tr.wf.toCtx hsorted hcurrentEq
          rcases CheckedSourceHeaderTranslation.checkedTerminal
              Hchecked hsorted' with
            ⟨_resultLevel, _hofLevel, Htarget⟩
          let Htraversal' : MaterializedSourceHeaderTraversal
              baseEnv baseUs indTypes (dIdx + 1) := by
            apply Htraversal.next hidx Hchecked.target
            simpa [hvenv, hlparams] using Htarget
          apply laterLoopIndChecked k Q hconsume Hfinish Hc hvenv hlparams
            Htraversal'
            (dIdx := dIdx + 1) (depth := depth)
            (stats := updatedStats stats stats.lctx resultSort false 0
              indTypes[dIdx].name)
          · omega
          · simpa [updatedStats] using hlevels
          · simp [updatedStats, hindices]
          · simp [updatedStats, hconsts]
          · simp [updatedStats]
          · simpa [hzero, updatedStats] using hparams
          · exact Hsuffix.reindexUpdatedStats stats.lctx resultSort false 0
              indTypes[dIdx].name
        · exact checkInductiveTypes.loopType.parameterMismatch.WF
            (Q := Q) hforall hzero
  · have hcoverage : indTypes.size ≤ dIdx := Nat.le_of_not_gt hidx
    have HheadersBase := Htraversal.complete hcoverage
    have Hheaders : MaterializedSourceHeaderAccumulator
        Hc.venv c.lparams indTypes.toList := by
      simpa [hvenv, hlparams] using HheadersBase
    apply result.WF (k := k) (Q := Q) hidx
    · simpa [hlparams] using hlevels
    · have : dIdx = indTypes.size := by omega
      simpa [this] using hindices
    · have : dIdx = indTypes.size := by omega
      simpa [this] using hconsts
    · exact hparams
    · exact Hfinish Hc Hheaders hnonempty hparams Hsuffix
termination_by indTypes.size - dIdx

/-- Initialize full existential header accumulation from the distinguished
first family.  This is the checked-target analogue of `firstLoopInd`; its
continuation receives exactly the complete ordered source block. -/
theorem firstLoopIndChecked
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {indTypes : Array InductiveType} {nparams : Nat}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {depth' : Nat},
      (Hc' : ContextWF c') →
      MaterializedSourceHeaderAccumulator Hc'.venv c'.lparams
        indTypes.toList →
      stats'.indConsts.isEmpty = false →
      stats'.params.size = nparams →
      checkInductiveTypes.loopType.ParameterContextSuffix
        Hc' stats' depth' →
      (k stats' c').WF Q)
    (Hc : ContextWF c)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < indTypes.size)
    (hempty : stats.indConsts.isEmpty = true)
    (hlevels : stats.levels.length = c.lparams.length)
    (hnindices : stats.nindices = #[])
    (hconsts : stats.indConsts = #[])
    (hparams : stats.params = #[]) :
    (AddInductive.checkInductiveTypes.loopInd nparams indTypes 0
      stats k c).WF Q := by
  let Htraversal := MaterializedSourceHeaderTraversal.empty
    Hc.venv c.lparams indTypes
  apply stepPrefix.accumulatesRawHeaders
    (nparams := nparams) (stats := stats) (k := k) (Q := Q)
    Hc Htraversal.raw.accumulator hnonempty
  intro checkedType Hchecked _Hraw normalized hbelow htype
  by_cases hforall : ∃ name dom body bi,
      normalized = .forallE name dom body bi
  · rcases hforall with ⟨name, dom, body, bi, rfl⟩
    have Htarget := CheckedSourceHeaderTranslation.checkedFirstForall
      Hchecked hctx htype
    let Htraversal' : MaterializedSourceHeaderTraversal
        Hc.venv c.lparams indTypes 1 :=
      Htraversal.next hnonempty Hchecked.target Htarget
    have Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
        Hc.venv c.lparams Hc.mlctx.vlctx stats 0 0 :=
      checkInductiveTypes.loopType.ParameterCachePrefix.empty hparams
    let Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
        Hc stats 0 :=
      checkInductiveTypes.loopType.ParameterContextSuffix.empty Hc hctx hparams
    apply checkInductiveTypes.loopType.firstHeader.accumulateContextWF
      (baseEnv := Hc.venv) (baseUs := c.lparams)
      (baseLevels := stats.levels) (baseNindices := stats.nindices)
      (baseConsts := stats.indConsts)
      (k := fun type stats nindices => show AddInductive.M α from do
        let type ← TypeChecker.ensureSort type
        let mut stats := stats
        let resultLevel := type.sortLevel!
        if stats.indConsts.isEmpty then
          let lctx := (← read).lctx
          stats := { stats with
            lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
        else if !resultLevel.isEquiv stats.resultLevel then
          throw <| .other
            "mutually inductive types must live in the same universe"
        stats := { stats with
          nindices := stats.nindices.push nindices
          indConsts := stats.indConsts.push
            (.const indTypes[0].name stats.levels) }
        AddInductive.checkInductiveTypes.loopInd nparams indTypes 1 stats k)
      (Q := Q) hconsume
      (Hresult := by
        intro c' Hc' hvenv' hlparams' stats' type' current' i' nindices
          hempty' hlevels' hnindices' hconsts' hnotforall hi htype'
          Hcache' Hsuffix'
        rcases htype' with ⟨current'', htype'', _hcurrentEq⟩
        subst i'
        apply firstResult.WF
          (nparams := nparams) (indTypes := indTypes) (dIdx := 0)
          (indName := indTypes[0].name) (nindices := nindices)
          k Q Hc' hempty' htype''
        intro resultSort _hsorted
        have hparamSize : stats'.params.size = nparams := by
          have hlength :=
            Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hcache'.params
          simpa using hlength
        apply laterLoopIndChecked k Q hconsume Hfinish Hc'
          hvenv' hlparams' Htraversal'
          (dIdx := 1) (depth := nindices)
          (stats := updatedStats stats' c'.lctx resultSort true nindices
            indTypes[0].name)
        · omega
        · simpa [updatedStats, hlevels', hlparams'] using hlevels
        · simp [updatedStats, hnindices', hnindices]
        · simp [updatedStats, hconsts', hconsts]
        · simp [updatedStats]
        · simpa [updatedStats] using hparamSize
        · exact Hsuffix'.reindexUpdatedStats c'.lctx resultSort true
            nindices indTypes[0].name)
      Hc rfl rfl hempty rfl rfl rfl Hcache Hsuffix
      (by
        intro _
        exact ⟨rfl, by
          dsimp [Hsuffix,
            checkInductiveTypes.loopType.ParameterContextSuffix.empty]⟩)
      htype
  · cases hfuel : c.fuel.inductiveFuel with
    | zero => exact checkInductiveTypes.loopType.zero.WF
    | succ fuel =>
      by_cases hzero : 0 = nparams
      · apply checkInductiveTypes.loopType.result.WF
          (Q := Q) hforall hzero
        rcases htype with ⟨current', htype', hcurrentEq⟩
        apply firstResult.WF
          (nparams := nparams) (indTypes := indTypes) (dIdx := 0)
          (indName := indTypes[0].name) (nindices := 0)
          k Q Hc hempty htype'
        intro resultSort hsorted
        have hsorted' := TrExpr.defeq Hc.checking.tr.wf
          Hc.mlctx_wf.tr.wf.toCtx hsorted hcurrentEq
        rcases CheckedSourceHeaderTranslation.checkedTerminal
            Hchecked hsorted' with
          ⟨_resultLevel, _hofLevel, Htarget⟩
        let Htraversal' : MaterializedSourceHeaderTraversal
            Hc.venv c.lparams indTypes 1 :=
          Htraversal.next hnonempty Hchecked.target Htarget
        let Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
            Hc stats 0 :=
          checkInductiveTypes.loopType.ParameterContextSuffix.empty
            Hc hctx hparams
        apply laterLoopIndChecked k Q hconsume Hfinish Hc rfl rfl
          Htraversal'
          (dIdx := 1) (depth := 0)
          (stats := updatedStats stats c.lctx resultSort true 0
            indTypes[0].name)
        · omega
        · simpa [updatedStats] using hlevels
        · simp [updatedStats, hnindices]
        · simp [updatedStats, hconsts]
        · simp [updatedStats]
        · simp [hzero, updatedStats, hparams]
        · exact Hsuffix.reindexUpdatedStats c.lctx resultSort true 0
            indTypes[0].name
      · exact checkInductiveTypes.loopType.parameterMismatch.WF
          (Q := Q) hforall hzero

/-- Public skeleton-free verifier returning one fully formed abstract header
constant for every source family, in exact source order. -/
theorem checkInductiveTypes.accumulatesCheckedHeaders
    {c : AddInductive.Context} {indTypes : Array InductiveType}
    {nparams : Nat} {α : Type}
    (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < indTypes.size)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {depth : Nat},
      (Hc' : ContextWF c') →
      MaterializedSourceHeaderAccumulator Hc'.venv c'.lparams
        indTypes.toList →
      stats'.indConsts.isEmpty = false →
      stats'.params.size = nparams →
      checkInductiveTypes.loopType.ParameterContextSuffix
        Hc' stats' depth →
      (k stats' c').WF Q) :
    (AddInductive.checkInductiveTypes nparams indTypes k c).WF Q := by
  change (AddInductive.checkInductiveTypes.loopInd nparams indTypes 0
    { (default : AddInductive.InductiveStats) with
      levels := c.lparams.map .param } k c).WF Q
  apply firstLoopIndChecked k Q hconsume Hfinish Hc hctx hnonempty
  · rfl
  · simp
  · rfl
  · rfl
  · rfl

end checkInductiveTypes.loopInd
end VerifyInductive
end Lean4Lean
