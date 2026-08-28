import Lean4Lean.Verify.Inductive.Header.Existential
import Lean4Lean.Verify.Inductive.Header.LoopInd

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
namespace VerifyInductive
namespace checkInductiveTypes.loopType

/-- The executable per-header statistics update leaves the cached common
parameters untouched, so the semantic cache can be transported without any
new evidence. -/
def ParameterCachePrefix.reindexUpdatedStats
    (H : ParameterCachePrefix
      env Us scope stats done depth)
    (lctx : LocalContext) (resultLevel : Level) (first : Bool)
    (nindices : Nat) (indName : Name) :
    ParameterCachePrefix env Us scope
      (checkInductiveTypes.loopInd.updatedStats stats lctx resultLevel first
        nindices indName)
      done depth :=
  H.reindex (by
    cases first <;> simp [checkInductiveTypes.loopInd.updatedStats])

/-- Exact cached-context suffixes survive the same per-header statistics
update. -/
def ParameterContextSuffix.reindexUpdatedStats
    (H : ParameterContextSuffix Hc stats depth)
    (lctx : LocalContext) (resultLevel : Level) (first : Bool)
    (nindices : Nat) (indName : Name) :
    ParameterContextSuffix Hc
      (checkInductiveTypes.loopInd.updatedStats stats lctx resultLevel first
        nindices indName) depth :=
  H.reindex (by
    cases first <;> simp [checkInductiveTypes.loopInd.updatedStats])

end checkInductiveTypes.loopType

namespace checkInductiveTypes.loopInd

/-- Fold all noninitial mutual headers without a caller-provided abstract
declaration.  The fold retains the exact ordered raw source translations and
the executable common-parameter suffix while the runtime context grows by
the indices of successive headers. -/
theorem laterLoopInd
    {baseEnv : VEnv} {baseUs : List Name}
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {indTypes : Array InductiveType} {nparams dIdx depth : Nat}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {depth' : Nat},
      (Hc' : ContextWF c') →
      CheckedSourceHeaderAccumulator Hc'.venv c'.lparams indTypes.toList →
      stats'.indConsts.isEmpty = false →
      stats'.params.size = nparams →
      checkInductiveTypes.loopType.ParameterContextSuffix
        Hc' stats' depth' →
      (k stats' c').WF Q)
    (Hc : ContextWF c)
    (hvenv : Hc.venv = baseEnv)
    (hlparams : c.lparams = baseUs)
    (Htraversal : CheckedSourceHeaderTraversal
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
      simpa [hvenv, hlparams] using Htraversal.accumulator
    apply stepPrefix.accumulatesRawHeaders
      (nparams := nparams) (stats := stats) (k := k) (Q := Q)
      Hc Hprefix hidx
    intro checkedType Hchecked _Haccumulator normalized hbelow htype
    let payload : CheckedSourceHeaderPayload baseEnv baseUs indTypes[dIdx] := by
      rw [← hvenv, ← hlparams]
      exact Hchecked.payload Hc
    let Htraversal' := Htraversal.next hidx payload
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
        intro c' Hc' hvenv' hlparams' type' current' nindices hforall
          htype' Hsuffix'
        rcases htype' with ⟨current'', htype'', _hcurrentEq⟩
        apply laterResult.WF
          (nparams := nparams) (indTypes := indTypes) (dIdx := dIdx)
          (indName := indTypes[dIdx].name) (nindices := nindices)
          k Q Hc' hnonempty htype''
        intro resultSort _hguard _hsorted
        apply laterLoopInd k Q hconsume Hfinish Hc' hvenv' hlparams'
          Htraversal'
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
      Hc hvenv hlparams hnonempty Hsuffix hparams Hchecked.source hbelow htype
  · have hcoverage : indTypes.size ≤ dIdx := Nat.le_of_not_gt hidx
    have HheadersBase := Htraversal.complete hcoverage
    have Hheaders : CheckedSourceHeaderAccumulator
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

/-- Verify the distinguished first mutual header without assuming a target
skeleton.  Its telescope initializes the executable parameter cache and
exact cached-context suffix; the successful result-sort check then hands the
remaining array to `laterLoopInd`. -/
theorem firstLoopInd
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {indTypes : Array InductiveType} {nparams : Nat}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {depth' : Nat},
      (Hc' : ContextWF c') →
      CheckedSourceHeaderAccumulator Hc'.venv c'.lparams indTypes.toList →
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
  let Htraversal := CheckedSourceHeaderTraversal.empty
    Hc.venv c.lparams indTypes
  apply stepPrefix.accumulatesRawHeaders
    (nparams := nparams) (stats := stats) (k := k) (Q := Q)
    Hc Htraversal.accumulator hnonempty
  intro checkedType Hchecked _Haccumulator normalized _hbelow htype
  let payload := Hchecked.payload Hc
  let Htraversal' := Htraversal.next hnonempty payload
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
        hempty' hlevels' hnindices' hconsts' hforall hi htype'
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
      apply laterLoopInd k Q hconsume Hfinish Hc' hvenv' hlparams'
        Htraversal'
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

end checkInductiveTypes.loopInd

/-- Public skeleton-free verifier for the complete executable mutual-header
phase.  A successful nonempty traversal supplies the continuation with one
raw abstract constant translation for every source family, in source order,
plus the retained executable context invariants required by constructor
checking.  No constructor target or preselected inductive skeleton occurs in
the statement. -/
theorem checkInductiveTypes.accumulatesRawHeaders
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
      CheckedSourceHeaderAccumulator Hc'.venv c'.lparams indTypes.toList →
      stats'.indConsts.isEmpty = false →
      stats'.params.size = nparams →
      checkInductiveTypes.loopType.ParameterContextSuffix
        Hc' stats' depth →
      (k stats' c').WF Q) :
    (AddInductive.checkInductiveTypes nparams indTypes k c).WF Q := by
  change (AddInductive.checkInductiveTypes.loopInd nparams indTypes 0
    { (default : AddInductive.InductiveStats) with
      levels := c.lparams.map .param } k c).WF Q
  apply checkInductiveTypes.loopInd.firstLoopInd
    k Q hconsume Hfinish Hc hctx hnonempty
  · rfl
  · simp
  · rfl
  · rfl
  · rfl

end VerifyInductive
end Lean4Lean
