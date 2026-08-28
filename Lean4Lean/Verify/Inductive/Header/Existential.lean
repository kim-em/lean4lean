import Lean4Lean.Verify.Inductive.Header.LoopType

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The abstract payload obtained directly from one successful closed header
check.  Its type translation is exact, but it deliberately does not claim
`VConstVal.WF`: header formation is established only after the executable
telescope traversal has checked the parameter/index telescope and result
sort. -/
structure CheckedSourceHeaderTranslation
    (Hc : ContextWF c) (name : Name) (type checkedType : Expr) where
  target : VConstVal
  runtimeTarget : VExpr
  checkedTarget : VExpr
  typing : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
    type checkedType runtimeTarget checkedTarget
  source : TrSourceConstRaw Hc.venv c.lparams name type target

/-- The declaration-facing part of a checked source header.  Unlike
`CheckedSourceHeaderTranslation`, this payload no longer mentions the
executable result of `checkClosedType`, so payloads from successive mutual
headers can be retained in one ordered accumulator even though those checks
run in different local contexts. -/
structure CheckedSourceHeaderPayload (env : VEnv) (Us : List Name)
    (source : InductiveType) where
  target : VConstVal
  translation : TrSourceConstRaw env Us source.name source.type target

/-- Ordered abstract payloads recovered from a prefix of the executable
mutual-header traversal.  This is intentionally earlier than a
`VInductDeclSkeleton`: constructors have not been translated yet, and the
header telescope traversal has not yet supplied semantic arities. -/
structure CheckedSourceHeaderAccumulator (env : VEnv) (Us : List Name)
    (sources : List InductiveType) where
  targets : List VConstVal
  translations : List.Forall₂
    (fun source target =>
      TrSourceConstRaw env Us source.name source.type target)
    sources targets

namespace CheckedSourceHeaderAccumulator

/-- The empty executable header prefix has an empty abstract payload. -/
def empty (env : VEnv) (Us : List Name) :
    CheckedSourceHeaderAccumulator env Us [] where
  targets := []
  translations := .nil

/-- Retain one newly checked source header at the end of the ordered prefix. -/
def snoc (H : CheckedSourceHeaderAccumulator env Us sources)
    (source : InductiveType) (payload : CheckedSourceHeaderPayload env Us source) :
    CheckedSourceHeaderAccumulator env Us (sources ++ [source]) where
  targets := H.targets ++ [payload.target]
  translations := Lean4Lean.VerifyInductive.List.Forall₂.append'
    H.translations (.cons payload.translation .nil)

@[simp] theorem empty_targets : (empty env Us).targets = [] := rfl

@[simp] theorem snoc_targets
    (H : CheckedSourceHeaderAccumulator env Us sources)
    (payload : CheckedSourceHeaderPayload env Us source) :
    (H.snoc source payload).targets = H.targets ++ [payload.target] := rfl

end CheckedSourceHeaderAccumulator

/-- Exact loop-indexed view of the accumulated mutual-header payloads. -/
structure CheckedSourceHeaderTraversal (env : VEnv) (Us : List Name)
    (indTypes : Array InductiveType) (dIdx : Nat) where
  accumulator : CheckedSourceHeaderAccumulator env Us
    (indTypes.toList.take dIdx)

namespace CheckedSourceHeaderTraversal

def empty (env : VEnv) (Us : List Name) (indTypes : Array InductiveType) :
    CheckedSourceHeaderTraversal env Us indTypes 0 where
  accumulator := CheckedSourceHeaderAccumulator.empty env Us

/-- Advancing `loopInd` by one extends exactly the source prefix selected by
the next executable array index. -/
def next (H : CheckedSourceHeaderTraversal env Us indTypes dIdx)
    (hidx : dIdx < indTypes.size)
    (payload : CheckedSourceHeaderPayload env Us indTypes[dIdx]) :
    CheckedSourceHeaderTraversal env Us indTypes (dIdx + 1) where
  accumulator := by
    rw [List.take_succ_eq_append_getElem (by simpa using hidx)]
    exact H.accumulator.snoc indTypes[dIdx] payload

/-- At loop termination, exact prefix coverage is coverage of the entire
mutual source block. -/
def complete (H : CheckedSourceHeaderTraversal env Us indTypes dIdx)
    (hdone : indTypes.size ≤ dIdx) :
    CheckedSourceHeaderAccumulator env Us indTypes.toList := by
  have htake : indTypes.toList.take dIdx = indTypes.toList :=
    List.take_of_length_le (by simpa using hdone)
  rw [← htake]
  exact H.accumulator

end CheckedSourceHeaderTraversal

namespace CheckedSourceHeaderTranslation

/-- Forget the context-sensitive checked-type evidence after the executable
telescope traversal has consumed it. -/
def payload
    {c : AddInductive.Context} {source : InductiveType} {checkedType : Expr}
    (Hc : ContextWF c)
    (H : CheckedSourceHeaderTranslation Hc source.name source.type checkedType) :
    CheckedSourceHeaderPayload Hc.venv c.lparams source where
  target := H.target
  translation := H.source

end CheckedSourceHeaderTranslation

/-- A successful `checkClosedType` constructs its abstract header payload;
no caller-selected declaration skeleton is needed at this boundary.  This is
the existential seed used to split header materialization from later
constructor translation. -/
theorem checkClosedType.rawSourceTranslationWF (Hc : ContextWF c) :
    (AddInductive.checkClosedType name type c).WF fun checkedType =>
      Nonempty (CheckedSourceHeaderTranslation Hc name type checkedType) := by
  change (c.env.checkNoMVarNoFVar name type >>= fun _ =>
    (monadLift (TypeChecker.checkType type) : AddInductive.M Expr) c).WF _
  have Hclosed : (c.env.checkNoMVarNoFVar name type).WF
      (fun _ => type.FVarsIn fun _ => False) := by
    intro _ Hresult
    exact checkNoMVarNoFVar.closed Hresult
  exact Hclosed.bind fun _ hclosed =>
    (checkTypeInContext.WF Hc
      (hclosed.mono fun _ h => False.elim h)).mono
      fun checkedType Hchecked => by
    rcases Hchecked with ⟨runtimeTarget, checkedTarget, Htyping⟩
    have hsourceClosed : Closed type 0 := by
      simpa [Hc.mlctx.noBV] using Htyping.2.1.closed
    have hsourceFVars :
        type.FVarsIn (fun fv => fv ∈ VLCtx.fvars ([] : VLCtx)) := by
      simpa [VLCtx.fvars] using hclosed
    rcases Htyping.2.1.weakFV'_inv Hc.checking.tr.wf
        (VLCtx.FVLift'.from_nil Hc.mlctx.noBV)
        (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
        hsourceClosed hsourceFVars with ⟨typeTarget, HtypeTarget⟩
    let target : VConstVal := {
      uvars := c.lparams.length
      name := name
      type := typeTarget }
    exact ⟨{
      target := target
      runtimeTarget := runtimeTarget
      checkedTarget := checkedTarget
      typing := Htyping
      source := {
        uvars := rfl
        name := rfl
        type := HtypeTarget } }⟩

namespace checkInductiveTypes.loopInd

/-- One executable mutual-header iteration extends an independently built,
ordered abstract-header accumulator.  The continuation also receives the
full context-sensitive typing evidence needed by `loopType`; only the stored
accumulator forgets that evidence.  No constructor translation or
caller-selected declaration skeleton is assumed at this boundary. -/
theorem stepPrefix.accumulatesRawHeaders
    {sources : List InductiveType}
    {c : AddInductive.Context} {nparams dIdx : Nat}
    {indTypes : Array InductiveType}
    {stats : AddInductive.InductiveStats}
    {k : AddInductive.InductiveStats → AddInductive.M α}
    {Q : α → Prop}
    (Hc : ContextWF c)
    (Hprefix : CheckedSourceHeaderAccumulator Hc.venv c.lparams sources)
    (hidx : dIdx < indTypes.size)
    (Hloop : ∀ checkedType,
      (Hchecked : CheckedSourceHeaderTranslation Hc indTypes[dIdx].name
        indTypes[dIdx].type checkedType) →
      CheckedSourceHeaderAccumulator Hc.venv c.lparams
        (sources ++ [indTypes[dIdx]]) →
      ∀ normalized,
        FVarsBelow Hc.mlctx.vlctx indTypes[dIdx].type normalized →
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
          normalized Hchecked.runtimeTarget →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized 0 0
          c.fuel.inductiveFuel (fun type stats nindices => show AddInductive.M _ from do
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
              (dIdx + 1) stats k) c).WF Q) :
    (AddInductive.checkInductiveTypes.loopInd nparams indTypes dIdx stats k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopInd]
  rw [dif_pos hidx]
  change (AddInductive.checkClosedType indTypes[dIdx].name indTypes[dIdx].type c >>=
    fun _ => ((do
      let normalized ← TypeChecker.whnf indTypes[dIdx].type
      AddInductive.checkInductiveTypes.loopType nparams stats normalized 0 0
        c.fuel.inductiveFuel (fun type stats nindices => show AddInductive.M _ from do
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
            (dIdx + 1) stats k)) : AddInductive.M _) c).WF Q
  exact (checkClosedType.rawSourceTranslationWF Hc).bind
    fun checkedType hchecked => by
      rcases hchecked with ⟨Hchecked⟩
      exact (whnfInContext.scopeWF Hc Hchecked.typing.2.1).bind
        fun normalized hnormalized =>
          Hloop checkedType Hchecked
            (Hprefix.snoc indTypes[dIdx] (Hchecked.payload Hc))
            normalized hnormalized.1 hnormalized.2

end checkInductiveTypes.loopInd

namespace checkInductiveTypes.loopType

/-- Skeleton-free traversal of the first mutual header.  Common parameters
are installed into the executable context and retained in both cache
invariants; subsequent index binders enlarge their ambient prefix. -/
theorem firstHeader.accumulateContextWF
    {baseEnv : VEnv} {baseUs : List Name} {c : AddInductive.Context}
    {baseLevels : List Level} {baseNindices : Array Nat}
    {baseConsts : Array Expr}
    {stats : AddInductive.InductiveStats}
    {k : Expr → AddInductive.InductiveStats → Nat → AddInductive.M α}
    {Q : α → Prop}
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hresult : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      (_hvenv : Hc'.venv = baseEnv)
      (_hlparams : c'.lparams = baseUs)
      {stats' : AddInductive.InductiveStats}
      {type' current' i' nindices'},
      stats'.indConsts.isEmpty = true →
      stats'.levels = baseLevels →
      stats'.nindices = baseNindices →
      stats'.indConsts = baseConsts →
      (¬ ∃ name dom body bi, type' = .forallE name dom body bi) →
      i' = nparams →
      TrExpr Hc'.venv c'.lparams Hc'.mlctx.vlctx type' current' →
      ParameterCachePrefix Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats' i' nindices' →
      ParameterContextSuffix Hc' stats' nindices' →
      (k type' stats' nindices' c').WF Q)
    (Hc : ContextWF c) (hvenv : Hc.venv = baseEnv)
    (hlparams : c.lparams = baseUs)
    (hempty : stats.indConsts.isEmpty = true)
    (hlevelsStable : stats.levels = baseLevels)
    (hnindicesStable : stats.nindices = baseNindices)
    (hconstsStable : stats.indConsts = baseConsts)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats i nindices)
    (Hsuffix : ParameterContextSuffix Hc stats nindices)
    (hphase : i < nparams →
      nindices = 0 ∧ Hsuffix.ambientDecls = [])
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type current) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i
      nindices fuel k c).WF Q := by
  induction fuel generalizing c stats type current i nindices with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi,
        type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      rcases TrExpr.forallE_source htype with
        ⟨sourceDom, sourceBody, hdom, hbody,
          hdomType, _hbodyType, _hcurrent⟩
      rcases hconsume c Hc hdom hdomType with ⟨consumedDom, Hdom⟩
      by_cases hi : i < nparams
      · rcases hphase hi with ⟨rfl, hambient⟩
        apply firstParameter.cacheWF
          (stats := stats) (nparams := nparams) (i := i)
          (nindices := 0) (fuel := fuel) (k := k) (Q := Q)
          Hc hi hempty Hcache Hdom hbody
        intro body' _hbodyEq normalized hnormalized Hcache'
        let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType
        apply ih (c := { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotationsVerified bi })
          (stats := { stats with
            params := stats.params.push (.fvar ⟨c.ngen.curr⟩) })
          (current := body') (i := i + 1) (nindices := 0)
          (Hc := Hc')
          (Hsuffix := Hsuffix.push Hc hambient
            Hdom.consumed Hdom.isType)
        · change Hc.venv = baseEnv
          exact hvenv
        · change c.lparams = baseUs
          exact hlparams
        · simpa using hempty
        · simpa using hlevelsStable
        · simpa using hnindicesStable
        · simpa using hconstsStable
        · exact Hcache'
        · intro _
          exact ⟨rfl, rfl⟩
        · simpa [Hc'] using hnormalized
      · apply index.cacheWF
          (stats := stats) (nparams := nparams) (i := i)
          (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
          Hc hi Hcache Hdom hbody
        intro body' _hbodyEq normalized hnormalized Hcache'
        let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType
        apply ih (c := { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotationsVerified bi })
          (current := body') (i := i) (nindices := nindices + 1)
          (Hc := Hc')
          (Hsuffix := Hsuffix.withIndex Hc
            Hdom.consumed Hdom.isType)
        · change Hc.venv = baseEnv
          exact hvenv
        · change c.lparams = baseUs
          exact hlparams
        · exact hempty
        · exact hlevelsStable
        · exact hnindicesStable
        · exact hconstsStable
        · exact Hcache'
        · intro hlt
          exact False.elim (hi hlt)
        · simpa [Hc'] using hnormalized
    · by_cases hi : i = nparams
      · apply checkInductiveTypes.loopType.result.WF
          (k := k) (Q := Q) hforall hi
        exact Hresult Hc hvenv hlparams hempty hlevelsStable hnindicesStable
          hconstsStable hforall hi htype Hcache Hsuffix
      · exact parameterMismatch.WF hforall hi

/-- Skeleton-free traversal of a header's index suffix.  It retains exactly
the checker context and cached-parameter suffix needed by the next mutual
header; no declaration-facing target is involved. -/
theorem indices.accumulateContextWF
    {baseEnv : VEnv} {baseUs : List Name} {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats}
    {k : Expr → AddInductive.InductiveStats → Nat → AddInductive.M α}
    {Q : α → Prop}
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hresult : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      (_hvenv : Hc'.venv = baseEnv)
      (_hlparams : c'.lparams = baseUs)
      {type' current' nindices'},
      (¬ ∃ name dom body bi, type' = .forallE name dom body bi) →
      TrExpr Hc'.venv c'.lparams Hc'.mlctx.vlctx type' current' →
      ParameterContextSuffix Hc' stats (depth + nindices') →
      (k type' stats nindices' c').WF Q)
    (Hc : ContextWF c) (hvenv : Hc.venv = baseEnv)
    (hlparams : c.lparams = baseUs)
    (Hsuffix : ParameterContextSuffix Hc stats (depth + nindices))
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type current) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type nparams
      nindices fuel k c).WF Q := by
  induction fuel generalizing c type current nindices with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi,
        type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      rcases TrExpr.forallE_source htype with
        ⟨sourceDom, sourceBody, hdom, hbody,
          hdomType, _hbodyType, _hcurrent⟩
      rcases hconsume c Hc hdom hdomType with ⟨consumedDom, Hdom⟩
      apply index.sourceWF (stats := stats) (nparams := nparams)
        (i := nparams) (nindices := nindices) (fuel := fuel)
        (k := k) (Q := Q) Hc (by omega) Hdom hbody
      intro body' _hbodyEq normalized hnormalized
      let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
        Hdom.consumed Hdom.isType
      apply ih (c := { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotationsVerified bi })
        (current := body') (nindices := nindices + 1) (Hc := Hc')
      · change Hc.venv = baseEnv
        exact hvenv
      · change c.lparams = baseUs
        exact hlparams
      · simpa [Nat.add_assoc] using
          Hsuffix.withIndex Hc Hdom.consumed Hdom.isType
      · simpa [Hc'] using hnormalized
    · apply checkInductiveTypes.loopType.result.WF
        (k := k) (Q := Q) hforall rfl
      exact Hresult Hc hvenv hlparams hforall htype Hsuffix

/-- A raw checked source header is closed independently of the retained
first-header parameter context.  Therefore it initializes the later-header
parameter scope without requiring a semantic header target. -/
noncomputable def LaterParameterScope.ofRawHeader
    {c : AddInductive.Context} {source : InductiveType}
    {target : VConstVal}
    (Hc : ContextWF c)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (hi : 0 < stats.params.size)
    (Hsource : TrSourceConstRaw Hc.venv c.lparams
      source.name source.type target)
    (hnormalized : FVarsBelow Hc.mlctx.vlctx source.type normalized) :
    LaterParameterScope Hsuffix 0 normalized := by
  have hsourceNoFVars : FVarsIn (fun _ => False) source.type :=
    Hsource.type.fvarsIn.mono fun fv hfv => by
      simpa [VLCtx.fvars] using hfv
  have hfalseUpSet : IsFVarUpSet (fun _ => False) Hc.mlctx.vlctx := by
    have hsuffix := IsFVarUpSet.suffixFVars ([] : VLCtx)
      Hc.mlctx.vlctx (by simpa using Hc.mlctx_wf.tr.wf)
    simpa [VLCtx.fvars] using hsuffix
  exact LaterParameterScope.ofNoFVars hi
    (hnormalized _ hfalseUpSet hsourceNoFVars)

/-- Skeleton-free traversal of a later mutual header.  Cached common
parameters are consumed using their retained suffix, after which the generic
index fold above returns the enlarged context and suffix. -/
theorem laterHeader.accumulateContextWF
    {baseEnv : VEnv} {baseUs : List Name} {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats}
    {source : InductiveType} {target : VConstVal}
    {k : Expr → AddInductive.InductiveStats → Nat → AddInductive.M α}
    {Q : α → Prop}
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hresult : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      (_hvenv : Hc'.venv = baseEnv)
      (_hlparams : c'.lparams = baseUs)
      {type' current' nindices'},
      (¬ ∃ name dom body bi, type' = .forallE name dom body bi) →
      TrExpr Hc'.venv c'.lparams Hc'.mlctx.vlctx type' current' →
      ParameterContextSuffix Hc' stats (depth + nindices') →
      (k type' stats nindices' c').WF Q)
    (Hc : ContextWF c) (hvenv : Hc.venv = baseEnv)
    (hlparams : c.lparams = baseUs)
    (hnonempty : stats.indConsts.isEmpty = false)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (hparams : stats.params.size = nparams)
    (Hsource : TrSourceConstRaw Hc.venv c.lparams
      source.name source.type target)
    (hnormalized : FVarsBelow Hc.mlctx.vlctx source.type normalized)
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized current) :
    (AddInductive.checkInductiveTypes.loopType nparams stats normalized 0 0
      fuel k c).WF Q := by
  apply laterParametersWF Hc k Q
    (hnonempty := hnonempty) (Hsuffix := Hsuffix)
    (hparams := hparams) (hbound := by omega)
    (Hscope := fun hi =>
      LaterParameterScope.ofRawHeader Hc Hsuffix
        (by simpa [hparams] using hi) Hsource hnormalized)
    (htype := htype)
  intro type' current' i' fuel' hi htype'
  subst i'
  exact indices.accumulateContextWF hconsume Hresult Hc hvenv hlparams
    (depth := depth) (nindices := 0) Hsuffix htype'

end checkInductiveTypes.loopType

end VerifyInductive
end Lean4Lean
