import Lean4Lean.Verify.Inductive.Header.LoopType

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

namespace checkInductiveTypes.loopInd

/-- At the first mutual header, the executable `whnf` result determines a
syntax-directed abstract normal form.  Independent translation of the source
header shows that this normal form is definitionally equal to the header in
`TrInductDecl`; the checked source type supplies the common typing witness. -/
theorem initialHeaderNormalization
    {source : InductiveType} {target : VInductiveTypeSkeleton}
    (Hc : ContextWF c) (hctx : Hc.mlctx.vlctx = [])
    (Htarget : TrSourceConst Hc.venv c.lparams source.name source.type
      target.toVConstVal)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source.type checkedType sourceType checkedType')
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized sourceType) :
    ∃ normalized' exprType,
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx normalized normalized' ∧
      Hc.venv.IsDefEq c.lparams.length []
        target.type normalized' exprType := by
  rcases hnormalized with ⟨normalized', hnormalized', hnormalizedEq⟩
  have hsource : TrExprS Hc.venv c.lparams [] source.type sourceType := by
    simpa [hctx] using hchecked.2.1
  have htargetEq : Hc.venv.IsDefEqU c.lparams.length []
      target.type sourceType :=
    Htarget.type.uniq Hc.checking.tr.wf
      (.refl Hc.checking.tr.wf (by trivial)) hsource
  have hsourceType : Hc.venv.HasType c.lparams.length []
      sourceType checkedType' := by
    simpa [hctx, VLCtx.toCtx] using hchecked.2.2.2
  have htargetType := hsourceType.defeqU_l Hc.checking.tr.wf
    (by trivial) htargetEq.symm
  have hnormalizedEq' : Hc.venv.IsDefEqU c.lparams.length []
      normalized' sourceType := by
    simpa [hctx, VLCtx.toCtx] using hnormalizedEq
  have htargetNormalized := htargetEq.trans Hc.checking.tr.wf
    (by trivial) hnormalizedEq'.symm
  exact ⟨normalized', checkedType', hnormalized',
    htargetNormalized.of_l Hc.checking.tr.wf (by trivial) htargetType⟩

/-- Package initial normalization with the empty executable telescope state.
This is the state consumed by the first parameter/index branch. -/
theorem initialHeaderState
    {source : InductiveType} {target : VInductiveTypeSkeleton}
    (Hc : ContextWF c) (hctx : Hc.mlctx.vlctx = [])
    (Htarget : TrSourceConst Hc.venv c.lparams source.name source.type
      target.toVConstVal)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source.type checkedType sourceType checkedType')
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized sourceType) :
    ∃ normalized' exprType,
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx normalized normalized' ∧
      Hc.venv.IsDefEq c.lparams.length []
        target.type normalized' exprType ∧
      Nonempty (checkInductiveTypes.loopType.HeaderTelescopeLoopCertificate
        Hc normalized' normalized' 0 0) := by
  rcases initialHeaderNormalization Hc hctx Htarget hchecked hnormalized with
    ⟨normalized', exprType, hnormalized', hheader⟩
  have hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      [] Hc.mlctx.vlctx.toCtx := by
    simpa [hctx, VLCtx.toCtx] using
      (VEnv.IsDefEqCtx.refl (env := Hc.venv) (U := c.lparams.length)
        (by trivial : OnCtx ([] : List VExpr)
          (Hc.venv.IsType c.lparams.length)))
  exact ⟨normalized', exprType, hnormalized', hheader,
    ⟨checkInductiveTypes.loopType.HeaderTelescopeLoopCertificate.empty hctxEq⟩⟩

/-- Definitional synthesis state used by the complete first-header recursion. -/
theorem initialHeaderSynthesisState
    {source : InductiveType} {target : VInductiveTypeSkeleton}
    (Hc : ContextWF c) (hctx : Hc.mlctx.vlctx = [])
    (Htarget : TrSourceConst Hc.venv c.lparams source.name source.type
      target.toVConstVal)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source.type checkedType sourceType checkedType')
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized sourceType) :
    ∃ normalized',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx normalized normalized' ∧
      Nonempty (checkInductiveTypes.loopType.HeaderSynthesisCertificate
        Hc target normalized' 0 0) := by
  rcases initialHeaderNormalization Hc hctx Htarget hchecked hnormalized with
    ⟨normalized', exprType, hnormalized', hheader⟩
  have hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      [] Hc.mlctx.vlctx.toCtx := by
    simpa [hctx, VLCtx.toCtx] using
      (VEnv.IsDefEqCtx.refl (env := Hc.venv) (U := c.lparams.length)
        (by trivial : OnCtx ([] : List VExpr)
          (Hc.venv.IsType c.lparams.length)))
  have htargetType : Hc.venv.IsType c.lparams.length [] target.type := by
    have hwf := Htarget.wf
    change Hc.venv.IsType target.uvars [] target.type at hwf
    rw [Htarget.uvars] at hwf
    exact hwf
  have hcurrent : Hc.venv.IsType c.lparams.length [] normalized' :=
    htargetType.defeqU_l Hc.checking.tr.wf (by trivial) hheader.toU
  exact ⟨normalized', hnormalized',
    ⟨checkInductiveTypes.loopType.HeaderSynthesisCertificate.empty
      hctxEq hcurrent hheader⟩⟩

/-- A later source header is closed before cached parameters are substituted.
The outer `whnf` scope witness therefore initializes the narrow
later-parameter invariant at executable parameter zero. -/
noncomputable def initialLaterParameterScope
    {source : InductiveType} {target : VInductiveTypeSkeleton}
    (Hc : ContextWF c)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (hi : 0 < stats.params.size)
    (Htarget : TrSourceConst Hc.venv c.lparams source.name source.type
      target.toVConstVal)
    (hnormalized : FVarsBelow Hc.mlctx.vlctx source.type normalized) :
    checkInductiveTypes.loopType.LaterParameterScope
      Hsuffix 0 normalized := by
  have hsourceNoFVars : FVarsIn (fun _ => False) source.type :=
    Htarget.type.fvarsIn.mono fun fv hfv => by
      simpa [VLCtx.fvars] using hfv
  have hfalseUpSet : IsFVarUpSet (fun _ => False) Hc.mlctx.vlctx := by
    have hsuffix := IsFVarUpSet.suffixFVars ([] : VLCtx)
      Hc.mlctx.vlctx (by simpa using Hc.mlctx_wf.tr.wf)
    simpa [VLCtx.fvars] using hsuffix
  exact checkInductiveTypes.loopType.LaterParameterScope.ofNoFVars hi
    (hnormalized _ hfalseUpSet hsourceNoFVars)

/-- Although a later header is normalized in the retained first-header local
context, both the source header and its initial normal form are closed.  The
normalization equality therefore descends to the empty abstract context,
where it can seed an independent later-header telescope certificate. -/
theorem initialLaterHeaderDefEqOfTranslation
    {source : InductiveType} {target : VInductiveTypeSkeleton}
    (Hc : ContextWF c)
    (Htarget : TrSourceConst Hc.venv c.lparams source.name source.type
      target.toVConstVal)
    (hsource : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      source.type sourceType)
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized sourceType)
    (hfvars : FVarsIn (fun _ => False) normalized) :
    ∃ normalized',
      TrExprS Hc.venv c.lparams [] normalized normalized' ∧
      Hc.venv.IsDefEqU c.lparams.length [] target.type normalized' := by
  rcases hnormalized with ⟨normalizedFull, hnormalizedFull, hnormalizeEq⟩
  let W : VLCtx.FVLift [] Hc.mlctx.vlctx 0
      Hc.mlctx.vlctx.toCtx.length 0 :=
    VLCtx.FVLift.from_nil Hc.mlctx.noBV
  have hnormalizedClosed : Closed normalized 0 := by
    have := hnormalizedFull.closed
    simpa [Hc.mlctx.noBV] using this
  have hnormalizedNoFVars :
      FVarsIn (fun fv => fv ∈ VLCtx.fvars []) normalized := by
    simpa [VLCtx.fvars] using hfvars
  rcases hnormalizedFull.weakFV_inv Hc.checking.tr.wf W
      (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      hnormalizedClosed hnormalizedNoFVars with
    ⟨normalized', hnormalized'⟩
  have hsourceNoFVars : FVarsIn (fun _ => False) source.type :=
    Htarget.type.fvarsIn.mono fun fv hfv => by
      simpa [VLCtx.fvars] using hfv
  have hsourceClosed : Closed source.type 0 := by
    have := hsource.closed
    simpa [Hc.mlctx.noBV] using this
  have hsourceNoFVars' :
      FVarsIn (fun fv => fv ∈ VLCtx.fvars []) source.type := by
    simpa [VLCtx.fvars] using hsourceNoFVars
  rcases hsource.weakFV_inv Hc.checking.tr.wf W
      (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      hsourceClosed hsourceNoFVars' with
    ⟨sourceType', hsourceType'⟩
  have hnormalizedWeak := hnormalized'.weakFV Hc.checking.tr.wf.ordered
    W Hc.mlctx_wf.tr.wf
  have hsourceWeak := hsourceType'.weakFV Hc.checking.tr.wf.ordered
    W Hc.mlctx_wf.tr.wf
  have hnormalizedUniq := hnormalizedFull.uniq Hc.checking.tr.wf
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hnormalizedWeak
  have hsourceUniq := hsource.uniq Hc.checking.tr.wf
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hsourceWeak
  have hfull : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
      (normalized'.liftN Hc.mlctx.vlctx.toCtx.length 0)
      (sourceType'.liftN Hc.mlctx.vlctx.toCtx.length 0) :=
    hnormalizedUniq.symm.trans Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf.toCtx
      (hnormalizeEq.trans Hc.checking.tr.wf
        Hc.mlctx_wf.tr.wf.toCtx hsourceUniq)
  have hempty : Hc.venv.IsDefEqU c.lparams.length []
      normalized' sourceType' :=
    (VEnv.IsDefEqU.weakN_iff Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf.toCtx W.toCtx).1 hfull
  have htarget : Hc.venv.IsDefEqU c.lparams.length []
      target.type sourceType' :=
    Htarget.type.uniq Hc.checking.tr.wf
      (.refl Hc.checking.tr.wf (by trivial)) hsourceType'
  exact ⟨normalized', hnormalized',
    htarget.trans Hc.checking.tr.wf (by trivial) hempty.symm⟩

/-- Checker-facing wrapper for the direct source-translation initializer. -/
theorem initialLaterHeaderDefEq
    {source : InductiveType} {target : VInductiveTypeSkeleton}
    (Hc : ContextWF c)
    (Htarget : TrSourceConst Hc.venv c.lparams source.name source.type
      target.toVConstVal)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source.type checkedType sourceType checkedType')
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized sourceType)
    (hfvars : FVarsIn (fun _ => False) normalized) :
    ∃ normalized',
      TrExprS Hc.venv c.lparams [] normalized normalized' ∧
      Hc.venv.IsDefEqU c.lparams.length [] target.type normalized' :=
  initialLaterHeaderDefEqOfTranslation Hc Htarget hchecked.2.1
    hnormalized hfvars

/-- Initialize the narrow later-header synthesis state in the empty consumed
scope. -/
theorem initialLaterHeaderSynthesisStateOfTranslation
    {source : InductiveType} {target : VInductiveTypeSkeleton}
    (Hc : ContextWF c)
    (Htarget : TrSourceConst Hc.venv c.lparams source.name source.type
      target.toVConstVal)
    (hsource : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      source.type sourceType)
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized sourceType)
    (hfvars : FVarsIn (fun _ => False) normalized) :
    ∃ normalized',
      TrExprS Hc.venv c.lparams [] normalized normalized' ∧
      Nonempty (checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        Hc.venv c.lparams target [] normalized' 0 0) := by
  rcases initialLaterHeaderDefEqOfTranslation Hc Htarget hsource
      hnormalized hfvars with
    ⟨normalized', hnormalized', hheader⟩
  have htargetType : Hc.venv.IsType c.lparams.length [] target.type := by
    have hwf := Htarget.wf
    change Hc.venv.IsType target.uvars [] target.type at hwf
    rw [Htarget.uvars] at hwf
    exact hwf
  have hnormalizedType : Hc.venv.IsType c.lparams.length [] normalized' :=
    htargetType.defeqU_l Hc.checking.tr.wf (by trivial) hheader
  rcases htargetType with ⟨targetLevel, htargetType⟩
  have hheaderTyped := hheader.of_l Hc.checking.tr.wf (by trivial)
    htargetType
  exact ⟨normalized', hnormalized',
    ⟨checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate.empty
      ⟨targetLevel, htargetType⟩ hnormalizedType hheaderTyped⟩⟩

/-- Checker-facing wrapper for the direct source-translation synthesis
initializer. -/
theorem initialLaterHeaderSynthesisState
    {source : InductiveType} {target : VInductiveTypeSkeleton}
    (Hc : ContextWF c)
    (Htarget : TrSourceConst Hc.venv c.lparams source.name source.type
      target.toVConstVal)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source.type checkedType sourceType checkedType')
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized sourceType)
    (hfvars : FVarsIn (fun _ => False) normalized) :
    ∃ normalized',
      TrExprS Hc.venv c.lparams [] normalized normalized' ∧
      Nonempty (checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        Hc.venv c.lparams target [] normalized' 0 0) :=
  initialLaterHeaderSynthesisStateOfTranslation Hc Htarget hchecked.2.1
    hnormalized hfvars

def updatedStats (stats : AddInductive.InductiveStats)
    (lctx : LocalContext) (resultLevel : Level) (setResult : Bool)
    (nindices : Nat) (indName : Name) : AddInductive.InductiveStats :=
  let stats := if setResult then
    { stats with
      lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
  else stats
  { stats with
    nindices := stats.nindices.push nindices
    indConsts := stats.indConsts.push (.const indName stats.levels) }

@[simp] theorem updatedStats_levels :
    (updatedStats stats lctx resultLevel setResult nindices indName).levels =
      stats.levels := by
  cases setResult <;> rfl

@[simp] theorem updatedStats_nindices_size :
    (updatedStats stats lctx resultLevel setResult nindices indName).nindices.size =
      stats.nindices.size + 1 := by
  cases setResult <;> simp [updatedStats]

@[simp] theorem updatedStats_nindices :
    (updatedStats stats lctx resultLevel setResult nindices indName).nindices =
      stats.nindices.push nindices := by
  cases setResult <;> rfl

@[simp] theorem updatedStats_indConsts_size :
    (updatedStats stats lctx resultLevel setResult nindices indName).indConsts.size =
      stats.indConsts.size + 1 := by
  cases setResult <;> simp [updatedStats]

@[simp] theorem updatedStats_indConsts :
    (updatedStats stats lctx resultLevel setResult nindices indName).indConsts =
      stats.indConsts.push (.const indName stats.levels) := by
  cases setResult <;> rfl

@[simp] theorem updatedStats_params :
    (updatedStats stats lctx resultLevel setResult nindices indName).params =
      stats.params := by
  cases setResult <;> rfl

/-- Initialize the loop certificate when the first header fixes the common
result universe. -/
def HeaderLoopCertificate.first
    {c : AddInductive.Context} {decl : VInductDecl} {params : List VExpr}
    (hindex : 0 < decl.types.length)
    (htarget : decl.types[0] = target)
    (hofLevel : VLevel.ofLevel c.lparams resultSort =
      some target.resultLevel)
    (hshape : decl.TypeShape env params target) :
    HeaderLoopCertificate env c.lparams decl params
      (updatedStats stats c.lctx resultSort true nindices indName) 1 := by
  subst target
  exact {
    resultLevel := decl.types[0].resultLevel
    commonLevel := by simpa [updatedStats] using hofLevel
    headerPrefix := HeaderPrefixCertificate.first hindex hshape }

/-- Extend the loop certificate for a later mutual header using precisely the
successful production `isEquiv` guard and sort-translation witness. -/
def HeaderLoopCertificate.later
    {c : AddInductive.Context} {decl : VInductDecl} {params : List VExpr}
    (H : HeaderLoopCertificate env c.lparams decl params stats dIdx)
    (hindex : dIdx < decl.types.length)
    (htarget : decl.types[dIdx] = target)
    (hguard : resultSort.isEquiv stats.resultLevel = true)
    (hofLevel : VLevel.ofLevel c.lparams resultSort =
      some target.resultLevel)
    (hshape : decl.TypeShape env params target) :
    HeaderLoopCertificate env c.lparams decl params
      (updatedStats stats stats.lctx resultSort false nindices indName)
      (dIdx + 1) := by
  subst target
  exact {
    resultLevel := H.resultLevel
    commonLevel := by simpa [updatedStats] using H.commonLevel
    headerPrefix := H.headerPrefix.pushOfIsEquiv hindex hguard hofLevel
      H.commonLevel hshape }

def HeaderLoopCertificate.complete
    (H : HeaderLoopCertificate env lparams decl params stats
      decl.types.length) : HeaderCertificate env decl :=
  H.headerPrefix.complete

/-- Post-telescope continuation for the first mutual header. -/
theorem firstResult.WF
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type')
    (Hrec : ∀ resultSort,
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx (.sort resultSort) type' →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  change ((monadLift (TypeChecker.ensureSort type) : AddInductive.M Expr) c >>=
    fun type => ((do
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) : AddInductive.M α) c).WF Q
  refine (ensureSortInContext.WF Hc htype).bind fun sorted hsorted => ?_
  rcases hsorted with ⟨hsorted, resultSort, rfl⟩
  rw [if_pos hempty]
  have hread : ((read : AddInductive.M AddInductive.Context) c).WF (fun c' => c' = c) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun c' h => ?_
  subst c'
  simpa [updatedStats, Expr.sortLevel!] using Hrec resultSort hsorted

/-- The first mutual header records its result universe and simultaneously
assembles the independent `TypeShape` certificate before continuing with the
remaining headers. -/
theorem firstResult.refines
    {decl : VInductDecl} {target : VInductiveType}
    {params ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type result)
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ ownParams.reverse) Hc.mlctx.vlctx.toCtx)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hparams : decl.ParamsDefEq Hc.venv params ownParams)
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (Hrec : ∀ resultSort,
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      decl.TypeShape Hc.venv params target →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  apply firstResult.WF k Q Hc hempty htype
  intro resultSort hsorted
  rcases TrExpr.sort_source hsorted with ⟨resultLevel, hofLevel, _⟩
  have hresultLevel := hlevel resultSort resultLevel hofLevel
  subst resultLevel
  apply Hrec resultSort hofLevel
  exact TrExpr.typeShapeOfDefEqCtx Hc.checking.tr.wf Hc.mlctx_wf.tr.wf huvars
    hctxEq hheader hparamsTake hindicesTake hparams
    (hlevel resultSort) hsorted

/-- Canonical first-header specialization: choose the first header's own
parameter telescope as the block-wide parameter list.  Its `ParamsDefEq`
obligation is reflexive and follows from local-context well-formedness. -/
theorem firstResult.refinesCanonical
    {decl : VInductDecl} {target : VInductiveType}
    {ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type result)
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ ownParams.reverse) Hc.mlctx.vlctx.toCtx)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (Hrec : ∀ resultSort,
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      decl.TypeShape Hc.venv ownParams target →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  have hctxType : OnCtx (indices.reverse ++ ownParams.reverse)
      (Hc.venv.IsType decl.uvars) := by
    simpa [huvars] using hctxEq.isType
  exact firstResult.refines k Q Hc hempty htype huvars hctxEq hheader
    hparamsTake hindicesTake
    (VInductDecl.paramsDefEq_reflOfAppend hctxType) hlevel Hrec

/-- First-header result with the retained ambient-prefix invariant initialized
from the checked index telescope. -/
theorem firstResult.refinesRuntimeState
    {decl : VInductDecl} {target : VInductiveType}
    {ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type result)
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ ownParams.reverse) Hc.mlctx.vlctx.toCtx)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (Hrec : ∀ resultSort,
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      decl.TypeShape Hc.venv ownParams target →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc ownParams indices.length →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  apply firstResult.refinesCanonical k Q Hc hempty htype huvars hctxEq
    hheader hparamsTake hindicesTake hlevel
  intro resultSort hofLevel hshape
  exact Hrec resultSort hofLevel hshape
    (checkInductiveTypes.loopType.AmbientParamContext.ofFirstDefEq hctxEq)

/-- First-header result specialized to the state accumulated by the actual
`loopType` parameter/index branches.  The source telescope supplies the
parameter split, index split, and context-conversion premises. -/
theorem firstResult.refinesTelescope
    {decl : VInductDecl} {target : VInductiveType}
    {normalized result translatedResult exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (Htelescope : checkInductiveTypes.loopType.HeaderTelescopeLoopCertificate
      Hc normalized result decl.nparams nindices)
    (hnindices : nindices = target.numIndices)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type translatedResult)
    (hresultEq : Hc.venv.IsDefEqU c.lparams.length
      Hc.mlctx.vlctx.toCtx result translatedResult)
    (huvars : c.lparams.length = decl.uvars)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (Hrec : ∀ resultSort,
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      decl.TypeShape Hc.venv Htelescope.params target →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc Htelescope.params Htelescope.indices.length →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  subst nindices
  apply firstResult.WF k Q Hc hempty htype
  intro resultSort hsorted
  rcases TrExpr.sort_source hsorted with ⟨resultLevel, hofLevel, _⟩
  have hresultLevel := hlevel resultSort resultLevel hofLevel
  subst resultLevel
  have hctxType : OnCtx
      (Htelescope.indices.reverse ++ Htelescope.params.reverse)
      (Hc.venv.IsType decl.uvars) := by
    simpa [huvars] using Htelescope.telescope.context.isType
  have hshape := TrExpr.typeShapeOfDefEqCtxResult
    Hc.checking.tr.wf Hc.mlctx_wf.tr.wf huvars
    Htelescope.telescope.context hheader Htelescope.takeParameters
    Htelescope.takeIndices
    (VInductDecl.paramsDefEq_reflOfAppend hctxType) hresultEq
    (hlevel resultSort) hsorted
  exact Hrec resultSort hofLevel hshape
    (checkInductiveTypes.loopType.AmbientParamContext.ofFirstDefEq
      Htelescope.telescope.context)

/-- Post-telescope first-header refinement using the definitional synthesis
state produced by `firstHeaderSynthesisWF`. -/
theorem firstResult.refinesSynthesis
    {decl : VInductDecl} {target : VInductiveType}
    {current : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (Hsynthesis : checkInductiveTypes.loopType.HeaderSynthesisCertificate
      Hc target.toSkeleton current decl.nparams nindices)
    (hnindices : nindices = target.numIndices)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type current)
    (huvars : c.lparams.length = decl.uvars)
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (Hrec : ∀ resultSort,
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      decl.TypeShape Hc.venv Hsynthesis.params target →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc Hsynthesis.params Hsynthesis.indices.length →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  subst nindices
  apply firstResult.WF k Q Hc hempty htype
  intro resultSort hsorted
  rcases TrExpr.sort_source hsorted with ⟨resultLevel, hofLevel, _⟩
  have hresultLevel := hlevel resultSort resultLevel hofLevel
  subst resultLevel
  exact Hrec resultSort hofLevel
    (Hsynthesis.typeShape huvars (hlevel resultSort) hsorted)
    (checkInductiveTypes.loopType.AmbientParamContext.ofFirstDefEq
      Hsynthesis.context)

/-- Metadata-synthesizing first-header continuation.  The executable index
counter and translated result sort are exported as data, together with a
declaration-independent shape proof; no pre-existing `VInductiveType`
metadata is assumed. -/
theorem firstResult.synthesizesHeader
    {source : VInductiveTypeSkeleton} {current : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (Hsynthesis : checkInductiveTypes.loopType.HeaderSynthesisCertificate
      Hc source current nparams nindices)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type current)
    (huvars : c.lparams.length = uvars)
    (Hrec : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      checkInductiveTypes.loopType.SynthesizedHeader Hc.venv uvars nparams
        Hsynthesis.params source nindices resultLevel →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc Hsynthesis.params Hsynthesis.indices.length →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  apply firstResult.WF k Q Hc hempty htype
  intro resultSort hsorted
  rcases TrExpr.sort_source hsorted with ⟨resultLevel, hofLevel, _⟩
  exact Hrec resultSort resultLevel hofLevel
    (Hsynthesis.synthesizedHeader huvars hofLevel hsorted)
    (checkInductiveTypes.loopType.AmbientParamContext.ofFirstDefEq
      Hsynthesis.context)

/-- Initialize the ordered mutual metadata prefix from the first successful
header result. -/
theorem firstResult.initializesPrefix
    {skeleton : VInductDeclSkeleton} {current : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (hindex : 0 < skeleton.types.length)
    (Hsynthesis : checkInductiveTypes.loopType.HeaderSynthesisCertificate
      Hc skeleton.types[0] current skeleton.nparams nindices)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type current)
    (huvars : c.lparams.length = skeleton.uvars)
    (Hrec : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      checkInductiveTypes.loopType.SynthesizedHeaderPrefix Hc.venv
        skeleton Hsynthesis.params resultLevel [(nindices, resultLevel)] 1 →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc Hsynthesis.params Hsynthesis.indices.length →
      (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  apply firstResult.synthesizesHeader k Q Hc hempty Hsynthesis htype
    huvars
  intro resultSort resultLevel hofLevel Hheader Hambient
  exact Hrec resultSort resultLevel hofLevel
    (checkInductiveTypes.loopType.SynthesizedHeaderPrefix.first
      hindex Hheader) Hambient

/-- Post-telescope continuation for later mutual headers.  A mismatched result
universe throws; a successful path records the checked equivalence before
updating the per-type arrays. -/
theorem laterResult.WF
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hnonempty : stats.indConsts.isEmpty = false)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type')
    (Hrec : ∀ resultSort,
      resultSort.isEquiv stats.resultLevel = true →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx (.sort resultSort) type' →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats stats.lctx resultSort false nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  change ((monadLift (TypeChecker.ensureSort type) : AddInductive.M Expr) c >>=
    fun type => ((do
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) : AddInductive.M α) c).WF Q
  refine (ensureSortInContext.WF Hc htype).bind fun sorted hsorted => ?_
  rcases hsorted with ⟨hsorted, resultSort, rfl⟩
  rw [if_neg (by simp [hnonempty])]
  by_cases hequiv : (Expr.sort resultSort).sortLevel!.isEquiv stats.resultLevel = true
  · have hequiv' : resultSort.isEquiv stats.resultLevel = true := by
      simpa [Expr.sortLevel!] using hequiv
    simpa [updatedStats, Expr.sortLevel!, hequiv, hequiv'] using
      Hrec resultSort hequiv' hsorted
  · have hfalse : (Expr.sort resultSort).sortLevel!.isEquiv stats.resultLevel = false := by
      cases h : (Expr.sort resultSort).sortLevel!.isEquiv stats.resultLevel <;>
        simp_all
    have hnot : (!(Expr.sort resultSort).sortLevel!.isEquiv stats.resultLevel) = true := by
      simp [hfalse]
    rw [if_pos hnot]
    change (Except.error _).WF Q
    exact Except.WF.throw

/-- Every later mutual header produces the same independent `TypeShape`
certificate as the first header. The executable `isEquiv` guard is retained
as an explicit continuation premise; it is subsequently used to establish
the common-result-universe component of `FormationWF`. -/
theorem laterResult.refines
    {decl : VInductDecl} {target : VInductiveType}
    {params ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hnonempty : stats.indConsts.isEmpty = false)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type result)
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ ownParams.reverse) Hc.mlctx.vlctx.toCtx)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hparams : decl.ParamsDefEq Hc.venv params ownParams)
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (Hrec : ∀ resultSort,
      resultSort.isEquiv stats.resultLevel = true →
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      decl.TypeShape Hc.venv params target →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats stats.lctx resultSort false nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  apply laterResult.WF k Q Hc hnonempty htype
  intro resultSort hequiv hsorted
  rcases TrExpr.sort_source hsorted with ⟨resultLevel, hofLevel, _⟩
  have hresultLevel := hlevel resultSort resultLevel hofLevel
  subst resultLevel
  apply Hrec resultSort hequiv hofLevel
  exact TrExpr.typeShapeOfDefEqCtx Hc.checking.tr.wf Hc.mlctx_wf.tr.wf huvars
    hctxEq hheader hparamsTake hindicesTake hparams
    (hlevel resultSort) hsorted

/-- Metadata-synthesizing continuation for a later mutual header.  The
executable result-universe guard extends the ordered metadata prefix, while
the successful parameter comparisons let the independently synthesized
header use the common parameter telescope fixed by the first family member.

This theorem deliberately starts at the post-telescope boundary.  The
per-binder later-header recursion has a different runtime shape from the
first header (cached parameters are substituted rather than introduced), so
it is verified separately instead of being hidden behind the first-header
invariant. -/
theorem laterResult.extendsPrefix
    {skeleton : VInductDeclSkeleton} {source : VInductiveTypeSkeleton}
    {current : VExpr} {commonParams : List VExpr}
    {metadata : List (Nat × VLevel)} {commonLevel : VLevel}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hnonempty : stats.indConsts.isEmpty = false)
    (hindex : dIdx < skeleton.types.length)
    (hsource : skeleton.types[dIdx] = source)
    (Hprefix : checkInductiveTypes.loopType.SynthesizedHeaderPrefix
      Hc.venv skeleton commonParams commonLevel metadata dIdx)
    (Hsynthesis : checkInductiveTypes.loopType.HeaderSynthesisCertificate
      Hc source current skeleton.nparams nindices)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type current)
    (huvars : c.lparams.length = skeleton.uvars)
    (hparams : VEnv.IsDefEqCtx Hc.venv skeleton.uvars []
      commonParams.reverse Hsynthesis.params.reverse)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (Hrec : ∀ resultSort resultLevel,
      resultSort.isEquiv stats.resultLevel = true →
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      checkInductiveTypes.loopType.SynthesizedHeaderPrefix Hc.venv
        skeleton commonParams commonLevel
        (metadata ++ [(nindices, resultLevel)]) (dIdx + 1) →
      (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1)
        (updatedStats stats stats.lctx resultSort false nindices indName)
        k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
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
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  subst source
  apply laterResult.WF k Q Hc hnonempty htype
  intro resultSort hguard hsorted
  rcases TrExpr.sort_source hsorted with
    ⟨resultLevel, hofLevel, _hresult⟩
  have hheader := Hsynthesis.synthesizedHeaderWithParams huvars hparams
    hofLevel hsorted
  have hlevel : resultLevel ≈ commonLevel :=
    Level.isEquiv_wf hguard hofLevel hcommon
  exact Hrec resultSort resultLevel hguard hofLevel
    (Hprefix.push hindex hheader hlevel)

/-- Later-header result continuation for the independent narrow telescope.
The executable sort check runs in the retained runtime context; `resultSort`
restricts its translation before the synthesized header is added to the
ordered metadata prefix. -/
theorem laterResult.extendsPrefixNarrow
    {skeleton : VInductDeclSkeleton} {source : VInductiveTypeSkeleton}
    {narrowCurrent fullCurrent : VExpr} {scope : VLCtx}
    {commonParams : List VExpr}
    {metadata : List (Nat × VLevel)} {commonLevel : VLevel}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hnonempty : stats.indConsts.isEmpty = false)
    (hindex : dIdx < skeleton.types.length)
    (hsource : skeleton.types[dIdx] = source)
    (Hprefix : checkInductiveTypes.loopType.SynthesizedHeaderPrefix
      Hc.venv skeleton commonParams commonLevel metadata dIdx)
    (Hsynthesis : checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
      Hc.venv c.lparams source scope narrowCurrent
      skeleton.nparams nindices)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowCurrent)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      type fullCurrent)
    (huvars : c.lparams.length = skeleton.uvars)
    (hparams : VEnv.IsDefEqCtx Hc.venv skeleton.uvars []
      commonParams.reverse Hsynthesis.params.reverse)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (Hrec : ∀ resultSort resultLevel,
      resultSort.isEquiv stats.resultLevel = true →
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      checkInductiveTypes.loopType.SynthesizedHeaderPrefix Hc.venv
        skeleton commonParams commonLevel
        (metadata ++ [(nindices, resultLevel)]) (dIdx + 1) →
      (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1)
        (updatedStats stats stats.lctx resultSort false nindices indName)
        k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
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
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  subst source
  rcases htypeFull with ⟨sourceFull, hsourceFull, _hsourceEq⟩
  apply laterResult.WF k Q Hc hnonempty hsourceFull
  intro resultSort hguard hsorted
  have hsourceFull' : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      type sourceFull :=
    hsourceFull.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
  have hsortedNarrow := Hruntime.resultSort Hc.checking.tr.wf
    htypeNarrow hsourceFull' hsorted
  rcases TrExpr.sort_source hsortedNarrow with
    ⟨resultLevel, hofLevel, _hresult⟩
  have hheader := Hsynthesis.synthesizedHeaderWithParams
    Hc.checking.tr.wf huvars hparams hofLevel hsortedNarrow
  have hlevel : resultLevel ≈ commonLevel :=
    Level.isEquiv_wf hguard hofLevel hcommon
  exact Hrec resultSort resultLevel hguard hofLevel
    (Hprefix.push hindex hheader hlevel)

/-- Base case of the mutual-header loop.  The executable assertions become
explicit invariants at the proof boundary instead of being silently erased. -/
theorem result.WF
    (hidx : ¬ dIdx < indTypes.size)
    (hlevels : stats.levels.length = c.lparams.length)
    (hindices : stats.nindices.size = indTypes.size)
    (hconsts : stats.indConsts.size = indTypes.size)
    (hparams : stats.params.size = nparams)
    (Hk : (k stats c).WF Q) :
    (AddInductive.checkInductiveTypes.loopInd nparams indTypes dIdx stats k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopInd]
  rw [dif_neg hidx]
  have hread : ((read : AddInductive.M AddInductive.Context) c).WF (fun c' => c' = c) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  simpa [hlevels, hindices, hconsts, hparams] using Hk

/-- Verified prefix of one mutual-header iteration: closed source checking and
WHNF are connected to the abstract translation before control enters the
already verified telescope loop.  The continuation owns the result-sort,
statistics update, and recursive mutual iteration invariants. -/
theorem stepPrefix.WF
    (Hc : ContextWF c) (hidx : dIdx < indTypes.size)
    (Hloop : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        indTypes[dIdx].type checkedType type' checkedType' →
      ∀ normalized,
      FVarsBelow Hc.mlctx.vlctx indTypes[dIdx].type normalized →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized type' →
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
            throw <| .other "mutually inductive types must live in the same universe"
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
            throw <| .other "mutually inductive types must live in the same universe"
          stats := { stats with
            nindices := stats.nindices.push nindices
            indConsts := stats.indConsts.push
              (.const indTypes[dIdx].name stats.levels) }
          AddInductive.checkInductiveTypes.loopInd nparams indTypes
            (dIdx + 1) stats k)) : AddInductive.M _) c).WF Q
  exact (checkClosedType.WF Hc).bind fun checkedType hchecked => by
    rcases hchecked with ⟨type', checkedType', hchecked⟩
    exact (whnfInContext.scopeWF Hc hchecked.2.1).bind
      fun normalized hnormalized =>
      Hloop checkedType type' checkedType' hchecked normalized
        hnormalized.1 hnormalized.2

/-- Metadata-free declaration-facing header step.  This is the entry point
used before `checkInductiveTypes` has recovered enough information to build a
`VInductDecl`. -/
theorem stepPrefix.refinesSkeleton
    {skeleton : VInductDeclSkeleton}
    {envTypes : VEnv}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeletonHeaders Hc.venv c.lparams nparams
      indTypes.toList isUnsafe skeleton envTypes)
    (hidx : dIdx < indTypes.size)
    (Hloop : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        indTypes[dIdx].type checkedType type' checkedType' →
      ∀ envTypes,
        Hc.venv.addConstVals skeleton.typeConstants = some envTypes →
        ∀ target,
        skeleton.types[dIdx]? = some target →
        TrSourceConst Hc.venv c.lparams indTypes[dIdx].name
          indTypes[dIdx].type target.toVConstVal →
      ∀ normalized,
        FVarsBelow Hc.mlctx.vlctx indTypes[dIdx].type normalized →
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized type' →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized 0 0
          c.fuel.inductiveFuel (fun type stats nindices =>
            show AddInductive.M _ from do
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
  have htarget : dIdx < skeleton.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeletonHeaders.types_length Hdecl]
    simpa using hidx
  have htargetTr :=
    Lean4Lean.VerifyInductive.TrInductDeclSkeletonHeaders.typeAt Hdecl dIdx
      (by simpa using hidx) htarget
  apply stepPrefix.WF (nparams := nparams) (stats := stats) (k := k)
    (Q := Q) Hc hidx
  intro checkedType type' checkedType' hchecked normalized hscope hnormalized
  exact Hloop checkedType type' checkedType' hchecked envTypes Hdecl.typesAdded
    skeleton.types[dIdx] (by simp [htarget])
      (by simpa using htargetTr.header)
    normalized hscope hnormalized

/-- Complete first iteration of the executable mutual-header loop, from the
closed source check through initialization of the ordered synthesized
metadata prefix. -/
theorem firstStep.initializesPrefix
    {skeleton : VInductDeclSkeleton}
    {envTypes : VEnv}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeletonHeaders Hc.venv c.lparams skeleton.nparams
      indTypes.toList isUnsafe skeleton envTypes)
    (hctx : Hc.mlctx.vlctx = [])
    (hidx : 0 < indTypes.size)
    (hempty : stats.indConsts.isEmpty = true)
    (hparams : stats.params = #[])
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hrec : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {nindices : Nat}
      {resultSort : Level} {resultLevel : VLevel} {params : List VExpr},
      (Hc' : ContextWF c') →
      c'.env = c.env →
      c'.lparams = c.lparams →
      stats'.levels = stats.levels →
      stats'.nindices = stats.nindices →
      stats'.indConsts = stats.indConsts →
      TrInductDeclSkeletonHeaders Hc'.venv c'.lparams skeleton.nparams
        indTypes.toList isUnsafe skeleton envTypes →
      VLevel.ofLevel c'.lparams resultSort = some resultLevel →
      checkInductiveTypes.loopType.ParameterCachePrefix
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats'
        skeleton.nparams nindices →
      checkInductiveTypes.loopType.ParameterContextSuffix
        Hc' stats' nindices →
      checkInductiveTypes.loopType.SynthesizedHeaderPrefix Hc'.venv
        skeleton params resultLevel [(nindices, resultLevel)] 1 →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc' params nindices →
      (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes 1
        (updatedStats stats' c'.lctx resultSort true nindices
          indTypes[0].name) k c').WF Q) :
    (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes 0
      stats k c).WF Q := by
  have hskeletonIdx : 0 < skeleton.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeletonHeaders.types_length Hdecl]
    simpa using hidx
  apply stepPrefix.refinesSkeleton (k := k) (Q := Q) Hc Hdecl hidx
  intro checkedType type' checkedType' hchecked translatedTypes htypes
    target htarget Htarget normalized _hscope hnormalized
  have htargetEq : target = skeleton.types[0] := by
    symm
    simpa [List.getElem?_eq_getElem hskeletonIdx] using htarget
  subst target
  rcases initialHeaderSynthesisState Hc hctx Htarget hchecked hnormalized with
    ⟨normalized', hnormalized', ⟨Hsynthesis⟩⟩
  have Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats 0 0 :=
    checkInductiveTypes.loopType.ParameterCachePrefix.empty hparams
  have Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats 0 :=
    checkInductiveTypes.loopType.ParameterContextSuffix.empty Hc hctx hparams
  apply checkInductiveTypes.loopType.firstHeaderSynthesisWF
    (Us := c.lparams) (target := skeleton.types[0])
    (nparams := skeleton.nparams) (stats := stats)
    (type := normalized) (current := normalized') (i := 0)
    (nindices := 0) (c := c)
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
      AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes 1
        stats k)
    (Q := Q) (hconsume := hconsume)
    (Hresult := by
      intro c' stats' type'' current'' i' nindices' Hc' henv' hlparams'
        hempty' hlevels' hnindices' hconsts' Hdecl' hforall iEq Hcache'
        Hsuffix' Hsynthesis' htype'
      cases iEq
      apply firstResult.initializesPrefix k Q Hc' hempty' hskeletonIdx
        Hsynthesis' htype'
      · rw [hlparams', ← Hdecl.uvars]
      · intro resultSort resultLevel hofLevel Hprefix Hambient
        apply Hrec Hc' henv' hlparams' hlevels' hnindices' hconsts'
          (by simpa [hlparams'] using Hdecl') hofLevel Hcache' Hsuffix'
          Hprefix
        simpa [Hsynthesis'.indexCount] using Hambient)
    (Hc := Hc) (henv := rfl) (hlparams := rfl) (hempty := hempty)
    (hlevelsStable := rfl) (hnindicesStable := rfl)
    (hconstsStable := rfl)
    (R := fun env => TrInductDeclSkeletonHeaders env c.lparams
      skeleton.nparams indTypes.toList isUnsafe skeleton envTypes)
    (HR := Hdecl)
    (Hcache := Hcache) (Hsuffix := Hsuffix) (Hsynthesis := Hsynthesis)
    (hphase := by
      intro _
      exact ⟨List.eq_nil_of_length_eq_zero Hsynthesis.indexCount, rfl⟩)
    (htype := hnormalized')

/-- Complete a noninitial mutual-header iteration.  Cached parameters are
consumed in an independent narrow telescope, later indices extend both the
runtime and outer-loop context certificates, and the result sort appends one
ordered metadata entry. -/
theorem laterStep.extendsPrefix
    {skeleton : VInductDeclSkeleton} {commonParams : List VExpr}
    {commonLevel : VLevel} {metadata : List (Nat × VLevel)}
    {envTypes : VEnv}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeletonHeaders Hc.venv c.lparams skeleton.nparams
      indTypes.toList isUnsafe skeleton envTypes)
    (hidx : dIdx < indTypes.size)
    (_hnoninitial : 0 < dIdx)
    (hnonempty : stats.indConsts.isEmpty = false)
    (hparams : stats.params.size = skeleton.nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats skeleton.nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hprefix : checkInductiveTypes.loopType.SynthesizedHeaderPrefix
      Hc.venv skeleton commonParams commonLevel metadata dIdx)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc commonParams depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hrec : ∀ {c' : AddInductive.Context} {nindices : Nat}
      {resultSort : Level} {resultLevel : VLevel},
      (Hc' : ContextWF c') →
      c'.env = c.env →
      c'.lparams = c.lparams →
      TrInductDeclSkeletonHeaders Hc'.venv c'.lparams skeleton.nparams
        indTypes.toList isUnsafe skeleton envTypes →
      checkInductiveTypes.loopType.ParameterCachePrefix
        Hc'.venv c'.lparams Hc'.mlctx.vlctx
        (updatedStats stats stats.lctx resultSort false nindices
          indTypes[dIdx].name)
        skeleton.nparams (depth + nindices) →
      checkInductiveTypes.loopType.ParameterContextSuffix Hc'
        (updatedStats stats stats.lctx resultSort false nindices
          indTypes[dIdx].name)
        (depth + nindices) →
      checkInductiveTypes.loopType.SynthesizedHeaderPrefix Hc'.venv
        skeleton commonParams commonLevel
        (metadata ++ [(nindices, resultLevel)]) (dIdx + 1) →
      checkInductiveTypes.loopType.AmbientParamContext Hc'
        commonParams (depth + nindices) →
      (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1)
        (updatedStats stats stats.lctx resultSort false nindices
          indTypes[dIdx].name) k c').WF Q) :
    (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
      dIdx stats k c).WF Q := by
  have hskeletonIdx : dIdx < skeleton.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeletonHeaders.types_length Hdecl]
    simpa using hidx
  apply stepPrefix.refinesSkeleton (k := k) (Q := Q) Hc Hdecl hidx
  intro checkedType type' checkedType' hchecked translatedTypes htypes
    target htarget Htarget normalized hbelow hnormalized
  have htargetEq : target = skeleton.types[dIdx] := by
    symm
    simpa [List.getElem?_eq_getElem hskeletonIdx] using htarget
  subst target
  have hnormalizedNoFVars : FVarsIn (fun _ => False) normalized := by
    have hsourceNoFVars : FVarsIn (fun _ => False)
        indTypes[dIdx].type :=
      Htarget.type.fvarsIn.mono fun fv hfv => by
        simpa [VLCtx.fvars] using hfv
    have hfalseUpSet : IsFVarUpSet (fun _ => False)
        Hc.mlctx.vlctx := by
      have hsuffix := IsFVarUpSet.suffixFVars ([] : VLCtx)
        Hc.mlctx.vlctx (by simpa using Hc.mlctx_wf.tr.wf)
      simpa [VLCtx.fvars] using hsuffix
    exact hbelow _ hfalseUpSet hsourceNoFVars
  rcases initialLaterHeaderSynthesisState Hc Htarget hchecked
      hnormalized hnormalizedNoFVars with
    ⟨narrowCurrent, hnormalizedNarrow, ⟨Hsynthesis⟩⟩
  let Hscope : ∀ h : 0 < stats.params.size,
      checkInductiveTypes.loopType.LaterParameterScope Hsuffix 0
        normalized := fun h =>
    initialLaterParameterScope Hc Hsuffix h Htarget hbelow
  apply checkInductiveTypes.loopType.laterParameterSynthesisWF Hc
    (target := skeleton.types[dIdx])
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
      AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1) stats k)
    (Q := Q) hnonempty Hsuffix
    (Hresult := by
      intro type'' narrow'' full'' scope'' i'' fuel'' hi'' Hsynthesis''
        hscope'' htypeNarrow'' htypeFVars'' htypeFull''
      cases hi''
      subst scope''
      let Hruntime :=
        checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
          Hc Hsuffix
      have hindices'' : Hsynthesis''.indices = [] :=
        List.eq_nil_of_length_eq_zero Hsynthesis''.indexCount
      have hparamScope : Hsuffix.parameterDecls.toCtx =
          Hsynthesis''.params.reverse := by
        simpa [hindices''] using Hsynthesis''.scopeCtx
      have hparamsBoundary := Hsuffix.paramsDefEq Hambient <|
        Hprefix.parameterCount.trans hparams.symm
      rw [hparamScope] at hparamsBoundary
      apply checkInductiveTypes.loopType.laterIndexSynthesisWF
        (depth := depth) (commonParams := commonParams)
        (paramU := c.lparams.length)
        (R := fun env =>
          checkInductiveTypes.loopType.SynthesizedHeaderPrefix env
              skeleton commonParams commonLevel metadata dIdx ∧
            TrInductDeclSkeletonHeaders env c.lparams skeleton.nparams
              indTypes.toList isUnsafe skeleton envTypes)
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
          AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
            (dIdx + 1) stats k)
        (Q := Q)
        (Hresult := by
          intro c' Hc' henv' hlparams' type''' narrow''' full''' scope'''
            nindices''' fuel''' hforall''' Hsynthesis''' Hruntime'''
            htypeNarrow''' _htypeFVars''' htypeFull''' Hcache'''
            Hsuffix''' Hambient''' HR''' hparams'''
          rcases HR''' with ⟨Hprefix''', Hdecl'''⟩
          apply checkInductiveTypes.loopType.result.WF
            (fuel := fuel''') (Q := Q) hforall''' rfl
          apply laterResult.extendsPrefixNarrow
            (indTypes := indTypes) (indName := indTypes[dIdx].name)
            (commonParams := commonParams) (metadata := metadata)
            (commonLevel := commonLevel) k Q Hc' hnonempty
            hskeletonIdx rfl Hprefix''' Hsynthesis'''
            Hruntime''' htypeNarrow''' htypeFull'''
          · rw [hlparams', ← Hdecl.uvars]
          · simpa [hlparams', ← Hdecl.uvars] using hparams'''
          · simpa [hlparams'] using hcommon
          · intro resultSort resultLevel hguard hofLevel Hprefix'
            apply Hrec Hc' henv' hlparams'
            · simpa [hlparams'] using Hdecl'''
            · exact Hcache'''.reindex (by simp [updatedStats])
            · exact Hsuffix'''.reindex (by simp [updatedStats])
            · exact Hprefix'
            · exact Hambient''')
        hconsume Hc rfl (by simpa using Hcache) (by simpa using Hsuffix)
        (by simpa using Hambient) ⟨Hprefix, Hdecl⟩ Hsynthesis''
        hparamsBoundary
        Hruntime
        htypeNarrow'' htypeFVars'' htypeFull'')
    hparams (by omega) Hscope
    (fun h => (Hscope h).older_eq_nil h |>.symm)
    (by
      intro hzero
      have hsize : stats.params.size = 0 := hparams.trans hzero.symm
      apply (List.eq_nil_of_length_eq_zero ?_).symm
      rw [Hsuffix.parameterDecls_length, hsize])
    Hsynthesis hnormalizedNarrow (by simpa [VLCtx.fvars] using
      hnormalizedNoFVars) hnormalized

/-- Concrete statistics recovered together with a materialized mutual header.
This is the early traversal-facing form of `ValidAppStatsWF`; it is kept here
because the latter also packages the derived name-search invariant used by
positivity, which is defined after the executable constructor interfaces. -/
structure MaterializedHeaderResult (env : VEnv) (Us : List Name)
    (Δ : VLCtx) (stats : AddInductive.InductiveStats)
    (decl : VInductDecl) (depth : Nat) where
  headers : HeaderCertificate env decl
  levels : stats.levels.length = decl.uvars
  levelParams : stats.levels = Us.map .param
  uvars : Us.length = decl.uvars
  consts : stats.indConsts =
    (decl.types.map fun type => .const type.name stats.levels).toArray
  indices : stats.nindices.toList = decl.types.map (·.numIndices)
  params : List.Forall₂ (TrExprS env Us Δ) stats.params.toList
    (decl.paramVars depth)
  paramFVars : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv
  parameterScope : VLCtx
  ambientScope : VLCtx
  scopeDecomposition : Δ = ambientScope ++ parameterScope
  ambientLength : ambientScope.length = depth
  cachedScope : List.Forall₂
    checkInductiveTypes.loopType.CachedParameterDecl
    stats.params.toList.reverse parameterScope
  runtimeScope : checkInductiveTypes.loopType.NarrowRuntimeScope
    env Us parameterScope Δ
  paramsContext : VEnv.IsDefEqCtx env Us.length []
    headers.params.reverse parameterScope.toCtx
  narrowParams : List.Forall₂ (TrExprS env Us parameterScope)
    stats.params.toList (decl.paramVars 0)

/-- The executable universe arguments initialized from the declaration's
level-parameter names translate pointwise to their abstract parameter
indices. -/
theorem VLevel.mapM_ofLevel_paramNames (names : List Name) :
    (names.map Level.param).mapM (VLevel.ofLevel names) =
      some (names.map fun name => .param (names.idxOf name)) := by
  have go : ∀ xs : List Name, xs ⊆ names →
      (xs.map Level.param).mapM (VLevel.ofLevel names) =
        some (xs.map fun name => .param (names.idxOf name)) := by
    intro xs hsubset
    induction xs with
    | nil => rfl
    | cons name xs ih =>
      have hname : names.idxOf name < names.length :=
        List.idxOf_lt_length_iff.2 (hsubset (by simp))
      simp [VLevel.ofLevel, hname,
        ih (fun value hvalue => hsubset (by simp [hvalue]))]
  exact go names fun _ => id

theorem MaterializedHeaderResult.levelTranslation
    (H : MaterializedHeaderResult env Us Δ stats decl depth) :
    stats.levels.mapM (VLevel.ofLevel Us) =
      some (Us.map fun name => .param (Us.idxOf name)) := by
  rw [H.levelParams]
  exact VLevel.mapM_ofLevel_paramNames Us

def _root_.Lean4Lean.TrSourceConst.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrSourceConst env Us name type value) :
    TrSourceConst env' Us name type value where
  uvars := H.uvars
  name := H.name
  type := H.type.mono henv
  wf := H.wf.mono henv

private theorem forall₂_trExprS_mono {env env' : VEnv}
    (henv : env ≤ env') :
    ∀ {es : List Expr} {es' : List VExpr},
      List.Forall₂ (TrExprS env Us Δ) es es' →
      List.Forall₂ (TrExprS env' Us Δ) es es'
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => .cons (h.mono henv)
      (forall₂_trExprS_mono henv hs)

def MaterializedHeaderResult.mono {env env' : VEnv}
    (henv : env ≤ env')
    (H : MaterializedHeaderResult env Us Δ stats decl depth) :
    MaterializedHeaderResult env' Us Δ stats decl depth where
  headers := H.headers.mono henv
  levels := H.levels
  levelParams := H.levelParams
  uvars := H.uvars
  consts := H.consts
  indices := H.indices
  params := forall₂_trExprS_mono henv H.params
  paramFVars := H.paramFVars
  parameterScope := H.parameterScope
  ambientScope := H.ambientScope
  scopeDecomposition := H.scopeDecomposition
  ambientLength := H.ambientLength
  cachedScope := H.cachedScope
  runtimeScope := H.runtimeScope.mono henv
  paramsContext := H.paramsContext.mono henv
  narrowParams := forall₂_trExprS_mono henv H.narrowParams

/-- Fold the verified noninitial step over the remainder of the mutual block.
At exact coverage the executable length assertions are discharged and the
metadata-free declaration is materialized together with its header
certificate. -/
theorem laterSteps.materialize
    {skeleton : VInductDeclSkeleton} {commonParams : List VExpr}
    {commonLevel : VLevel} {metadata : List (Nat × VLevel)}
    {envTypes : VEnv}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeletonHeaders Hc.venv c.lparams skeleton.nparams
      indTypes.toList isUnsafe skeleton envTypes)
    (hdone : dIdx ≤ indTypes.size)
    (hpositive : 0 < dIdx)
    (hlevels : stats.levels.length = c.lparams.length)
    (hlevelParams : stats.levels = c.lparams.map .param)
    (hindices : stats.nindices.size = dIdx)
    (hconsts : stats.indConsts.size = dIdx)
    (hindicesExact : stats.nindices.toList = metadata.map Prod.fst)
    (hconstsExact : stats.indConsts =
      ((skeleton.types.take dIdx).map fun type =>
        .const type.name stats.levels).toArray)
    (hparams : stats.params.size = skeleton.nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats skeleton.nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hprefix : checkInductiveTypes.loopType.SynthesizedHeaderPrefix
      Hc.venv skeleton commonParams commonLevel metadata dIdx)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc commonParams depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {decl : VInductDecl}
      {depth' : Nat},
      (Hc' : ContextWF c') →
      c'.env = c.env →
      c'.lparams = c.lparams →
      TrInductDeclHeaders Hc'.venv c'.lparams skeleton.nparams
        indTypes.toList isUnsafe decl envTypes →
      MaterializedHeaderResult Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats' decl depth' →
      (k stats' c').WF Q) :
    (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
      dIdx stats k c).WF Q := by
  by_cases hidx : dIdx < indTypes.size
  · have hnonempty : stats.indConsts.isEmpty = false := by
      cases hempty : stats.indConsts.isEmpty
      · rfl
      · have hzero : stats.indConsts.size = 0 := by
          simpa [Array.isEmpty] using hempty
        omega
    have htargetIdx : dIdx < skeleton.types.length := by
      rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeletonHeaders.types_length Hdecl]
      simpa using hidx
    have hname := Lean4Lean.VerifyInductive.TrInductDeclSkeletonHeaders.typeNameAt
      Hdecl dIdx (by simpa using hidx) htargetIdx
    have hname' : indTypes[dIdx].name = skeleton.types[dIdx].name := by
      simpa using hname
    apply laterStep.extendsPrefix k Q Hc Hdecl hidx hpositive hnonempty
      hparams Hcache Hsuffix Hprefix Hambient hcommon hconsume
    intro c' nindices resultSort resultLevel Hc' henv' hlparams' Hdecl'
      Hcache' Hsuffix' Hprefix' Hambient'
    apply laterSteps.materialize k Q Hc' Hdecl'
      (dIdx := dIdx + 1) (depth := depth + nindices)
      (stats := updatedStats stats stats.lctx resultSort false nindices
        indTypes[dIdx].name)
      (metadata := metadata ++ [(nindices, resultLevel)])
      (commonParams := commonParams) (commonLevel := commonLevel)
    · omega
    · omega
    · simpa [updatedStats, hlparams'] using hlevels
    · simpa [updatedStats, hlparams'] using hlevelParams
    · simp [updatedStats, hindices]
    · simp [updatedStats, hconsts]
    · simp [updatedStats, hindicesExact]
    · rw [List.take_succ_eq_append_getElem]
      · simp [updatedStats, hconstsExact, hname']
      · rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeletonHeaders.types_length Hdecl]
        simpa using hidx
    · simpa [updatedStats] using hparams
    · exact Hcache'
    · exact Hsuffix'
    · exact Hprefix'
    · exact Hambient'
    · simpa [updatedStats, hlparams'] using hcommon
    · exact hconsume
    · intro c'' stats'' decl depth'' Hc'' henv'' hlparams'' Hdecl'' Hresult
      exact Hfinish Hc'' (henv''.trans henv')
        (hlparams''.trans hlparams') Hdecl'' Hresult
  · have heq : dIdx = indTypes.size := by omega
    have htypes : skeleton.types.length = indTypes.size := by
      rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeletonHeaders.types_length Hdecl]
      simp
    have Hprefix' : checkInductiveTypes.loopType.SynthesizedHeaderPrefix
        Hc.venv skeleton commonParams commonLevel metadata
          skeleton.types.length := by
      simpa [heq, htypes] using Hprefix
    rcases Hprefix'.materializes with
      ⟨decl, hmaterialize, _⟩
    let Hheaders := Hprefix'.complete hmaterialize
    have hfields := VInductDeclSkeleton.materialize_fields hmaterialize
    have herase := VInductDeclSkeleton.materialize_toSkeleton hmaterialize
    have Hdecl' :=
      Lean4Lean.VerifyInductive.TrInductDeclSkeletonHeaders.materialized
        Hdecl hmaterialize
    apply checkInductiveTypes.loopInd.result.WF
      (k := k) (Q := Q) hidx hlevels
    · simpa [heq] using hindices
    · simpa [heq] using hconsts
    · exact hparams
    · apply Hfinish (depth' := depth) Hc rfl rfl Hdecl'
      refine {
        headers := Hheaders
        levels := ?_
        levelParams := hlevelParams
        uvars := ?_
        consts := ?_
        indices := ?_
        params := ?_
        paramFVars := Hcache.paramFVars
        parameterScope := Hsuffix.parameterDecls
        ambientScope := Hsuffix.ambientDecls
        scopeDecomposition := Hsuffix.context
        ambientLength := Hsuffix.prefixLength
        cachedScope := Hsuffix.cached
        runtimeScope :=
          checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
            Hc Hsuffix
        paramsContext := ?_
        narrowParams := ?_ }
      · exact hlevels.trans (Hdecl.uvars.symm.trans hfields.1.symm)
      · exact Hdecl.uvars.symm.trans hfields.1.symm
      · have hconstMap :
            (decl.types.map fun type => Expr.const type.name stats.levels) =
              (skeleton.types.map fun type =>
                Expr.const type.name stats.levels) := by
          have := congrArg (fun d : VInductDeclSkeleton =>
            d.types.map fun type => Expr.const type.name stats.levels) herase
          simpa [VInductDecl.toSkeleton, VInductiveType.toSkeleton,
            Function.comp_def] using this
        calc
          stats.indConsts =
              (skeleton.types.map fun type =>
                .const type.name stats.levels).toArray := by
            have hd : dIdx = skeleton.types.length := heq.trans htypes.symm
            simpa [hd] using hconstsExact
          _ = (decl.types.map fun type =>
                .const type.name stats.levels).toArray := by
            rw [hconstMap]
      · have hmetadata : metadata.map Prod.fst =
            decl.types.map (·.numIndices) := by
          have zipIndices : ∀ (types : List VInductiveTypeSkeleton)
              (data : List (Nat × VLevel)), data.length = types.length →
              (List.zipWith (fun type datum =>
                type.toVInductiveType datum.1 datum.2) types data).map
                  (·.numIndices) = data.map Prod.fst := by
            intro types data hlength
            induction types generalizing data with
            | nil => simpa using hlength
            | cons type types ih =>
              cases data with
              | nil => simp at hlength
              | cons datum data =>
                simp only [List.length_cons] at hlength
                change datum.1 ::
                    (List.zipWith (fun type datum =>
                      type.toVInductiveType datum.1 datum.2)
                      types data).map (·.numIndices) =
                    datum.1 :: data.map Prod.fst
                exact congrArg (List.cons datum.1) (ih data (by omega))
          have hmetadataLength :=
            VInductDeclSkeleton.materialize_length hmaterialize
          simp only [VInductDeclSkeleton.materialize] at hmaterialize
          split at hmaterialize
          · simp only [Option.some.injEq] at hmaterialize
            subst decl
            exact (zipIndices skeleton.types metadata hmetadataLength).symm
          · contradiction
        exact hindicesExact.trans hmetadata
      · have Hcache' : checkInductiveTypes.loopType.ParameterCachePrefix
            Hc.venv c.lparams Hc.mlctx.vlctx stats decl.nparams depth := by
          rw [hfields.2.1]
          exact Hcache
        exact Hcache'.complete
      · apply Hsuffix.paramsDefEq Hambient
        exact Hprefix.parameterCount.trans hparams.symm
      · rw [← checkInductiveTypes.loopType.cachedParamVars_eq_paramVars decl]
        have hsize : stats.params.size = decl.nparams := by
          exact hparams.trans hfields.2.1.symm
        simpa [hsize] using Hsuffix.narrowParams
termination_by indTypes.size - dIdx

def MaterializedHeaderResult.parameterSuffix
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MaterializedHeaderResult Hc.venv c.lparams Hc.mlctx.vlctx
      stats decl depth) :
    checkInductiveTypes.loopType.ParameterContextSuffix Hc stats depth where
  ambientDecls := H.ambientScope
  parameterDecls := H.parameterScope
  context := H.scopeDecomposition
  prefixLength := H.ambientLength
  cached := H.cachedScope
  narrowParams := by
    have hsize : stats.params.size = decl.nparams := by
      have hlength :=
        Lean4Lean.VerifyInductive.List.Forall₂.length_eq' H.narrowParams
      simpa [VInductDecl.paramVars] using hlength
    rw [hsize,
      checkInductiveTypes.loopType.cachedParamVars_eq_paramVars decl]
    exact H.narrowParams

/-- Extend a completed header result by one semantically verified ambient
declaration.  The cached common-parameter suffix is unchanged; only its
runtime embedding and the ambient depth advance.  This is the transport used
between mutual recursor frames. -/
def MaterializedHeaderResult.withAmbient
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MaterializedHeaderResult Hc.venv c.lparams Hc.mlctx.vlctx
      stats decl depth)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
    MaterializedHeaderResult Hc'.venv c.lparams Hc'.mlctx.vlctx
      stats decl (depth + 1) := by
  dsimp only
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
  let Hsuffix' := H.parameterSuffix.withIndex Hc
    (name := name) (bi := bi) htr hty
  let entry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty')
  let W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  have weakenParams : ∀ {sources targets},
      List.Forall₂ (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx)
        sources targets →
      List.Forall₂ (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
        sources (targets.map fun target => target.liftN 1 0) := by
    intro sources targets Htranslated
    induction Htranslated with
    | nil => exact .nil
    | cons hsource _ ih =>
      exact .cons
        (hsource.weakFV Hc.checking.tr.wf.ordered W Hc'.mlctx_wf.tr.wf)
        ih
  have hparams := weakenParams H.params
  refine {
    headers := H.headers
    levels := H.levels
    levelParams := H.levelParams
    uvars := H.uvars
    consts := H.consts
    indices := H.indices
    params := ?_
    paramFVars := H.paramFVars
    parameterScope := H.parameterScope
    ambientScope := entry :: H.ambientScope
    scopeDecomposition := by
      change entry :: Hc.mlctx.vlctx =
        (entry :: H.ambientScope) ++ H.parameterScope
      simpa only [List.cons_append] using
        congrArg (entry :: ·) H.scopeDecomposition
    ambientLength := by simp [H.ambientLength]
    cachedScope := H.cachedScope
    runtimeScope :=
      checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
        Hc' Hsuffix'
    paramsContext := ?_
    narrowParams := ?_ }
  · have heq : (decl.paramVars depth).map (fun target =>
        target.liftN 1 0) = decl.paramVars (depth + 1) := by
      simp [VInductDecl.paramVars, VExpr.liftN]
      omega
    rw [← heq]
    exact hparams
  · exact H.paramsContext
  · exact H.narrowParams

/-- Complete the whole nonempty mutual-header phase, including the special
first header that establishes the common parameters and result universe. -/
theorem firstStep.materialize
    {skeleton : VInductDeclSkeleton}
    {envTypes : VEnv}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeletonHeaders Hc.venv c.lparams skeleton.nparams
      indTypes.toList isUnsafe skeleton envTypes)
    (hctx : Hc.mlctx.vlctx = [])
    (hidx : 0 < indTypes.size)
    (hempty : stats.indConsts.isEmpty = true)
    (hlevels : stats.levels.length = c.lparams.length)
    (hlevelParams : stats.levels = c.lparams.map .param)
    (hnindices : stats.nindices = #[])
    (hconsts : stats.indConsts = #[])
    (hparams : stats.params = #[])
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {decl : VInductDecl}
      {depth' : Nat},
      (Hc' : ContextWF c') →
      c'.env = c.env →
      c'.lparams = c.lparams →
      TrInductDeclHeaders Hc'.venv c'.lparams skeleton.nparams
        indTypes.toList isUnsafe decl envTypes →
      MaterializedHeaderResult Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats' decl depth' →
      (k stats' c').WF Q) :
    (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes 0
      stats k c).WF Q := by
  apply firstStep.initializesPrefix k Q Hc Hdecl hctx hidx hempty hparams
    hconsume
  intro c' stats' nindices resultSort resultLevel params Hc' henv' hlparams'
    hlevels' hnindices' hconsts' Hdecl' hofLevel Hcache' Hsuffix'
    Hprefix' Hambient'
  let statsNext := updatedStats stats' c'.lctx resultSort true nindices
    indTypes[0].name
  have hparamSize : stats'.params.size = skeleton.nparams := by
    have hlength :=
      Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hcache'.params
    simpa using hlength
  have hskeletonIdx : 0 < skeleton.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeletonHeaders.types_length Hdecl']
    simpa using hidx
  have hname := Lean4Lean.VerifyInductive.TrInductDeclSkeletonHeaders.typeNameAt
    Hdecl' 0 (by simpa using hidx) hskeletonIdx
  have hname' : indTypes[0].name = skeleton.types[0].name := by
    simpa using hname
  apply laterSteps.materialize k Q Hc' Hdecl'
    (dIdx := 1) (depth := nindices) (stats := statsNext)
    (metadata := [(nindices, resultLevel)])
    (commonParams := params) (commonLevel := resultLevel)
  · omega
  · omega
  · simpa [statsNext, updatedStats, hlevels', hlparams'] using hlevels
  · dsimp [statsNext]
    rw [updatedStats_levels, hlevels', hlevelParams, hlparams']
  · simp [statsNext, updatedStats, hnindices', hnindices]
  · simp [statsNext, updatedStats, hconsts', hconsts]
  · simp [statsNext, updatedStats, hnindices', hnindices]
  · rw [List.take_succ_eq_append_getElem hskeletonIdx]
    simp [statsNext, updatedStats, hconsts', hconsts, hname']
  · simpa [statsNext, updatedStats] using hparamSize
  · exact Hcache'.reindex (by simp [statsNext, updatedStats])
  · exact Hsuffix'.reindex (by simp [statsNext, updatedStats])
  · exact Hprefix'
  · exact Hambient'
  · simpa [statsNext, updatedStats] using hofLevel
  · exact hconsume
  · intro c'' stats'' decl depth'' Hc'' henv'' hlparams'' Hdecl'' Hresult
    exact Hfinish Hc'' (henv''.trans henv')
      (hlparams''.trans hlparams') Hdecl'' Hresult

/-- Public verifier for the executable mutual-header checker.  Successful
checking returns a materialized abstract declaration, its source translation,
and the independent header specification certificate to the continuation. -/
theorem checkInductiveTypes.materialize
    {skeleton : VInductDeclSkeleton}
    {envTypes : VEnv}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeletonHeaders Hc.venv c.lparams skeleton.nparams
      indTypes.toList isUnsafe skeleton envTypes)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < indTypes.size)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {decl : VInductDecl}
      {depth : Nat},
      (Hc' : ContextWF c') →
      c'.env = c.env →
      c'.lparams = c.lparams →
      TrInductDeclHeaders Hc'.venv c'.lparams skeleton.nparams
        indTypes.toList isUnsafe decl envTypes →
      MaterializedHeaderResult Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats' decl depth →
      (k stats' c').WF Q) :
    (AddInductive.checkInductiveTypes skeleton.nparams indTypes k c).WF Q := by
  change (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
    0 { (default : AddInductive.InductiveStats) with
      levels := c.lparams.map .param } k c).WF Q
  apply firstStep.materialize k Q Hc Hdecl hctx hnonempty
  · rfl
  · simp
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hconsume
  · exact Hfinish

/-- Indexed declaration-facing form of `stepPrefix.WF`.  Besides the checked
source translation, the continuation receives the exact corresponding
abstract mutual header and the environment obtained by installing all header
constants. -/
theorem stepPrefix.refinesTrInduct
    {decl : VInductDecl}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDecl Hc.venv c.lparams nparams
      indTypes.toList isUnsafe decl)
    (hidx : dIdx < indTypes.size)
    (Hloop : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        indTypes[dIdx].type checkedType type' checkedType' →
      ∀ envTypes,
        Hc.venv.addConstVals decl.typeConstants = some envTypes →
        ∀ target,
        decl.types[dIdx]? = some target →
        TrInductiveType Hc.venv envTypes c.lparams
          indTypes[dIdx] target →
      ∀ normalized,
        FVarsBelow Hc.mlctx.vlctx indTypes[dIdx].type normalized →
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized type' →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized 0 0
          c.fuel.inductiveFuel (fun type stats nindices =>
            show AddInductive.M _ from do
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
  have htarget : dIdx < decl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDecl.types_length Hdecl]
    simpa using hidx
  rcases Lean4Lean.VerifyInductive.TrInductDecl.typeAt Hdecl dIdx
      (by simpa using hidx) htarget with
    ⟨envTypes, htypes, htargetTr⟩
  apply stepPrefix.WF (nparams := nparams) (stats := stats) (k := k)
    (Q := Q) Hc hidx
  intro checkedType type' checkedType' hchecked normalized hscope hnormalized
  exact Hloop checkedType type' checkedType' hchecked envTypes htypes
    decl.types[dIdx] (by simp [htarget]) (by simpa using htargetTr)
    normalized hscope hnormalized

end checkInductiveTypes.loopInd


end VerifyInductive
end Lean4Lean
