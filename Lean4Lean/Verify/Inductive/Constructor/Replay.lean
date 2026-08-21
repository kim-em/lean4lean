import Lean4Lean.Verify.Inductive.Recursor.Structure

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
          TrExprS Hc.venv c.lparams tailScope tail tailTarget ∧
          ConstructorTailCertificate Hc.venv decl target
            tailScope.toCtx 0 tailTarget ∧
          TrSourceConstRaw Hc.venv c.lparams source.ctors[i].name
            source.ctors[i].type target.ctors[i] ∧
          Nonempty
            (checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
              Hc.venv c.lparams
              (constructorTelescopeTarget target.ctors[i]) tailScope
              tailTarget stats.params.size 0) ∧
          decl.CtorShape envTypes params target target.ctors[i] ∧
          envTypes.IsType decl.uvars [] target.ctors[i].type)
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
        ⟨tail, tailTarget, Hparam, Htranslated, Htail, HctorNarrow,
          Hsynthesis, HctorShape, HctorType⟩
      have HtailReplay : CheckedConstructorTailReplayAt Hc.venv c.lparams
          tailScope stats decl target source.ctors[ctorIdx] :=
        ⟨target.ctors[ctorIdx], tail, tailTarget,
          List.getElem_mem htarget, HctorNarrow, Hparam, Htranslated, Htail,
          Hsynthesis⟩
      exact refinesTypeWithReplay Q Hc Htarget
        (Hprefix.push htarget HctorShape HctorType)
        (Hreplay.push hidx Hparam) (Htails.push hidx HtailReplay)
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
          TrExprS Hc.venv c.lparams tailScope tail tailTarget ∧
          ConstructorTailCertificate Hc.venv decl decl.types[targetIdx]
            tailScope.toCtx 0 tailTarget ∧
          TrSourceConstRaw Hc.venv c.lparams
            indTypes[targetIdx].ctors[i].name
            indTypes[targetIdx].ctors[i].type
            decl.types[targetIdx].ctors[i] ∧
          Nonempty
            (checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
              Hc.venv c.lparams
              (constructorTelescopeTarget
                decl.types[targetIdx].ctors[i]) tailScope tailTarget
              stats.params.size 0) ∧
          decl.CtorShape envTypes params decl.types[targetIdx]
            decl.types[targetIdx].ctors[i] ∧
          envTypes.IsType decl.uvars [] decl.types[targetIdx].ctors[i].type)
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
        simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Htypes
      omega
    have Htarget : TrInductiveTypeHeaders sourceEnv envTypes c.lparams
        indTypes[targetIdx] decl.types[targetIdx] := by
      have Htarget' := Lean4Lean.VerifyInductive.List.Forall₂.getElem Htypes
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
        simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Htypes
      have := Hprefix.covered
      omega
    apply result.WF (Q := Q) hidx
    apply Hfinish
    · have hlength : indTypes.size = decl.types.length := by
        simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Htypes
      simpa [heq, hlength] using Hprefix
    · simpa [heq] using Hreplays
    · simpa [heq] using Htails
termination_by indTypes.size - targetIdx

end checkConstructors.loopTypes

/-- Constructor-checking output needed by both declaration installation and
recursor replay.  The first component is the abstract formation certificate;
the second retains the exact concrete parameter tails for production
constructors. -/
structure CheckedConstructorsResult
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
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hparams : Hmaterialized.headers.params = params)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ targetIdx (hi : targetIdx < decl.types.length)
      fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      decl.types[targetIdx].resultLevel ≈ .zero ∨
        fieldLevel' ≤ decl.types[targetIdx].resultLevel) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0 c).WF
      (fun _ => CheckedConstructorsResult sourceEnv decl Hc.venv
        params stats indTypes c.lparams Hmaterialized.parameterScope) := by
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
    simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Htypes
  apply checkConstructors.loopTypes.refinesBlockWithReplay
    (Q := fun _ => CheckedConstructorsResult sourceEnv decl Hc.venv
      params stats indTypes c.lparams Hmaterialized.parameterScope)
    Hc Htypes (ConstructorTypesPrefix.empty Hc.venv decl params)
    (ConstructorParamPrefixRows.empty stats indTypes)
    (ConstructorTailReplayRows.empty Hc.venv c.lparams
      Hmaterialized.parameterScope stats decl indTypes hindTypesSize)
  · intro targetIdx hsource htarget ctorIdx hctorSource hctorTarget
      Hctor checkedType fullType checkedType' hchecked
    have Htarget : TrInductiveTypeHeaders sourceEnv Hc.venv c.lparams
        indTypes[targetIdx] decl.types[targetIdx] := by
      have Htarget' := Lean4Lean.VerifyInductive.List.Forall₂.getElem Htypes
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
      (fuel := c.fuel.inductiveFuel) Hc Hsuffix Hstats hparamsCtx
      Hctor hchecked htarget rfl htargetUvars htargetLookup htargetWF
      htargetShape hconsume hlit hproj hunsafe (hbound targetIdx htarget)
    exact Hchecked.mono fun _ Hresult => by
      rcases Hresult with
        ⟨tail, tailTarget, Hprefix, Htranslated, HtailCertificate,
          Hsynthesis, Hshape, Htype⟩
      exact ⟨tail, tailTarget, Hprefix, Htranslated, HtailCertificate,
        Hctor, Hsynthesis, Hshape, Htype⟩
  · intro Hcomplete Hreplays Htails
    exact {
      checked := Hcomplete.checkedComplete (env := sourceEnv)
      parameterPrefixes := Hreplays.complete
      constructorTails := Htails.complete }

@[simp] theorem VInductDecl.recursorName_eq_mkRecName
    (decl : VInductDecl) (type : VInductiveType) :
    decl.recursorName type = Lean.mkRecName type.name := rfl

/-- The production choice of an extra eliminator universe has exactly the two
universe arities admitted by `RecursorShape`. -/
theorem AddInductive.getRecLevelParams_length :
    (AddInductive.getRecLevelParams elimLevel lparams).length = lparams.length ∨
    (AddInductive.getRecLevelParams elimLevel lparams).length =
      lparams.length + 1 := by
  cases elimLevel with
  | param u => simp [AddInductive.getRecLevelParams]
  | _ => simp [AddInductive.getRecLevelParams]

theorem AddInductive.getRecLevelParams_length_of_param
    (h : elimLevel.isParam = true) :
    (AddInductive.getRecLevelParams elimLevel lparams).length =
      lparams.length + 1 := by
  cases elimLevel <;> simp_all [AddInductive.getRecLevelParams, Level.isParam]

theorem AddInductive.getRecLevelParams_length_of_not_param
    (h : elimLevel.isParam = false) :
    (AddInductive.getRecLevelParams elimLevel lparams).length =
      lparams.length := by
  cases elimLevel <;> simp_all [AddInductive.getRecLevelParams, Level.isParam]

/-- Universe-level side condition required by recursor-frame semantics.  A
small eliminator uses `0`; a large eliminator uses a parameter fresh for the
inductive declaration.  Other level syntax is never produced by
`getElimLevel`. -/
def AddInductive.AdmissibleElimLevel (lparams : List Name) : Level → Prop
  | .zero => True
  | .param name => name ∉ lparams
  | _ => False

theorem AddInductive.getElimLevel.loop.WF
    (lparams : List Name) (candidate : Name) (i fuel : Nat)
    (c : AddInductive.Context) :
    (AddInductive.getElimLevel.loop lparams candidate i fuel c).WF
      fun level => ∃ name, level = .param name ∧ name ∉ lparams := by
  induction fuel generalizing candidate i with
  | zero =>
    rw [AddInductive.getElimLevel.loop]
    exact Except.WF.throw
  | succ fuel ih =>
    rw [AddInductive.getElimLevel.loop]
    by_cases hcontains : lparams.contains candidate = true
    · rw [if_pos hcontains]
      exact ih _ _
    · have hnotMem : candidate ∉ lparams := by
        intro hmem
        exact hcontains (List.contains_iff_mem.mpr hmem)
      have hp : (pure (Level.param candidate) :
          Except Exception Level).WF
          (fun level => ∃ name, level = .param name ∧ name ∉ lparams) :=
        Except.WF.pure ⟨candidate, rfl, hnotMem⟩
      rw [if_neg hcontains]
      exact hp

/-- The production eliminator-level search returns only a small eliminator
level or a parameter fresh for the declaration's existing universe list. -/
theorem AddInductive.getElimLevel.WF
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (c : AddInductive.Context) :
    (AddInductive.getElimLevel stats indTypes c).WF
      (AddInductive.AdmissibleElimLevel c.lparams) := by
  unfold AddInductive.getElimLevel
  have Hlarge : (AddInductive.isLargeEliminator stats indTypes c).WF
      (fun _ => True) := fun _ _ => trivial
  refine Hlarge.bind fun large _ => ?_
  cases large with
  | false =>
    exact Except.WF.pure trivial
  | true =>
    have hread : ((readThe AddInductive.Context :
        AddInductive.M AddInductive.Context) c).WF (fun c' => c' = c) := by
      intro c' h
      cases h
      rfl
    refine readerBind.WF (x := readThe AddInductive.Context) hread
      fun c' hc' => ?_
    subst c'
    exact (AddInductive.getElimLevel.loop.WF c.lparams `u 1
      (c.lparams.length + 1) c).mono fun level Hlevel => by
        rcases Hlevel with ⟨name, rfl, hfresh⟩
        exact hfresh

/-- An admissible eliminator level is well formed under the exact universe
parameter list later assigned to generated recursors. -/
theorem AddInductive.AdmissibleElimLevel.ofLevel
    (H : AddInductive.AdmissibleElimLevel lparams elimLevel) :
    ∃ level, VLevel.ofLevel
      (AddInductive.getRecLevelParams elimLevel lparams) elimLevel =
        some level := by
  cases elimLevel with
  | zero => exact ⟨.zero, rfl⟩
  | param name =>
    exact ⟨.param 0, by
      simp [AddInductive.getRecLevelParams, VLevel.ofLevel]⟩
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at H

/-- Adding the fresh large-elimination parameter preserves the kernel's
no-duplicate universe-parameter invariant.  The small-elimination case leaves
the declaration's universe list unchanged. -/
theorem AddInductive.AdmissibleElimLevel.recLevelParamsNodup
    (H : AddInductive.AdmissibleElimLevel lparams elimLevel)
    (hlparams : lparams.Nodup) :
    (AddInductive.getRecLevelParams elimLevel lparams).Nodup := by
  cases elimLevel with
  | zero => simpa [AddInductive.getRecLevelParams] using hlparams
  | param name =>
    simpa [AddInductive.getRecLevelParams] using List.nodup_cons.mpr
      ⟨H, hlparams⟩
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at H

/-- The recursor universe list is obtained by prepending at most the one fresh
large-elimination parameter.  This positional fact is kept explicit because
old declaration levels must later be reinterpreted beneath that prefix. -/
theorem AddInductive.AdmissibleElimLevel.recLevelParamsDecomposition
    (H : AddInductive.AdmissibleElimLevel lparams elimLevel) :
    ∃ pre : List Name, pre.length ≤ 1 ∧
      AddInductive.getRecLevelParams elimLevel lparams = pre ++ lparams := by
  cases elimLevel with
  | zero => exact ⟨[], by simp [AddInductive.getRecLevelParams]⟩
  | param name =>
    exact ⟨[name], by simp [AddInductive.getRecLevelParams]⟩
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at H

/-- Independent semantic seed for the codomain of every generated motive.
The concrete sort is interpreted under the exact universe list assigned to
the generated recursor, without consulting `checkRecursorTypes`. -/
theorem AddInductive.AdmissibleElimLevel.sortType
    (H : AddInductive.AdmissibleElimLevel lparams elimLevel) :
    ∃ level,
      TrExprS env (AddInductive.getRecLevelParams elimLevel lparams) Δ
        (.sort elimLevel) (.sort level) ∧
      env.IsType
        (AddInductive.getRecLevelParams elimLevel lparams).length
        Δ.toCtx (.sort level) := by
  rcases H.ofLevel with ⟨level, hlevel⟩
  refine ⟨level, TrExprS.sort hlevel, ?_⟩
  exact ⟨.succ level, VEnv.HasType.sort (.of_ofLevel hlevel)⟩

/-- Uniform entry into recursor-universe semantics for the exact two cases
produced by `getElimLevel`. -/
def ContextWF.toAdmissibleRecursorContextWF
    (H : ContextWF c)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    RecursorContextWF c
      (AddInductive.getRecLevelParams elimLevel c.lparams) := by
  cases elimLevel with
  | zero =>
    simpa [AddInductive.getRecLevelParams] using H.toRecursorContextWF
  | param name =>
    simpa [AddInductive.getRecLevelParams] using
      H.prependRecursorLevelParam Helim
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

@[simp] theorem ContextWF.toAdmissibleRecursorContextWF_venv
    (H : ContextWF c)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    (H.toAdmissibleRecursorContextWF Helim).venv = H.venv := by
  cases elimLevel with
  | zero => rfl
  | param name => rfl
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- Exact cached-parameter suffix after the local context has moved to the
recursor universe list.  The declaration itself still has `decl.uvars`
universes; this invariant deliberately mentions only the translations that
remain meaningful after the optional fresh eliminator parameter is prepended.
Generated major and motive locals accumulate in `ambientDecls`, while later
family replay starts from the unchanged `parameterDecls` suffix. -/
structure RecursorParameterContextSuffix
    {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    (stats : AddInductive.InductiveStats) (depth : Nat) : Type where
  ambientDecls : VLCtx
  parameterDecls : VLCtx
  context : R.mlctx.vlctx = ambientDecls ++ parameterDecls
  prefixLength : ambientDecls.length = depth
  cached : List.Forall₂
    checkInductiveTypes.loopType.CachedParameterDecl
    stats.params.toList.reverse parameterDecls
  narrowParams : List.Forall₂
    (TrExprS R.venv recLparams parameterDecls)
    stats.params.toList
    (checkInductiveTypes.loopType.cachedParamVars stats.params.size 0)

/-- The cached parameter suffix is independently well formed after dropping
the ambient declarations that precede it in the recursor context. -/
theorem RecursorParameterContextSuffix.parameterWF
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : RecursorParameterContextSuffix R stats depth) :
    VLCtx.WF R.venv recLparams.length H.parameterDecls := by
  have dropPrefix : ∀ (added suffix : VLCtx),
      VLCtx.WF R.venv recLparams.length (added ++ suffix) →
        VLCtx.WF R.venv recLparams.length suffix := by
    intro added
    induction added with
    | nil => intro suffix Hwf; simpa using Hwf
    | cons decl tail ih =>
      intro suffix Hwf
      exact ih suffix Hwf.1
  have Hwf := R.mlctx_wf.tr.wf
  rw [H.context] at Hwf
  exact dropPrefix H.ambientDecls H.parameterDecls Hwf

theorem VEnv.IsDefEqCtx.instL
    (hls : ∀ level ∈ levels, level.WF U') :
    ∀ {base left right},
      VEnv.IsDefEqCtx env U base left right →
      VEnv.IsDefEqCtx env U'
        (base.map (VExpr.instL levels))
        (left.map (VExpr.instL levels))
        (right.map (VExpr.instL levels))
  | _, _, _, .zero => .zero
  | _, _, _, .succ hctx htype =>
    .succ (VEnv.IsDefEqCtx.instL hls hctx) (htype.instL hls)

theorem _root_.Lean4Lean.VLCtx.WF.mono
    {env env' : VEnv} (henv : env ≤ env') :
    ∀ {scope : VLCtx}, VLCtx.WF env U scope → VLCtx.WF env' U scope
  | [], H => H
  | (ofv, decl) :: scope, ⟨Hscope, Hfresh, Hdecl⟩ => by
    refine ⟨VLCtx.WF.mono henv Hscope, Hfresh, ?_⟩
    cases decl with
    | vlam type => exact Hdecl.mono henv
    | vlet type value => exact Hdecl.mono henv

/-- Universe-instantiated view of a synthesized header target.  The stored
constant arity and identity are unchanged; only the type interpreted under
the new universe context is substituted. -/
def _root_.Lean4Lean.VInductiveTypeSkeleton.instL
    (target : VInductiveTypeSkeleton) (levels : List VLevel) :
    VInductiveTypeSkeleton :=
  { target with type := target.type.instL levels }

@[simp] theorem _root_.Lean4Lean.VExpr.instL_wrapForalls
    (domains : List VExpr) (result : VExpr) (levels : List VLevel) :
    (VExpr.wrapForalls domains result).instL levels =
      VExpr.wrapForalls (domains.map (VExpr.instL levels))
        (result.instL levels) := by
  induction domains with
  | nil => rfl
  | cons domain domains ih =>
    exact congrArg (VExpr.forallE (domain.instL levels)) ih

def checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate.mono
    {env env' : VEnv} (henv : env ≤ env')
    (H : checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
      env Us target scope current i nindices) :
    checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
      env' Us target scope current i nindices where
  params := H.params
  indices := H.indices
  parameterCount := H.parameterCount
  indexCount := H.indexCount
  scopeCtx := H.scopeCtx
  scopeWF := H.scopeWF.mono henv
  currentType := H.currentType.mono henv
  exprType := H.exprType
  header := H.header.mono henv

/-- Reinterpret an exact narrow telescope synthesis under an arbitrary
universe substitution.  This is the semantic bridge used by constructor
replay when large elimination prepends its fresh universe parameter. -/
noncomputable def
    checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate.instL
    {Us' : List Name}
    (hlevels : ∀ level ∈ levels, level.WF Us'.length)
    (hlength : levels.length = Us.length)
    (H : checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
      env Us target scope current i nindices) :
    checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
      env Us'
      (target.instL levels) (scope.instL levels) (current.instL levels)
      i nindices where
  params := H.params.map (VExpr.instL levels)
  indices := H.indices.map (VExpr.instL levels)
  parameterCount := by simp [H.parameterCount]
  indexCount := by simp [H.indexCount]
  scopeCtx := by
    simpa [VLCtx.instL_toCtx, List.map_append, List.map_reverse,
      Function.comp_def] using
      congrArg (List.map (VExpr.instL levels)) H.scopeCtx
  scopeWF := by
    have hsource : VLCtx.WF env levels.length scope := by
      simpa [hlength] using H.scopeWF
    exact hsource.instL hlevels
  currentType := by
    have hsource : env.IsType levels.length scope.toCtx current := by
      simpa [hlength] using H.currentType
    simpa [VLCtx.instL_toCtx] using hsource.instL hlevels
  exprType := H.exprType.instL levels
  header := by
    have hsource : env.IsDefEq levels.length [] target.type
        (VExpr.wrapForalls (H.params ++ H.indices) current) H.exprType := by
      simpa [hlength] using H.header
    simpa [VInductiveTypeSkeleton.instL, List.map_append] using
      hsource.instL hlevels

/-- Applying an installed constant to the canonical variables of an exact
narrow parameter synthesis produces the retained residual tail type. -/
theorem checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate.canonicalApplication
    {ctorVal : VConstVal} {levels : List VLevel}
    (H : checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
      env Us target scope current i 0)
    (henv : env.WF)
    (hlookup : env.constants ctorVal.name = some ctorVal.toVConstant)
    (hlevels : ∀ level ∈ levels, level.WF Us.length)
    (hlength : levels.length = ctorVal.uvars)
    (htarget : ctorVal.type.instL levels = target.type) :
    env.HasType Us.length scope.toCtx
      (VExpr.mkApps (.const ctorVal.name levels)
        (recursorCanonicalVars H.params.length)) current := by
  have hindices : H.indices = [] :=
    List.eq_nil_of_length_eq_zero H.indexCount
  have hconst := VEnv.HasType.const (Γ := []) hlookup hlevels hlength
  have hhead : env.HasType Us.length []
      (.const ctorVal.name levels) target.type := by
    simpa [htarget] using hconst
  have htelescope : env.HasType Us.length []
      (.const ctorVal.name levels)
      (VExpr.wrapForalls H.params current) := by
    apply hhead.defeqU_r henv (by trivial)
    exact ⟨H.exprType, by simpa [hindices] using H.header⟩
  have happ := VEnv.HasType.mkApps_wrapForalls_canonical
    henv.ordered htelescope
  simpa [hindices, H.scopeCtx, recursorCanonicalVars,
    VExpr.liftN] using happ

/-- Rebase the independently checked parameter suffix into the exact
recursor universe context.  In the small-elimination case this is identity;
in the large-elimination case concrete declarations and free-variable names
are unchanged and their abstract types are shifted by one universe slot. -/
def checkInductiveTypes.loopType.ParameterContextSuffix.toRecursorContext
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : checkInductiveTypes.loopType.ParameterContextSuffix Hc stats depth)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    let R := Hc.toAdmissibleRecursorContextWF Helim
    RecursorParameterContextSuffix R stats depth := by
  dsimp only
  cases elimLevel with
  | zero =>
    exact {
      ambientDecls := H.ambientDecls
      parameterDecls := H.parameterDecls
      context := H.context
      prefixLength := H.prefixLength
      cached := H.cached
      narrowParams := H.narrowParams }
  | param fresh =>
    let shift := VLevel.prependShift c.lparams.length
    have hcached : List.Forall₂
        checkInductiveTypes.loopType.CachedParameterDecl
        stats.params.toList.reverse (H.parameterDecls.instL shift) := by
      have go : ∀ {params : List Expr} {entries : VLCtx},
          List.Forall₂ checkInductiveTypes.loopType.CachedParameterDecl
              params entries →
          List.Forall₂ checkInductiveTypes.loopType.CachedParameterDecl
              params (entries.instL shift) := by
        intro params entries Hcached
        induction Hcached with
        | nil => exact .nil
        | @cons param entry params entries hentry _ ih =>
          rcases hentry with ⟨fv, deps, type, rfl, rfl⟩
          exact .cons ⟨fv, deps, type.instL shift, rfl, by
            simp [VLCtx.instL, VLocalDecl.instL]⟩ ih
      exact go H.cached
    have hnarrow : List.Forall₂
        (TrExprS Hc.venv (fresh :: c.lparams)
          (H.parameterDecls.instL shift))
        stats.params.toList
        (checkInductiveTypes.loopType.cachedParamVars stats.params.size 0) := by
      have go : ∀ {sources targets},
          List.Forall₂ (TrExprS Hc.venv c.lparams H.parameterDecls)
              sources targets →
          List.Forall₂ (TrExprS Hc.venv (fresh :: c.lparams)
              (H.parameterDecls.instL shift))
            sources (targets.map fun target => target.instL shift) := by
        intro sources targets Htranslated
        induction Htranslated with
        | nil => exact .nil
        | cons hsource _ ih =>
          exact .cons
            (by
              simpa [shift] using
                (hsource.prependLevelParam Hc.checking.tr.wf
                  ((checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
                    Hc H).scopeWF Hc.checking.tr.wf) Helim))
            ih
      have hshifted := go H.narrowParams
      have htargets :
          (checkInductiveTypes.loopType.cachedParamVars
              stats.params.size 0).map (fun target => target.instL shift) =
            checkInductiveTypes.loopType.cachedParamVars
              stats.params.size 0 := by
        induction stats.params.size with
        | zero => rfl
        | succ n ih =>
          rw [checkInductiveTypes.loopType.cachedParamVars_succ,
            List.map_append, List.map_map]
          congr 1
          · rw [show
                (fun target : VExpr => target.instL shift) ∘
                    (fun target : VExpr => target.liftN 1 0) =
                  (fun target : VExpr =>
                    (target.instL shift).liftN 1 0) by
                funext target
                simpa [Function.comp_apply] using
                  (VExpr.instL_liftN (e := target) (n := 1)
                    (k := 0) (ls := shift))]
            simpa [List.map_map] using congrArg
              (List.map fun target : VExpr => target.liftN 1 0) ih
      rw [htargets] at hshifted
      exact hshifted
    exact {
      ambientDecls := H.ambientDecls.instL shift
      parameterDecls := H.parameterDecls.instL shift
      context := by
        have hcontext := congrArg (fun Δ : VLCtx => Δ.instL shift) H.context
        change (Hc.mlctx.prependLevelParam c.lparams.length).vlctx =
          H.ambientDecls.instL shift ++ H.parameterDecls.instL shift
        simpa only [TypeChecker.MLCtx.prependLevelParam_vlctx,
          shift, VLCtx.instL_eq_map, List.map_append] using hcontext
      prefixLength := by
        rw [VLCtx.instL_eq_map, List.length_map, H.prefixLength]
      cached := hcached
      narrowParams := hnarrow }
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- The exact constructor telescope target as interpreted by generated
recursor code. -/
def recursorConstructorTelescopeTarget
    (ctorVal : VConstVal)
    (Helim : AddInductive.AdmissibleElimLevel lparams elimLevel) :
    VInductiveTypeSkeleton :=
  match elimLevel with
  | .zero => constructorTelescopeTarget ctorVal
  | .param _ => (constructorTelescopeTarget ctorVal).instL
      (VLevel.prependShift lparams.length)
  | .succ _ | .max _ _ | .imax _ _ | .mvar _ => False.elim Helim

def recursorDeclarationAbstractLevels
    (lparams : List Name)
    (Helim : AddInductive.AdmissibleElimLevel lparams elimLevel) :
    List VLevel :=
  match elimLevel with
  | .zero => VLevel.params lparams.length
  | .param _ => (VLevel.params lparams.length).map
      (VLevel.inst (VLevel.prependShift lparams.length))
  | .succ _ | .max _ _ | .imax _ _ | .mvar _ => False.elim Helim

theorem List.map_param_idxOf_eq_params
    {names : List Name} (H : names.Nodup) :
    names.map (fun name => VLevel.param (names.idxOf name)) =
      VLevel.params names.length := by
  apply List.ext_getElem
  · simp [VLevel.params]
  · intro i hleft hright
    have hi : i < names.length := by
      simpa [VLevel.params] using hright
    simp [VLevel.params, H.idxOf_getElem i hi]

theorem checkInductiveTypes.loopInd.MaterializedHeaderResult.recursorLevelTranslation
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : checkInductiveTypes.loopInd.MaterializedHeaderResult
      Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hlparams : c.lparams.Nodup)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    stats.levels.mapM (VLevel.ofLevel
      (AddInductive.getRecLevelParams elimLevel c.lparams)) =
      some (recursorDeclarationAbstractLevels c.lparams Helim) := by
  cases elimLevel with
  | zero =>
    simpa [AddInductive.getRecLevelParams,
      recursorDeclarationAbstractLevels,
      List.map_param_idxOf_eq_params hlparams] using H.levelTranslation
  | param fresh =>
    have hshifted := VLevel.mapM_ofLevel_fresh_cons Helim H.levelTranslation
    simpa [AddInductive.getRecLevelParams,
      recursorDeclarationAbstractLevels,
      List.map_param_idxOf_eq_params hlparams] using hshifted
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- The complete concrete universe list attached to a generated recursor
translates to the identity instantiation of its exact recursor universe
context.  For large elimination this prepends the fresh eliminator level to
the shifted declaration levels. -/
theorem
    checkInductiveTypes.loopInd.MaterializedHeaderResult.recursorLevelsTranslation
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : checkInductiveTypes.loopInd.MaterializedHeaderResult
      Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hlparams : c.lparams.Nodup)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    (AddInductive.getRecLevels elimLevel stats.levels).mapM
      (VLevel.ofLevel
        (AddInductive.getRecLevelParams elimLevel c.lparams)) =
      some (VLevel.params
        (AddInductive.getRecLevelParams elimLevel c.lparams).length) := by
  cases elimLevel with
  | zero =>
    simpa [AddInductive.getRecLevels, AddInductive.getRecLevelParams,
      recursorDeclarationAbstractLevels, Level.isParam] using
      H.recursorLevelTranslation hlparams Helim
  | param fresh =>
    have htail := H.recursorLevelTranslation hlparams Helim
    have hhead : VLevel.ofLevel (fresh :: c.lparams) (.param fresh) =
        some (.param 0) := by
      simp [VLevel.ofLevel]
    simp [AddInductive.getRecLevelParams,
      recursorDeclarationAbstractLevels] at htail
    simp only [AddInductive.getRecLevels, Level.isParam,
      ↓reduceIte, List.mapM_cons]
    simp only [AddInductive.getRecLevelParams]
    rw [hhead, htail]
    simp [VLevel.params, VLevel.prependShift]
    rw [List.range_succ_eq_map]
    simp [Function.comp_def, VLevel.inst]
    intro a ha
    simp [ha]
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

theorem recursorDeclarationAbstractLevels_wf
    (Helim : AddInductive.AdmissibleElimLevel lparams elimLevel) :
    ∀ level ∈ recursorDeclarationAbstractLevels lparams Helim,
      level.WF (AddInductive.getRecLevelParams elimLevel lparams).length := by
  cases elimLevel with
  | zero =>
    simpa [recursorDeclarationAbstractLevels,
      AddInductive.getRecLevelParams] using VLevel.params_wf
  | param fresh =>
    let shift := VLevel.prependShift lparams.length
    have hshift : ∀ level ∈ shift,
        level.WF (fresh :: lparams).length := by
      simpa [shift] using VLevel.prependShift_wf (n := lparams.length)
    intro level hlevel
    rw [recursorDeclarationAbstractLevels, List.mem_map] at hlevel
    rcases hlevel with ⟨sourceLevel, hsourceLevel, rfl⟩
    exact VLevel.WF.inst hshift
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

theorem recursorDeclarationAbstractLevels_length
    (Helim : AddInductive.AdmissibleElimLevel lparams elimLevel) :
    (recursorDeclarationAbstractLevels lparams Helim).length =
      lparams.length := by
  cases elimLevel with
  | zero => simp [recursorDeclarationAbstractLevels, VLevel.params]
  | param fresh =>
    simp [recursorDeclarationAbstractLevels, VLevel.params]
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

theorem VConstVal.type_instL_recursorDeclarationAbstractLevels
    (Hwf : ctorVal.toVConstant.WF env)
    (huvars : ctorVal.uvars = lparams.length)
    (Helim : AddInductive.AdmissibleElimLevel lparams elimLevel) :
    ctorVal.type.instL (recursorDeclarationAbstractLevels lparams Helim) =
      (recursorConstructorTelescopeTarget ctorVal Helim).type := by
  have hlevelWF : ctorVal.type.LevelWF ctorVal.uvars := by
    exact (Classical.choose_spec Hwf).levelWF (by trivial) |>.1
  cases elimLevel with
  | zero =>
    simpa [recursorDeclarationAbstractLevels,
      recursorConstructorTelescopeTarget, constructorTelescopeTarget,
      huvars] using hlevelWF.instL_id
  | param fresh =>
    let shift := VLevel.prependShift lparams.length
    have hid : ctorVal.type.instL (VLevel.params lparams.length) =
        ctorVal.type := by simpa [← huvars] using hlevelWF.instL_id
    rw [recursorDeclarationAbstractLevels,
      recursorConstructorTelescopeTarget, ← VExpr.instL_instL, hid]
    rfl
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- Rebase one retained constructor replay into the exact parameter scope
and universe list used at the start of recursor generation. -/
theorem CheckedConstructorTailReplayAt.toRecursorContext
    {c : AddInductive.Context} {Hc : ContextWF c}
    {sourceEnv : VEnv} {decl : VInductDecl}
    {target : VInductiveType} {source : Constructor}
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (H : CheckedConstructorTailReplayAt sourceEnv c.lparams
      Hmaterialized.parameterScope stats decl target source)
    (henv : sourceEnv ≤ Hc.venv)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    let R := Hc.toAdmissibleRecursorContextWF Helim
    let Hsuffix := Hmaterialized.parameterSuffix.toRecursorContext Helim
    ∃ ctorVal tail tailTarget,
      ctorVal ∈ target.ctors ∧
      ctorVal.name = source.name ∧
      ctorVal.uvars = c.lparams.length ∧
      RecursorParamPrefix stats 0 source.type tail ∧
      TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Hsuffix.parameterDecls tail tailTarget ∧
      R.venv.IsType
        (AddInductive.getRecLevelParams elimLevel c.lparams).length
        Hsuffix.parameterDecls.toCtx tailTarget ∧
      Nonempty
        (checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
          (recursorConstructorTelescopeTarget ctorVal Helim)
          Hsuffix.parameterDecls tailTarget stats.params.size 0) := by
  rcases H with
    ⟨ctorVal, tail, tailTarget, hmem, Hraw, Hprefix, Htranslated,
      Htail, Hsynthesis⟩
  rcases Hsynthesis with ⟨Hsynthesis⟩
  dsimp only
  cases elimLevel with
  | zero =>
    refine ⟨ctorVal, tail, tailTarget, hmem, Hraw.name, Hraw.uvars,
      Hprefix, ?_, ?_, ?_⟩
    · change TrExprS Hc.venv c.lparams Hmaterialized.parameterScope
        tail tailTarget
      exact Htranslated.mono henv
    · change Hc.venv.IsType c.lparams.length
        Hmaterialized.parameterScope.toCtx tailTarget
      simpa [Hmaterialized.uvars] using Htail.isType.mono henv
    · refine ⟨?_⟩
      change checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
        Hmaterialized.parameterScope tailTarget stats.params.size 0
      exact Hsynthesis.mono henv
  | param fresh =>
    let shift := VLevel.prependShift c.lparams.length
    have hshift : ∀ level ∈ shift,
        level.WF (fresh :: c.lparams).length := by
      simpa [shift] using VLevel.prependShift_wf (n := c.lparams.length)
    have hshiftLength : shift.length = c.lparams.length := by
      simp [shift, VLevel.prependShift]
    have hscopeWF : Hmaterialized.parameterScope.WF
        Hc.venv c.lparams.length :=
      (checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
        Hc Hmaterialized.parameterSuffix).scopeWF Hc.checking.tr.wf
    refine ⟨ctorVal, tail, tailTarget.instL shift, hmem, Hraw.name,
      Hraw.uvars, Hprefix, ?_, ?_, ?_⟩
    · change TrExprS Hc.venv (fresh :: c.lparams)
        (Hmaterialized.parameterScope.instL shift) tail
        (tailTarget.instL shift)
      simpa [shift] using (Htranslated.mono henv).prependLevelParam
        Hc.checking.tr.wf hscopeWF Helim
    · have htype := (Htail.isType.mono henv).instL hshift
      change Hc.venv.IsType (fresh :: c.lparams).length
        (Hmaterialized.parameterScope.instL shift).toCtx
        (tailTarget.instL shift)
      simpa [VLCtx.instL_toCtx, shift, Hmaterialized.uvars] using htype
    · refine ⟨?_⟩
      change checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        Hc.venv (fresh :: c.lparams)
        ((constructorTelescopeTarget ctorVal).instL shift)
        (Hmaterialized.parameterScope.instL shift)
        (tailTarget.instL shift) stats.params.size 0
      simpa [shift] using
        (Hsynthesis.mono henv).instL hshift hshiftLength
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

theorem RecursorParameterContextSuffix.noIndConsts
    (H : RecursorParameterContextSuffix R stats depth)
    (names : List Name) :
    checkPositivityStep.VLCtx.NoIndConsts names H.parameterDecls := by
  have go : ∀ {params : List Expr} {entries : VLCtx},
      List.Forall₂ checkInductiveTypes.loopType.CachedParameterDecl
          params entries →
      checkPositivityStep.VLCtx.NoIndConsts names entries := by
    intro params entries hcached
    induction hcached with
    | nil =>
      intro v mapped type hfind
      simp [VLCtx.find?] at hfind
    | @cons param entry params entries hentry _ ih =>
      rcases hentry with ⟨fv, deps, type, rfl, rfl⟩
      exact checkPositivityStep.VLCtx.NoIndConsts.cons ih rfl
  intro v mapped type hfind
  exact go H.cached hfind

/-- Recover the narrow semantic parameter scope embedded in the complete
universe-rebased runtime context. -/
def RecursorParameterContextSuffix.runtimeScope
    {c : AddInductive.Context}
    {R : RecursorContextWF c recLparams}
    (H : RecursorParameterContextSuffix R stats depth) :
    checkInductiveTypes.loopType.NarrowRuntimeScope
      R.venv recLparams H.parameterDecls R.mlctx.vlctx := by
  have hambient : H.ambientDecls.NoBV := by
    apply VLCtx.NoBV.leftOfAppend H.ambientDecls H.parameterDecls
    rw [← H.context]
    exact R.mlctx.noBV
  let W := VLCtx.FVLift.to_append H.parameterDecls hambient
  refine {
    expanded := R.mlctx.vlctx
    shift := .skipN .refl H.ambientDecls.toCtx.length
    lift := ?_
    frontSourceDomains := []
    frontExpandedDomains := []
    front := ?_
    context := .refl R.checking.tr.wf R.mlctx_wf.tr.wf
    upset := ?_
    noBV := ?_
    noIndConsts := H.noIndConsts }
  · rw [H.context]
    exact W.toFVLift'
  · exact .zero (by
      rw [H.context]
      exact W.toFVLift')
  · have hwf : VLCtx.WF R.venv recLparams.length
        (H.ambientDecls ++ H.parameterDecls) := by
      rw [← H.context]
      exact R.mlctx_wf.tr.wf
    simpa [H.context] using
      (IsFVarUpSet.suffixFVars H.parameterDecls H.ambientDecls hwf)
  · have hfull : (H.ambientDecls ++ H.parameterDecls).NoBV := by
      rw [← H.context]
      exact R.mlctx.noBV
    change H.parameterDecls.bvars = 0
    change (H.ambientDecls ++ H.parameterDecls).bvars = 0 at hfull
    rw [VLCtx.bvars_append] at hfull
    omega

/-- Any generated recursor local extends only the ambient prefix.  The cached
parameter suffix and all of its narrow translations remain literally
unchanged. -/
def RecursorParameterContextSuffix.withAmbient
    {c : AddInductive.Context}
    {R : RecursorContextWF c recLparams}
    (H : RecursorParameterContextSuffix R stats depth)
    (htr : TrExprS R.venv recLparams R.mlctx.vlctx ty ty')
    (hty : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx ty') :
    let R' := @RecursorContextWF.withLocalDecl c recLparams ty ty' name bi
      R htr hty
    RecursorParameterContextSuffix R' stats (depth + 1) := by
  dsimp only
  let entry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty')
  exact {
    ambientDecls := entry :: H.ambientDecls
    parameterDecls := H.parameterDecls
    context := by
      change entry :: R.mlctx.vlctx =
        (entry :: H.ambientDecls) ++ H.parameterDecls
      simpa only [List.cons_append] using congrArg (entry :: ·) H.context
    prefixLength := by simp [H.prefixLength]
    cached := H.cached
    narrowParams := H.narrowParams }

theorem RecursorParameterContextSuffix.parameterDecls_length
    (H : RecursorParameterContextSuffix R stats depth) :
    H.parameterDecls.length = stats.params.size := by
  have hlength := Lean4Lean.VerifyInductive.List.Forall₂.length_eq' H.cached
  simpa using hlength.symm

theorem RecursorParameterContextSuffix.depth_le
    (H : RecursorParameterContextSuffix R stats depth) :
    depth ≤ R.mlctx.length := by
  rw [← TypeChecker.MLCtx.vlctx_length]
  rw [H.context, List.length_append, H.prefixLength]
  omega

/-- Removing the recorded generated-local prefix leaves exactly the cached
parameter scope, not merely a context of the same length. -/
theorem RecursorParameterContextSuffix.dropAmbient_vlctx
    (H : RecursorParameterContextSuffix R stats depth) :
    (R.mlctx.dropN depth H.depth_le).vlctx = H.parameterDecls := by
  have hdecomp := TypeChecker.MLCtx.vlctx_eq_take_append_dropN
    R.mlctx depth H.depth_le
  have htake : R.mlctx.vlctx.take depth = H.ambientDecls := by
    have := congrArg (List.take depth) H.context
    simpa [H.prefixLength] using this
  exact List.append_cancel_left <| calc
    H.ambientDecls ++ (R.mlctx.dropN depth H.depth_le).vlctx =
        R.mlctx.vlctx := by rw [← htake, ← hdecomp]
    _ = H.ambientDecls ++ H.parameterDecls := H.context

theorem RecursorParameterContextSuffix.parameterAt
    (H : RecursorParameterContextSuffix R stats depth)
    (hi : i < stats.params.size)
    (hj : stats.params.size - 1 - i < H.parameterDecls.length) :
    checkInductiveTypes.loopType.CachedParameterDecl stats.params[i]
      H.parameterDecls[stats.params.size - 1 - i] := by
  let j := stats.params.size - 1 - i
  have hj' : j < stats.params.size := by
    dsimp [j]
    omega
  have hleft : j < stats.params.toList.reverse.length := by
    simpa using hj'
  have hright : j < H.parameterDecls.length := hj
  have hcached := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    H.cached j hleft hright
  simp only [List.getElem_reverse, Array.getElem_toList] at hcached
  change checkInductiveTypes.loopType.CachedParameterDecl
    stats.params[stats.params.size - 1 - j] H.parameterDecls[j] at hcached
  dsimp [j] at hcached ⊢
  have hindex : stats.params.size - 1 -
      (stats.params.size - 1 - i) = i := by omega
  have helem :
      stats.params[stats.params.size - 1 -
        (stats.params.size - 1 - i)] = stats.params[i] :=
    getElem_congr rfl hindex (by omega)
  rw [← helem]
  exact hcached

theorem RecursorParameterContextSuffix.splitAt
    (H : RecursorParameterContextSuffix R stats depth)
    (hi : i < stats.params.size) :
    ∃ newer entry older,
      H.parameterDecls = newer ++ entry :: older ∧
      newer.length = stats.params.size - 1 - i ∧
      checkInductiveTypes.loopType.CachedParameterDecl stats.params[i]
        entry := by
  let j := stats.params.size - 1 - i
  have hj : j < H.parameterDecls.length := by
    rw [H.parameterDecls_length]
    dsimp [j]
    omega
  refine ⟨H.parameterDecls.take j, H.parameterDecls[j],
    H.parameterDecls.drop (j + 1), ?_, ?_, ?_⟩
  · calc
      H.parameterDecls =
          H.parameterDecls.take j ++ H.parameterDecls.drop j :=
        (List.take_append_drop j H.parameterDecls).symm
      _ = H.parameterDecls.take j ++
          H.parameterDecls[j] :: H.parameterDecls.drop (j + 1) := by
        rw [List.drop_eq_getElem_cons hj]
  · simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj), j]
  · exact H.parameterAt hi hj

theorem RecursorParameterContextSuffix.fvLiftAt
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : RecursorParameterContextSuffix R stats depth)
    (hi : i < stats.params.size) :
    ∃ added newer older fv deps paramType,
      H.parameterDecls =
        newer ++ (some (fv, deps), .vlam paramType) :: older ∧
      newer.length = stats.params.size - 1 - i ∧
      added = H.ambientDecls ++ newer ∧
      R.mlctx.vlctx =
        added ++ (some (fv, deps), .vlam paramType) :: older ∧
      stats.params[i] = .fvar fv ∧
      VLCtx.FVLift ((some (fv, deps), .vlam paramType) :: older)
        R.mlctx.vlctx 0 (VLCtx.toCtx added).length 0 := by
  rcases H.splitAt hi with
    ⟨newer, entry, older, hdecls, hnewer, hcached⟩
  rcases hcached with ⟨fv, deps, paramType, hparam, rfl⟩
  let added := H.ambientDecls ++ newer
  have hcontext : R.mlctx.vlctx =
      added ++ (some (fv, deps), .vlam paramType) :: older := by
    rw [H.context, hdecls]
    simp only [added, List.append_assoc]
  have hfullNoBV :
      (added ++ (some (fv, deps), .vlam paramType) :: older).NoBV := by
    rw [← hcontext]
    exact R.mlctx.noBV
  have hadded : added.NoBV :=
    VLCtx.NoBV.leftOfAppend added
      ((some (fv, deps), .vlam paramType) :: older) hfullNoBV
  have hlift := VLCtx.FVLift.to_append
    ((some (fv, deps), .vlam paramType) :: older) hadded
  rw [← hcontext] at hlift
  exact ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer,
    rfl, hcontext, hparam, hlift⟩

/-- Cursor exposing cached parameter `i` while later-family header replay is
performed in a universe-rebased recursor context. -/
structure RecursorLaterParameterScope
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (Hsuffix : RecursorParameterContextSuffix R stats depth)
    (i : Nat) (e : Expr) : Type where
  added : VLCtx
  newer : VLCtx
  older : VLCtx
  fv : FVarId
  deps : List FVarId
  paramType : VExpr
  parameterDecls : Hsuffix.parameterDecls =
    newer ++ (some (fv, deps), .vlam paramType) :: older
  newerLength : newer.length = stats.params.size - 1 - i
  addedEq : added = Hsuffix.ambientDecls ++ newer
  context : R.mlctx.vlctx =
    added ++ (some (fv, deps), .vlam paramType) :: older
  parameter : stats.params[i]! = .fvar fv
  lift : VLCtx.FVLift ((some (fv, deps), .vlam paramType) :: older)
    R.mlctx.vlctx 0 (VLCtx.toCtx added).length 0
  fvars : FVarsIn (· ∈ older.fvars) e

theorem RecursorLaterParameterScope.olderLength
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : RecursorParameterContextSuffix R stats depth} {e : Expr}
    (H : RecursorLaterParameterScope Hsuffix i e)
    (hi : i < stats.params.size) : H.older.length = i := by
  have htotal := Hsuffix.parameterDecls_length
  have hparts := congrArg List.length H.parameterDecls
  simp only [List.length_append, List.length_cons] at hparts
  rw [htotal, H.newerLength] at hparts
  omega

theorem RecursorLaterParameterScope.parameterDefEq
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    {params : List VExpr}
    (H : RecursorLaterParameterScope Hsuffix i e)
    (hi : i < stats.params.size)
    (hparams : params.length = stats.params.size)
    (hctx : VEnv.IsDefEqCtx R.venv recLparams.length []
      params.reverse Hsuffix.parameterDecls.toCtx) :
    ∃ u, R.venv.IsDefEq recLparams.length H.older.toCtx
      (params[i]'(hparams.symm ▸ hi)) H.paramType (.sort u) := by
  have hcachedLength :=
    checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
      Hsuffix.cached
  have hdeclLength := Hsuffix.parameterDecls_length
  have hnewerLe :=
    checkInductiveTypes.loopType.VLCtx.toCtx_length_le H.newer
  have holderLe :=
    checkInductiveTypes.loopType.VLCtx.toCtx_length_le H.older
  have hctxParts := congrArg List.length <|
    congrArg VLCtx.toCtx H.parameterDecls
  simp only [VLCtx.toCtx_append, VLCtx.toCtx, List.length_append,
    List.length_cons] at hctxParts
  have hlistParts := congrArg List.length H.parameterDecls
  simp only [List.length_append, List.length_cons] at hlistParts
  have hnewerCtx : H.newer.toCtx.length = H.newer.length := by omega
  let j := H.newer.toCtx.length
  have hj : j < params.reverse.length := by
    simp only [List.length_reverse, j, hnewerCtx, hparams,
      H.newerLength]
    omega
  have hscopeCtx : Hsuffix.parameterDecls.toCtx =
      H.newer.toCtx ++ H.paramType :: H.older.toCtx := by
    rw [H.parameterDecls]
    simp [VLCtx.toCtx]
  have hctx' : VEnv.IsDefEqCtx R.venv recLparams.length []
      params.reverse (H.newer.toCtx ++ H.paramType :: H.older.toCtx) := by
    rw [← hscopeCtx]
    exact hctx
  have hentry := VEnv.IsDefEqCtx.getElemRight
    R.checking.tr.wf.ordered hctx' hj
  have hjEq : j = stats.params.size - 1 - i := by
    change H.newer.toCtx.length = stats.params.size - 1 - i
    rw [hnewerCtx]
    exact H.newerLength
  have hsourceIndex : params.length - 1 - j = i := by
    rw [hparams, hjEq]
    omega
  have hsourceIndex' :
      params.length - 1 - H.newer.toCtx.length = i := by
    simpa [j] using hsourceIndex
  rcases hentry with ⟨u, hentry⟩
  simp [j] at hentry
  exact ⟨u, by
    simpa only [List.getElem_reverse, hsourceIndex'] using hentry⟩

theorem RecursorLaterParameterScope.parameterPrefixDefEq
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    {params : List VExpr}
    (H : RecursorLaterParameterScope Hsuffix i e)
    (hi : i < stats.params.size)
    (hparams : params.length = stats.params.size)
    (hctx : VEnv.IsDefEqCtx R.venv recLparams.length []
      params.reverse Hsuffix.parameterDecls.toCtx) :
    VEnv.IsDefEqCtx R.venv recLparams.length []
      (params.take i).reverse H.older.toCtx := by
  have hcachedLength :=
    checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
      Hsuffix.cached
  have hdeclLength := Hsuffix.parameterDecls_length
  have hnewerLe :=
    checkInductiveTypes.loopType.VLCtx.toCtx_length_le H.newer
  have holderLe :=
    checkInductiveTypes.loopType.VLCtx.toCtx_length_le H.older
  have hctxParts := congrArg List.length <|
    congrArg VLCtx.toCtx H.parameterDecls
  simp only [VLCtx.toCtx_append, VLCtx.toCtx, List.length_append,
    List.length_cons] at hctxParts
  have hlistParts := congrArg List.length H.parameterDecls
  simp only [List.length_append, List.length_cons] at hlistParts
  have hnewerCtx : H.newer.toCtx.length = H.newer.length := by omega
  have hscopeCtx : Hsuffix.parameterDecls.toCtx =
      H.newer.toCtx ++ H.paramType :: H.older.toCtx := by
    rw [H.parameterDecls]
    simp [VLCtx.toCtx]
  have hctx' : VEnv.IsDefEqCtx R.venv recLparams.length []
      params.reverse (H.newer.toCtx ++ H.paramType :: H.older.toCtx) := by
    rw [← hscopeCtx]
    exact hctx
  let j := H.newer.toCtx.length
  have hjEq : j = stats.params.size - 1 - i := by
    change H.newer.toCtx.length = stats.params.size - 1 - i
    rw [hnewerCtx]
    exact H.newerLength
  have htake : params.length - (j + 1) = i := by
    rw [hparams, hjEq]
    omega
  have htake' : params.length - (H.newer.toCtx.length + 1) = i := by
    simpa [j] using htake
  have hdrop := VEnv.IsDefEqCtx.dropHeads hctx' (j + 1)
  simp [j] at hdrop
  simpa [List.drop_reverse, htake'] using hdrop

theorem RecursorLaterParameterScope.ownParameterDefEq
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    {params ownParams : List VExpr}
    (H : RecursorLaterParameterScope Hsuffix i e)
    (hi : i < stats.params.size)
    (hparamsLength : params.length = stats.params.size)
    (hctx : VEnv.IsDefEqCtx R.venv recLparams.length []
      params.reverse Hsuffix.parameterDecls.toCtx)
    (hown : VEnv.IsDefEqCtx R.venv recLparams.length []
      params.reverse ownParams.reverse) :
    ∃ u, R.venv.IsDefEq recLparams.length H.older.toCtx
      (ownParams[i]'(by
        have hlen : params.length = ownParams.length := by
          simpa using hown.length_eq
        omega)) H.paramType (.sort u) := by
  have hiparams : i < params.length := by omega
  have hlen : params.length = ownParams.length := by
    simpa using hown.length_eq
  have hrev : params.length - 1 - i < params.reverse.length := by
    simp
    omega
  have hentry := VEnv.IsDefEqCtx.getElem hown hrev
  have htake :
      params.length - (params.length - (1 + i) + 1) = i := by omega
  have hindex :
      params.length - (1 + (params.length - (1 + i))) = i := by omega
  have hcommonOwn : ∃ u, R.venv.IsDefEq recLparams.length
      (params.take i).reverse params[i]
      (ownParams[i]'(hlen ▸ hiparams)) (.sort u) := by
    simpa [List.getElem_reverse, List.drop_reverse, hlen.symm,
      Nat.sub_sub, htake, hindex] using hentry
  rcases hcommonOwn with ⟨u, hcommonOwn⟩
  have hprefix := H.parameterPrefixDefEq hi hparamsLength hctx
  have hcommonOwn' := hcommonOwn.defeqDFC
    R.checking.tr.wf.ordered hprefix
  rcases H.parameterDefEq hi hparamsLength hctx with
    ⟨cachedLevel, hcommonCached⟩
  have holderWF :=
    (H.lift.wf R.checking.tr.wf R.mlctx_wf.tr.wf).1
  exact ⟨cachedLevel, hcommonOwn'.symm.trans_r R.checking.tr.wf
    holderWF.toCtx hcommonCached⟩

theorem RecursorLaterParameterScope.older_eq_nil
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    {Hsuffix : RecursorParameterContextSuffix R stats depth} {e : Expr}
    (H : RecursorLaterParameterScope Hsuffix 0 e)
    (hi : 0 < stats.params.size) : H.older = [] :=
  List.eq_nil_of_length_eq_zero (H.olderLength hi)

theorem RecursorLaterParameterScope.completedScope
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : RecursorParameterContextSuffix R stats depth} {e : Expr}
    (H : RecursorLaterParameterScope Hsuffix i e)
    (hdone : i + 1 = stats.params.size) :
    (some (H.fv, H.deps), .vlam H.paramType) :: H.older =
      Hsuffix.parameterDecls := by
  have hnewerLength : H.newer.length = 0 := by
    rw [H.newerLength]
    omega
  have hnewer : H.newer = [] :=
    List.eq_nil_of_length_eq_zero hnewerLength
  rw [H.parameterDecls, hnewer]
  simp

noncomputable def RecursorLaterParameterScope.ofNoFVars
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    (hi : i < stats.params.size)
    (hfvars : FVarsIn (fun _ => False) e) :
    RecursorLaterParameterScope Hsuffix i e :=
  Classical.choice <| by
    rcases Hsuffix.fvLiftAt hi with
      ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer,
        hadd, hcontext, hparam, hlift⟩
    exact ⟨{
      added := added
      newer := newer
      older := older
      fv := fv
      deps := deps
      paramType := paramType
      parameterDecls := hdecls
      newerLength := hnewer
      addedEq := hadd
      context := hcontext
      parameter := by
        simpa [Array.getElem!_eq_getD, hi] using hparam
      lift := hlift
      fvars := hfvars.mono fun _ h => False.elim h }⟩

theorem RecursorLaterParameterScope.openedFVars
    (H : RecursorLaterParameterScope Hsuffix i body) :
    FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      (body.instantiate1' (.fvar H.fv)) := by
  apply (H.fvars.mono fun fv hfv => by
    rw [VLCtx.fvars_cons_some]
    exact List.mem_cons_of_mem H.fv hfv).instantiate1
  simp only [FVarsIn]
  rw [VLCtx.fvars_cons_some]
  exact List.mem_cons_self

theorem RecursorLaterParameterScope.openedUpSet
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    (H : RecursorLaterParameterScope Hsuffix i body) :
    IsFVarUpSet
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      R.mlctx.vlctx := by
  rw [H.context]
  exact IsFVarUpSet.suffixFVars
    ((some (H.fv, H.deps), .vlam H.paramType) :: H.older)
    H.added (by simpa [H.context] using R.mlctx_wf.tr.wf)

theorem RecursorLaterParameterScope.consumedFVars
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    (H : RecursorLaterParameterScope Hsuffix i body)
    (hbelow : FVarsBelow R.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) normalized) :
    FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      normalized := by
  have hopened : FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      (body.instantiate1 stats.params[i]!) := by
    rw [Expr.instantiate1_eq, H.parameter]
    exact H.openedFVars
  exact hbelow _ H.openedUpSet hopened

theorem RecursorLaterParameterScope.olderLift
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    (H : RecursorLaterParameterScope Hsuffix i body) :
    VLCtx.FVLift H.older R.mlctx.vlctx 0
      (VLCtx.toCtx H.added).length.succ 0 := by
  let current : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (H.fv, H.deps), .vlam H.paramType)
  have hcontext : R.mlctx.vlctx =
      (H.added ++ [current]) ++ H.older := by
    simpa only [current, List.append_assoc, List.singleton_append]
      using H.context
  have hfullNoBV : ((H.added ++ [current]) ++ H.older).NoBV := by
    rw [← hcontext]
    exact R.mlctx.noBV
  have hprefixNoBV : (H.added ++ [current]).NoBV :=
    VLCtx.NoBV.leftOfAppend (H.added ++ [current]) H.older hfullNoBV
  have hlift := VLCtx.FVLift.to_append H.older hprefixNoBV
  rw [← hcontext] at hlift
  simpa [current, VLCtx.toCtx] using hlift

theorem RecursorLaterParameterScope.domainTranslation
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    {name : Name} {dom body : Expr} {bi : BinderInfo} {dom' : VExpr}
    (H : RecursorLaterParameterScope Hsuffix i
      (.forallE name dom body bi))
    (hdom : TrExprS R.venv recLparams R.mlctx.vlctx dom dom') :
    ∃ sourceDom', TrExprS R.venv recLparams H.older dom sourceDom' := by
  have hclosed : Closed dom 0 := by
    have h := hdom.closed
    simpa [R.mlctx.noBV] using h
  exact hdom.weakFV_inv R.checking.tr.wf H.olderLift
    (.refl R.checking.tr.wf R.mlctx_wf.tr.wf) hclosed H.fvars.1

/-- Recover the cached parameter's concrete type and its recursor-universe
translation from the exact generated local context. -/
theorem RecursorLaterParameterScope.typing
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    (H : RecursorLaterParameterScope Hsuffix i body) :
    ∃ paramTy paramTy' param',
      (AddInductive.getType stats.params[i]! c).WF
        (fun ty => ty = paramTy) ∧
      TrExprS R.venv recLparams R.mlctx.vlctx paramTy paramTy' ∧
      paramTy' = H.paramType.lift.liftN
        (VLCtx.toCtx H.added).length 0 ∧
      TrExprS R.venv recLparams R.mlctx.vlctx
        stats.params[i]! param' ∧
      R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
        param' paramTy' := by
  have hhead : VLCtx.find?
      ((some (H.fv, H.deps), .vlam H.paramType) :: H.older)
      (.inr H.fv) = some (.bvar 0, H.paramType.lift) := by
    simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type]
  have hfull := H.lift.find? R.mlctx_wf.tr.wf hhead
  let param' := (VExpr.bvar 0).liftN (VLCtx.toCtx H.added).length 0
  let paramTy' := H.paramType.lift.liftN
    (VLCtx.toCtx H.added).length 0
  have hfind : R.mlctx.vlctx.find? (.inr H.fv) =
      some (param', paramTy') := by
    simpa [param', paramTy'] using hfull
  have hfv : H.fv ∈ R.mlctx.vlctx.fvars :=
    VLCtx.find?_eq_some.1 ⟨_, hfind⟩
  rcases (R.mlctx_wf.tr.find?_eq_some (fv := H.fv)).2 hfv with
    ⟨localDecl, hlocal⟩
  have hlocal' : c.lctx.find? H.fv = some localDecl := by
    rw [← R.lctx_eq]
    exact hlocal
  have hlist := hlocal
  rw [R.mlctx_wf.tr.1.find?_eq_find?_toList] at hlist
  have hid : H.fv = localDecl.fvarId := by
    simpa using List.find?_some hlist
  have hmem : localDecl ∈ R.mlctx.lctx.toList :=
    List.mem_of_find?_eq_some hlist
  rcases R.mlctx_wf.tr.find?_of_mem R.checking.tr.wf hmem with
    ⟨value', type', hfind', _hvalueBelow, _htypeBelow,
      _hvalue, htype⟩
  rw [← hid] at hfind'
  rw [hfind] at hfind'
  cases hfind'
  refine ⟨localDecl.type, paramTy', param', ?_, htype, rfl, ?_, ?_⟩
  · intro ty hrun
    rw [H.parameter] at hrun
    change Except.ok ((c.lctx.get! H.fv).type) = Except.ok ty at hrun
    simp [LocalContext.get!, hlocal'] at hrun
    exact hrun.symm
  · rw [H.parameter]
    exact .fvar hfind
  · exact R.mlctx_wf.tr.wf.find?_wf R.checking.tr.wf hfind

noncomputable def RecursorLaterParameterScope.next
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    (H : RecursorLaterParameterScope Hsuffix i body)
    (hi : i + 1 < stats.params.size)
    (hbelow : FVarsBelow R.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) normalized) :
    RecursorLaterParameterScope Hsuffix (i + 1) normalized :=
  Classical.choice <| by
    rcases Hsuffix.fvLiftAt hi with
      ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer,
        hadd, hcontext, hparam, hlift⟩
    let currentEntry : Option (FVarId × List FVarId) × VLocalDecl :=
      (some (H.fv, H.deps), .vlam H.paramType)
    let nextEntry : Option (FVarId × List FVarId) × VLocalDecl :=
      (some (fv, deps), .vlam paramType)
    have hdecomp : H.newer ++ currentEntry :: H.older =
        (newer ++ [nextEntry]) ++ older := by
      calc
        H.newer ++ currentEntry :: H.older =
            Hsuffix.parameterDecls := H.parameterDecls.symm
        _ = newer ++ nextEntry :: older := hdecls
        _ = (newer ++ [nextEntry]) ++ older := by
          simp [List.append_assoc]
    have hprefixLength :
        H.newer.length = (newer ++ [nextEntry]).length := by
      simp only [List.length_append, List.length_singleton]
      rw [H.newerLength, hnewer]
      omega
    have htail : currentEntry :: H.older = older :=
      List.append_inj_right hdecomp hprefixLength
    have hnormalized := H.consumedFVars hbelow
    have hnextFVars : FVarsIn (· ∈ VLCtx.fvars older) normalized := by
      rw [← htail]
      exact hnormalized
    exact ⟨{
      added := added
      newer := newer
      older := older
      fv := fv
      deps := deps
      paramType := paramType
      parameterDecls := hdecls
      newerLength := hnewer
      addedEq := hadd
      context := hcontext
      parameter := by
        simpa [Array.getElem!_eq_getD, hi] using hparam
      lift := hlift
      fvars := hnextFVars }⟩

/-- Consecutive universe-rebased cached-parameter cursors expose the same
consumed suffix. -/
theorem RecursorLaterParameterScope.nextOlder
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    {e next : Expr}
    (H : RecursorLaterParameterScope Hsuffix i e)
    (Hnext : RecursorLaterParameterScope Hsuffix (i + 1) next)
    (hi : i + 1 < stats.params.size) :
    (some (H.fv, H.deps), .vlam H.paramType) :: H.older =
      Hnext.older := by
  let currentEntry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (H.fv, H.deps), .vlam H.paramType)
  let nextEntry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (Hnext.fv, Hnext.deps), .vlam Hnext.paramType)
  have hdecomp :
      H.newer ++ currentEntry :: H.older =
        (Hnext.newer ++ [nextEntry]) ++ Hnext.older := by
    calc
      H.newer ++ currentEntry :: H.older =
          Hsuffix.parameterDecls := H.parameterDecls.symm
      _ = Hnext.newer ++ nextEntry :: Hnext.older :=
        Hnext.parameterDecls
      _ = (Hnext.newer ++ [nextEntry]) ++ Hnext.older := by
        simp [List.append_assoc]
  have hprefixLength :
      H.newer.length = (Hnext.newer ++ [nextEntry]).length := by
    simp only [List.length_append, List.length_singleton]
    rw [H.newerLength, Hnext.newerLength]
    omega
  simpa only [currentEntry] using
    List.append_inj_right hdecomp hprefixLength

/-- Descend a successful executable parameter-domain comparison to the exact
already-consumed recursor parameter suffix. -/
theorem RecursorLaterParameterScope.domainDefEq
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    {name : Name} {dom body : Expr} {bi : BinderInfo}
    {dom' paramTy' : VExpr}
    (H : RecursorLaterParameterScope Hsuffix i
      (.forallE name dom body bi))
    (hdom : TrExprS R.venv recLparams R.mlctx.vlctx dom dom')
    (hparamTyEq : paramTy' = H.paramType.lift.liftN
      (VLCtx.toCtx H.added).length 0)
    (heq : R.venv.IsDefEqU recLparams.length R.mlctx.vlctx.toCtx
      dom' paramTy') :
    ∃ sourceDom',
      TrExprS R.venv recLparams H.older dom sourceDom' ∧
      R.venv.IsDefEqU recLparams.length H.older.toCtx
        sourceDom' H.paramType := by
  rcases H.domainTranslation hdom with ⟨sourceDom', hsourceDom⟩
  have hweak := hsourceDom.weakFV R.checking.tr.wf.ordered
    H.olderLift R.mlctx_wf.tr.wf
  have htranslated : R.venv.IsDefEqU recLparams.length
      R.mlctx.vlctx.toCtx dom'
      (sourceDom'.liftN (VLCtx.toCtx H.added).length.succ 0) :=
    hdom.uniq R.checking.tr.wf
      (.refl R.checking.tr.wf R.mlctx_wf.tr.wf) hweak
  rw [hparamTyEq] at heq
  have hfull := htranslated.symm.trans R.checking.tr.wf
    R.mlctx_wf.tr.wf.toCtx heq
  have hfull' : R.venv.IsDefEqU recLparams.length
      R.mlctx.vlctx.toCtx
      (sourceDom'.liftN (VLCtx.toCtx H.added).length.succ 0)
      (H.paramType.liftN (VLCtx.toCtx H.added).length.succ 0) := by
    simpa [Nat.succ_eq_add_one, VExpr.liftN_liftN, Nat.add_comm]
      using hfull
  exact ⟨sourceDom', hsourceDom,
    (VEnv.IsDefEqU.weakN_iff R.checking.tr.wf
      R.mlctx_wf.tr.wf.toCtx H.olderLift.toCtx).1 hfull'⟩

/-- Reconstruct the source binder after substituting its cached concrete
parameter in a universe-rebased recursor context, retaining the equality back
in the full executable context. -/
theorem RecursorLaterParameterScope.uninstantiateEq
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    {body : Expr} {body' : VExpr}
    (H : RecursorLaterParameterScope Hsuffix i body)
    (hopened : TrExprS R.venv recLparams R.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) body') :
    ∃ body'', TrExprS R.venv recLparams
        ((none, .vlam H.paramType) :: H.older) body body'' ∧
      R.venv.IsDefEqU recLparams.length R.mlctx.vlctx.toCtx
        body' (body''.liftN (VLCtx.toCtx H.added).length 0) := by
  have hopened' : TrExprS R.venv recLparams R.mlctx.vlctx
      (body.instantiate1' (.fvar H.fv)) body' := by
    simpa [Expr.instantiate1_eq, H.parameter] using hopened
  have hsuffixWF := H.lift.wf R.checking.tr.wf R.mlctx_wf.tr.wf
  have hfresh : H.fv ∉ H.older.fvars :=
    (hsuffixWF.2.1 H.fv H.deps rfl).1
  have hsourceFresh : FVarsIn (· ≠ H.fv) body :=
    H.fvars.mono fun fv hfv heq => by
      subst fv
      exact hfresh hfv
  have hopenedClosed : Closed (body.instantiate1' (.fvar H.fv)) 0 := by
    have hclosed := hopened'.closed
    simpa [R.mlctx.noBV] using hclosed
  exact hopened'.uninstantiateAfterWeakFV_eq R.checking.tr.wf H.lift
    (.refl R.checking.tr.wf.ordered R.mlctx_wf.tr.wf)
    hopenedClosed H.openedFVars hsourceFresh

theorem RecursorLaterParameterScope.uninstantiate
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    {body : Expr} {body' : VExpr}
    (H : RecursorLaterParameterScope Hsuffix i body)
    (hopened : TrExprS R.venv recLparams R.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) body') :
    ∃ body'', TrExprS R.venv recLparams
      ((none, .vlam H.paramType) :: H.older) body body'' := by
  rcases H.uninstantiateEq hopened with ⟨body'', hbody'', _⟩
  exact ⟨body'', hbody''⟩

/-- Restrict a normalized cached-parameter substitution to the exact
consumed recursor suffix and relate it to the reconstructed source body. -/
theorem RecursorLaterParameterScope.normalizedBody
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    {body normalized : Expr} {body' : VExpr}
    (H : RecursorLaterParameterScope Hsuffix i body)
    (hopened : TrExprS R.venv recLparams R.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) body')
    (hbelow : FVarsBelow R.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) normalized)
    (hnormalized : TrExpr R.venv recLparams R.mlctx.vlctx
      normalized body') :
    ∃ sourceBody' normalized',
      TrExprS R.venv recLparams
        ((none, .vlam H.paramType) :: H.older) body sourceBody' ∧
      TrExprS R.venv recLparams
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older)
        normalized normalized' ∧
      R.venv.IsDefEqU recLparams.length
        (H.paramType :: H.older.toCtx) sourceBody' normalized' := by
  rcases H.uninstantiateEq hopened with
    ⟨sourceBody', hsourceBody, hopenedEq⟩
  rcases hnormalized with ⟨normalizedFull, hnormalizedFull, hnormalizeEq⟩
  have hopenedFVars : FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      (body.instantiate1 stats.params[i]!) := by
    rw [Expr.instantiate1_eq, H.parameter]
    exact H.openedFVars
  have hnormalizedFVars : FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      normalized :=
    hbelow _ H.openedUpSet hopenedFVars
  have hnormalizedClosed : Closed normalized 0 := by
    have hclosed := hnormalizedFull.closed
    simpa [R.mlctx.noBV] using hclosed
  rcases hnormalizedFull.weakFV_inv R.checking.tr.wf H.lift
      (.refl R.checking.tr.wf R.mlctx_wf.tr.wf)
      hnormalizedClosed hnormalizedFVars with
    ⟨normalized', hnormalized'⟩
  have hnormalizedWeak := hnormalized'.weakFV
    R.checking.tr.wf.ordered H.lift R.mlctx_wf.tr.wf
  have hnormalizedUniq := hnormalizedFull.uniq R.checking.tr.wf
    (.refl R.checking.tr.wf R.mlctx_wf.tr.wf) hnormalizedWeak
  have hfull : R.venv.IsDefEqU recLparams.length
      R.mlctx.vlctx.toCtx
      (sourceBody'.liftN (VLCtx.toCtx H.added).length 0)
      (normalized'.liftN (VLCtx.toCtx H.added).length 0) :=
    hopenedEq.symm.trans R.checking.tr.wf R.mlctx_wf.tr.wf.toCtx
      (hnormalizeEq.symm.trans R.checking.tr.wf
        R.mlctx_wf.tr.wf.toCtx hnormalizedUniq)
  have hnarrow : R.venv.IsDefEqU recLparams.length
      (VLCtx.toCtx
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      sourceBody' normalized' :=
    (VEnv.IsDefEqU.weakN_iff R.checking.tr.wf
      R.mlctx_wf.tr.wf.toCtx H.lift.toCtx).1 hfull
  exact ⟨sourceBody', normalized', hsourceBody, hnormalized',
    by simpa [VLCtx.toCtx] using hnarrow⟩

/-- Application statistics interpreted under recursor universes.  Unlike
`ValidAppStatsWF`, this structure does not claim that the recursor universe
list has the declaration's arity: large elimination has one additional
parameter.  The original constant-level arity remains recorded by `levels`,
while all concrete cached parameters are translated in the actual recursor
context. -/
structure RecursorValidAppStatsWF
    (env : VEnv) (recLparams : List Name) (Δ : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (depth : Nat) : Prop where
  levels : stats.levels.length = decl.uvars
  consts : checkPositivityStep.IndConstArray stats.levels stats.indConsts
    (decl.types.map (·.name))
  indices : stats.nindices.toList = decl.types.map (·.numIndices)
  params : List.Forall₂ (TrExprS env recLparams Δ) stats.params.toList
    (decl.paramVars depth)
  paramFVars : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv

/-- Reinterpret complete application statistics after introducing the
optional fresh recursor universe parameter. -/
def checkPositivityStep.ValidAppStatsWF.toRecursorContext
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    let R := Hc.toAdmissibleRecursorContextWF Helim
    RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      R.mlctx.vlctx stats decl depth := by
  dsimp only
  cases elimLevel with
  | zero =>
    exact {
      levels := H.levels
      consts := H.consts
      indices := H.indices
      params := H.params
      paramFVars := H.paramFVars }
  | param fresh =>
    let shift := VLevel.prependShift c.lparams.length
    have hparamsShift : List.Forall₂
        (TrExprS Hc.venv (fresh :: c.lparams)
          (Hc.mlctx.vlctx.instL shift))
        stats.params.toList
        ((decl.paramVars depth).map fun target => target.instL shift) := by
      have go : ∀ {sources targets},
          List.Forall₂ (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx)
              sources targets →
          List.Forall₂ (TrExprS Hc.venv (fresh :: c.lparams)
              (Hc.mlctx.vlctx.instL shift))
            sources (targets.map fun target => target.instL shift) := by
        intro sources targets Htranslated
        induction Htranslated with
        | nil => exact .nil
        | cons hsource _ ih =>
          exact .cons
            (by simpa [shift] using
              (hsource.prependLevelParam Hc.checking.tr.wf
                Hc.mlctx_wf.tr.wf Helim)) ih
      exact go H.params
    have hparamsTarget :
        (decl.paramVars depth).map (fun target => target.instL shift) =
          decl.paramVars depth := by
      simp [VInductDecl.paramVars, VExpr.instL]
    rw [hparamsTarget] at hparamsShift
    exact {
      levels := H.levels
      consts := H.consts
      indices := H.indices
      params := by
        change List.Forall₂
          (TrExprS Hc.venv (fresh :: c.lparams)
            (Hc.mlctx.prependLevelParam c.lparams.length).vlctx)
          stats.params.toList (decl.paramVars depth)
        simpa only [TypeChecker.MLCtx.prependLevelParam_vlctx, shift]
          using hparamsShift
      paramFVars := H.paramFVars }
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- Restrict recursor application statistics to the exact cached-parameter
suffix, independently of all generated ambient frames. -/
def RecursorParameterContextSuffix.narrowStats
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : RecursorParameterContextSuffix R stats depth)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams R.mlctx.vlctx
      stats decl depth) :
    RecursorValidAppStatsWF R.venv recLparams H.parameterDecls
      stats decl 0 where
  levels := Hstats.levels
  consts := Hstats.consts
  indices := Hstats.indices
  params := by
    have hsize : stats.params.size = decl.nparams := by
      have hlength :=
        Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hstats.params
      simpa [VInductDecl.paramVars] using hlength
    rw [← checkInductiveTypes.loopType.cachedParamVars_eq_paramVars decl,
      ← hsize]
    exact H.narrowParams
  paramFVars := Hstats.paramFVars

/-- Opening one semantic index under recursor universes weakens every cached
parameter target by exactly one binder. -/
theorem RecursorValidAppStatsWF.withFVar
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (henv : env.WF)
    (hscope' : VLCtx.WF env recLparams.length
      ((some (fv, deps), .vlam fieldType) :: scope)) :
    RecursorValidAppStatsWF env recLparams
      ((some (fv, deps), .vlam fieldType) :: scope)
      stats decl (depth + 1) := by
  let W : VLCtx.FVLift scope
      ((some (fv, deps), .vlam fieldType) :: scope) 0 1 0 :=
    .skip_fvar _ _ .refl
  have hparams := checkPositivityStep.forall₂_map_right
    (f := fun target => target.liftN 1 0)
    (S := TrExprS env recLparams
      ((some (fv, deps), .vlam fieldType) :: scope))
    H.params fun h => h.weakFV henv.ordered W hscope'
  exact {
    levels := H.levels
    consts := H.consts
    indices := H.indices
    params := by
      rw [← checkPositivityStep.VInductDecl.paramVars_liftN]
      exact hparams
    paramFVars := H.paramFVars }

theorem RecursorValidAppStatsWF.params_size
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth) :
    stats.params.size = decl.nparams := by
  have hlength := checkPositivityStep.forall₂_length_eq H.params
  simpa [VInductDecl.paramVars] using hlength

theorem RecursorValidAppStatsWF.types_size
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth) :
    stats.indConsts.size = decl.types.length := by
  rw [H.consts.exact]
  simp

theorem RecursorValidAppStatsWF.indConstAt
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (hi : i < decl.types.length) :
    stats.indConsts[i]? = some (.const decl.types[i].name stats.levels) := by
  rw [H.consts.exact]
  simp [hi]

theorem RecursorValidAppStatsWF.familyPrefixUnique
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (target : Nat) (htarget : target < decl.types.length) :
    TrExprS.IsUnique
      (mkAppN stats.indConsts[target]! stats.params) := by
  have hstats : target < stats.indConsts.size := by
    rw [H.types_size]
    exact htarget
  have hconst : stats.indConsts[target] =
      .const decl.types[target].name stats.levels := by
    exact Option.some.inj <|
      (Array.getElem?_eq_getElem hstats).symm.trans (H.indConstAt htarget)
  apply TrExprS.IsUnique.mkAppN (by
    simpa [Array.getElem!_eq_getD, Array.getD, hstats] using
      (show TrExprS.IsUnique stats.indConsts[target] by rw [hconst]; trivial))
  intro param hparam
  rcases H.paramFVars param hparam with ⟨fv, rfl⟩
  trivial

theorem RecursorValidAppStatsWF.nindicesAt
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (hi : i < decl.types.length) :
    stats.nindices[i]? = some decl.types[i].numIndices := by
  rw [← Array.getElem?_toList, H.indices]
  simp [hi]

theorem RecursorValidAppStatsWF.paramAt
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (hi : i < stats.params.size) :
    ∃ param', (decl.paramVars depth)[i]? = some param' ∧
      TrExprS env recLparams scope stats.params[i] param' := by
  have hsource : stats.params.toList[i]? = some stats.params[i] := by
    simp [hi]
  have htarget : ∃ param', (decl.paramVars depth)[i]? = some param' := by
    have hi' : i < (decl.paramVars depth).length := by
      have hlength := checkPositivityStep.forall₂_length_eq H.params
      simpa using hlength ▸ hi
    exact ⟨(decl.paramVars depth)[i], List.getElem?_eq_getElem hi'⟩
  rcases htarget with ⟨param', htarget⟩
  exact ⟨param', htarget,
    checkPositivityStep.forall₂_get?_eq_some H.params hsource htarget⟩

theorem RecursorValidAppStatsWF.paramFVarAt
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (hi : i < stats.params.size) :
    ∃ fv, stats.params[i] = .fvar fv := by
  exact H.paramFVars _ (by simp)

/-- A validated cached parameter still translates to the matching abstract
parameter after the recursor universe list has been extended.  The argument
uses no equality between the recursor universe arity and `decl.uvars`. -/
theorem RecursorValidAppStatsWF.translatedParam
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (hargs : List.Forall₂ (TrExprS env recLparams scope)
      type.getAppArgsList args')
    (hj : j < stats.params.size) :
    args'[j]? = (decl.paramVars depth)[j]? := by
  have harity := checkPositivityStep.isValidIndAppIdx.arity hvalid
  have hjArgs : j < type.getAppArgs.size := by omega
  have hsource : type.getAppArgsList[j]? = some type.getAppArgs[j] := by
    rw [← Expr.getAppArgs_toList]
    simp [hjArgs]
  have hlength := checkPositivityStep.forall₂_length_eq hargs
  have hjArgs' : j < args'.length := by
    rw [← hlength, ← Expr.getAppArgs_toList]
    simp [hjArgs]
  have htarget : args'[j]? = some args'[j] :=
    List.getElem?_eq_getElem hjArgs'
  have harg := checkPositivityStep.forall₂_get?_eq_some
    hargs hsource htarget
  rcases H.paramAt hj with ⟨param', hparamTarget, hparam⟩
  rcases H.paramFVarAt hj with ⟨fv, hfv⟩
  have heq := checkPositivityStep.isValidIndAppIdx.param hvalid hj
  rw [hfv] at hparam heq
  have habstract := checkPositivityStep.TrExprS.eqv_fvar_target
    hparam harg heq
  rw [htarget, hparamTarget, ← habstract]

/-- The executable parameter-prefix comparison is structural once the cached
parameters are known to be free variables.  This turns the kernel's
annotation-insensitive `Expr.eqv` guard into the exact application split used
by translation inversion below. -/
theorem RecursorValidAppStatsWF.sourceParameterPrefix
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true) :
    type.getAppArgsList.take stats.params.size = stats.params.toList := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_take]
  by_cases hj : j < stats.params.size
  · rw [if_pos hj]
    have harity := checkPositivityStep.isValidIndAppIdx.arity hvalid
    have hjArgs : j < type.getAppArgs.size := by omega
    have hsource : type.getAppArgsList[j]? =
        some type.getAppArgs[j] := by
      rw [← Expr.getAppArgs_toList]
      simp [hjArgs]
    have hcached : stats.params.toList[j]? = some stats.params[j] := by
      simp [hj]
    rcases H.paramFVarAt hj with ⟨fv, hfv⟩
    have hargEq := checkPositivityStep.isValidIndAppIdx.param hvalid hj
    rw [hfv] at hargEq
    have harg : type.getAppArgs[j] = .fvar fv :=
      Expr.eqv_fvar_eq hargEq
    rw [hsource, hcached, harg, hfv]
  · rw [if_neg hj]
    simp [hj]

theorem RecursorValidAppStatsWF.translatedIndexNoOccurrence
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (hargs : List.Forall₂ (TrExprS env recLparams scope)
      type.getAppArgsList args')
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) scope)
    (hproj : ∀ {Delta : VLCtx} {s i e' e''},
      TrProj Delta.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hlower : stats.params.size ≤ j) (hupper : j < args'.length) :
    args'[j].containsAnyConst (decl.types.map (·.name)) = false := by
  have hlength := checkPositivityStep.forall₂_length_eq hargs
  have hjArgs : j < type.getAppArgs.size := by
    have hsize : type.getAppArgs.size = type.getAppArgsList.length := by
      rw [← Expr.getAppArgs_toList]
      simp
    rw [hsize, hlength]
    exact hupper
  have hsource : type.getAppArgsList[j]? = some type.getAppArgs[j] := by
    rw [← Expr.getAppArgs_toList]
    simp [hjArgs]
  have htarget : args'[j]? = some args'[j] :=
    List.getElem?_eq_getElem hupper
  have harg := checkPositivityStep.forall₂_get?_eq_some
    hargs hsource htarget
  have hno := checkPositivityStep.isValidIndAppIdx.indexNoOccurrence
    hvalid hlower hjArgs
  exact checkPositivityStep.TrExprS.noIndOcc H.consts.names hlit hctx hproj
    harg hno

/-- Recursor-universe form of application validation.  The executable
classifier depends on the declaration's original constant levels, while the
translated expression may live under the extra large-elimination universe. -/
theorem RecursorValidAppStatsWF.validIndAppAtTarget
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (htr : TrExprS env recLparams scope type type')
    (hvalid : AddInductive.isValidIndApp? stats type = some typeIdx)
    (hi : typeIdx < decl.types.length)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) scope)
    (hproj : ∀ {Delta : VLCtx} {s i e' e''},
      TrProj Delta.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false) :
    decl.ValidIndAppAt (some (decl.types[typeIdx]'hi).name) depth type' := by
  rcases checkPositivityStep.isValidIndApp?_some hvalid with
    ⟨hsourceBound, hvalidIdx⟩
  have hconst := H.indConstAt hi
  have hhead := checkPositivityStep.isValidIndAppIdx.constHead
    hvalidIdx hconst
  rcases checkPositivityStep.TrExprS.constAppSpine htr hhead with
    ⟨levels', args', hspine, hlevels, hargs⟩
  have hlevelLen : levels'.length = decl.uvars := by
    have hlength := checkPositivityStep.List.mapM_some_length hlevels
    exact hlength.symm.trans H.levels
  have hargsLen : args'.length =
      decl.nparams + decl.types[typeIdx].numIndices := by
    have htranslated := checkPositivityStep.forall₂_length_eq hargs
    have hsource : type.getAppArgsList.length = type.getAppArgs.size := by
      rw [← Expr.getAppArgs_toList]
      simp
    have harity := checkPositivityStep.isValidIndAppIdx.arity hvalidIdx
    have hnindices : stats.nindices[typeIdx]! =
        decl.types[typeIdx].numIndices := by
      simp [Array.getElem!_eq_getD, H.nindicesAt hi]
    have hparamsSize := H.params_size
    omega
  have hparams : args'.take decl.nparams = decl.paramVars depth := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_take]
    by_cases hj : j < decl.nparams
    · rw [if_pos hj]
      apply H.translatedParam hvalidIdx hargs
      rw [H.params_size]
      exact hj
    · rw [if_neg hj]
      simp [VInductDecl.paramVars, hj]
  rw [VInductDecl.ValidIndAppAt, hspine]
  refine ⟨decl.types[typeIdx], List.getElem_mem hi, Or.inr rfl,
    levels', rfl, hlevelLen, hargsLen, hparams, ?_⟩
  intro arg harg
  rcases List.mem_drop_iff_getElem.mp harg with ⟨j, hj, hargEq⟩
  subst arg
  exact H.translatedIndexNoOccurrence (j := decl.nparams + j)
    hvalidIdx hargs hlit hctx hproj
    (by rw [H.params_size]; omega) (by simpa [Nat.add_comm] using hj)

theorem RecursorValidAppStatsWF.validIndAppAt
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (htr : TrExprS env recLparams scope type type')
    (hvalid : AddInductive.isValidIndApp? stats type = some typeIdx)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) scope)
    (hproj : ∀ {Delta : VLCtx} {s i e' e''},
      TrProj Delta.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false) :
    decl.ValidIndAppAt none depth type' := by
  have hi : typeIdx < decl.types.length := by
    have hsourceBound := (checkPositivityStep.isValidIndApp?_some hvalid).1
    rw [← H.types_size]
    exact hsourceBound
  exact (H.validIndAppAtTarget htr hvalid hi hlit hctx hproj).forgetTarget

/-- The concrete suffix consumed by motive application translates exactly to
the abstract index suffix of a validated mutual-family application. -/
theorem RecursorValidAppStatsWF.translatedIndices
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (htr : TrExprS env recLparams scope type type')
    (hvalid : AddInductive.isValidIndApp? stats type = some typeIdx)
    (hi : typeIdx < decl.types.length) :
    ∃ levels' params' indices',
      type'.getAppFnArgs =
        (.const (decl.types[typeIdx]'hi).name levels', params' ++ indices') ∧
      params' = decl.paramVars depth ∧
      indices'.length = (decl.types[typeIdx]'hi).numIndices ∧
      List.Forall₂ (TrExprS env recLparams scope)
        (type.getAppArgs[stats.params.size:]).toList indices' ∧
      TrExprS env recLparams scope
        (mkAppN stats.indConsts[typeIdx]! stats.params)
        (VExpr.mkApps
          (.const (decl.types[typeIdx]'hi).name levels') params') := by
  rcases checkPositivityStep.isValidIndApp?_some hvalid with
    ⟨_sourceBound, hvalidIdx⟩
  have hhead := checkPositivityStep.isValidIndAppIdx.constHead
    hvalidIdx (H.indConstAt hi)
  rcases checkPositivityStep.TrExprS.constAppSpine htr hhead with
    ⟨levels', args', hspine, _hlevels, hargs⟩
  let params' := args'.take decl.nparams
  let indices' := args'.drop decl.nparams
  have hsplit : args' = params' ++ indices' := by
    exact (List.take_append_drop decl.nparams args').symm
  have hparams : params' = decl.paramVars depth := by
    dsimp only [params']
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_take]
    by_cases hj : j < decl.nparams
    · rw [if_pos hj]
      apply H.translatedParam hvalidIdx hargs
      rw [H.params_size]
      exact hj
    · rw [if_neg hj]
      simp [VInductDecl.paramVars, hj]
  have hindicesLength : indices'.length =
      (decl.types[typeIdx]'hi).numIndices := by
    have harity := checkPositivityStep.isValidIndAppIdx.arity hvalidIdx
    have hnindices : stats.nindices[typeIdx]! =
        (decl.types[typeIdx]'hi).numIndices := by
      simp [Array.getElem!_eq_getD, H.nindicesAt hi]
    have hargsLength := checkPositivityStep.forall₂_length_eq hargs
    have hsourceLength : type.getAppArgsList.length =
        type.getAppArgs.size := by
      rw [← Expr.getAppArgs_toList]
      simp
    have hargsLen : args'.length =
        stats.params.size + stats.nindices[typeIdx]! := by
      omega
    dsimp only [indices']
    rw [List.length_drop, hargsLen, H.params_size, hnindices]
    omega
  have hindicesTr : List.Forall₂ (TrExprS env recLparams scope)
      (type.getAppArgs[stats.params.size:]).toList indices' := by
    have hdrop := checkPositivityStep.List.Forall₂.drop
      hargs stats.params.size
    have hparamsSize := H.params_size
    rw [hparamsSize] at hdrop ⊢
    have hsuffix : (type.getAppArgs[decl.nparams:]).toList =
        type.getAppArgs.toList.drop decl.nparams := by
      rw [List.drop_eq_drop_min]
      simp only [Subarray.toList_eq, Array.array_toSubarray,
        Array.start_toSubarray, Array.stop_toSubarray, Nat.min_self,
        Array.toList_extract, List.extract_eq_take_drop,
        Array.length_toList]
      apply List.take_of_length_le
      simp
    rw [hsuffix]
    simpa only [Expr.getAppArgs_toList] using hdrop
  have hconstSource : stats.indConsts[typeIdx]! =
      .const (decl.types[typeIdx]'hi).name stats.levels := by
    simp [Array.getElem!_eq_getD, H.indConstAt hi]
  have hsourceHead : type.getAppFn = stats.indConsts[typeIdx]! := by
    rw [hhead, hconstSource]
  have hsourcePrefix := H.sourceParameterPrefix hvalidIdx
  have hsourceSplit : type = Expr.mkAppList
      (mkAppN stats.indConsts[typeIdx]! stats.params)
      (type.getAppArgsList.drop stats.params.size) := by
    calc
      type = Expr.mkAppList type.getAppFn type.getAppArgsList :=
        (Expr.mkAppList_getAppArgsList type).symm
      _ = Expr.mkAppList type.getAppFn
          (type.getAppArgsList.take stats.params.size ++
            type.getAppArgsList.drop stats.params.size) := by
        rw [List.take_append_drop]
      _ = Expr.mkAppList
          (Expr.mkAppList type.getAppFn
            (type.getAppArgsList.take stats.params.size))
          (type.getAppArgsList.drop stats.params.size) := by
        rw [Expr.mkAppList_append]
      _ = Expr.mkAppList
          (mkAppN stats.indConsts[typeIdx]! stats.params)
          (type.getAppArgsList.drop stats.params.size) := by
        rw [hsourceHead, hsourcePrefix, Expr.mkAppN_eq_mkAppList]
  have hsplitTr : TrExprS env recLparams scope
      (Expr.mkAppList (mkAppN stats.indConsts[typeIdx]! stats.params)
        (type.getAppArgsList.drop stats.params.size)) type' := by
    rwa [← hsourceSplit]
  rcases checkPositivityStep.TrExprS.mkAppList_inv hsplitTr with
    ⟨familyTarget, _suffixTargets, hfamilyTr, _hsuffixTr, _hout⟩
  have hsourceFamilyHead :
      (mkAppN stats.indConsts[typeIdx]! stats.params).getAppFn =
        .const (decl.types[typeIdx]'hi).name stats.levels := by
    rw [Expr.getAppFn_mkAppN, hconstSource]
    rfl
  rcases checkPositivityStep.TrExprS.constAppSpine hfamilyTr
      hsourceFamilyHead with
    ⟨familyLevels, familyParams, hfamilySpine, hfamilyLevels,
      hfamilyParams⟩
  have hfamilyParams' : List.Forall₂ (TrExprS env recLparams scope)
      stats.params.toList familyParams := by
    simpa [Expr.getAppArgsList_mkAppN, hconstSource,
      Expr.getAppArgsList_const] using hfamilyParams
  have hfamilyParamsEq : familyParams = decl.paramVars depth := by
    apply List.Forall₂.targets_eq_of_unique
      hfamilyParams' H.params
    intro param hparam
    have hparamArray : param ∈ stats.params :=
      Array.mem_toList_iff.mp hparam
    rcases H.paramFVars param hparamArray with ⟨fv, rfl⟩
    trivial
  have hfamilyLevelsEq : familyLevels = levels' := by
    exact Option.some.inj (hfamilyLevels.symm.trans _hlevels)
  have hfamilyTargetEq : familyTarget = VExpr.mkApps
      (.const (decl.types[typeIdx]'hi).name levels') params' := by
    have hrebuild := VExpr.mkApps_getAppFnArgs familyTarget
    rw [hfamilySpine] at hrebuild
    rw [← hrebuild, hfamilyLevelsEq, hfamilyParamsEq, hparams]
  refine ⟨levels', params', indices', ?_, hparams, hindicesLength,
    hindicesTr, ?_⟩
  · simpa [hsplit] using hspine
  · rwa [hfamilyTargetEq] at hfamilyTr

/-- Complete terminal payload produced by the explicit recursive-result
validation branch.  It packages the targeted abstract application together
with the exact concrete/abstract index correspondence used by the motive. -/
structure RecursorValidatedIndAppAt
    (env : VEnv) (recLparams : List Name) (scope : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (depth : Nat) (type : Expr) (type' : VExpr) (target : Nat) : Prop where
  target_lt : target < decl.types.length
  owner_valid : AddInductive.isValidIndApp? stats type = some target
  application : decl.ValidIndAppAt
    (some (decl.types[target]'target_lt).name) depth type'
  indices_payload : ∃ levels params indices,
    type'.getAppFnArgs =
      (.const (decl.types[target]'target_lt).name levels, params ++ indices) ∧
    params = decl.paramVars depth ∧
    indices.length = (decl.types[target]'target_lt).numIndices ∧
    List.Forall₂ (TrExprS env recLparams scope)
      (type.getAppArgs[stats.params.size:]).toList indices ∧
    TrExprS env recLparams scope
      (mkAppN stats.indConsts[target]! stats.params)
      (VExpr.mkApps
        (.const (decl.types[target]'target_lt).name levels) params)

def RecursorValidAppStatsWF.validatedIndAppAt
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (htr : TrExprS env recLparams scope type type')
    (hvalid : AddInductive.isValidIndApp? stats type = some target)
    (htarget : target < decl.types.length)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) scope)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''},
      TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false) :
    RecursorValidatedIndAppAt env recLparams scope stats decl depth
      type type' target := by
  exact {
    target_lt := htarget
    owner_valid := hvalid
    application := H.validIndAppAtTarget htr hvalid htarget hlit hctx hproj
    indices_payload := H.translatedIndices htr hvalid htarget }

namespace isRecArg.loop

/-- The recursive-field classifier remains sound after generated recursor
frames rebase the semantic universe list. -/
theorem refinesRecursor
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hwhnf : WhnfLParamsCompat)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s i e' e''},
      TrProj Delta.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htype : TrExpr R.venv recLparams R.mlctx.vlctx type type') :
    (AddInductive.isRecArg.loop stats type fuel c).WF
      (fun result => ∀ target, result = some target →
        ∃ htarget : target < decl.types.length,
        decl.RecursiveArgAtTarget R.venv recLparams.length
          (decl.types[target]'htarget).name
          R.mlctx.vlctx.toCtx depth type') := by
  induction fuel generalizing c type type' depth with
  | zero =>
    intro _ h
    simp [AddInductive.isRecArg.loop] at h
  | succ fuel ih =>
    rcases htype with ⟨sourceSyntax, hsource, hsourceEq⟩
    rw [AddInductive.isRecArg.loop]
    refine (whnfInRecursorContext.scopeWF hwhnf R hsource).bind
      fun normalized hnormalized => ?_
    rcases hnormalized.2 with ⟨exposed, hexposed, hexposedEq⟩
    have hsourceExposed :=
      (hexposedEq.trans R.checking.tr.wf R.mlctx_wf.tr.wf.toCtx
        hsourceEq).symm
    rcases hsourceExposed with ⟨exprType, hsourceExposed⟩
    by_cases hforall : ∃ name dom body bi,
        normalized = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      cases hexposed with
      | forallE hdomType _ hdom hbody =>
        rcases hconsume c recLparams R hdom hdomType with
          ⟨consumedDom', Hdom⟩
        rcases Hdom.body R hbody with ⟨body'', hbody'', hbodyEq⟩
        refine withLocalDecl.recursorWF (name := name) (bi := bi)
          (Q := fun result => ∀ target, result = some target →
            ∃ htarget : target < decl.types.length,
            decl.RecursiveArgAtTarget R.venv recLparams.length
              (decl.types[target]'htarget).name
              R.mlctx.vlctx.toCtx depth type')
          R Hdom.consumed Hdom.isType ?_
        let R' := R.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType
        have hopened := R.instantiateFresh (name := name) (bi := bi)
          Hdom.consumed Hdom.isType hbody''
        have Hstats' := Hstats.withFVar R'.checking.tr.wf
          R'.mlctx_wf.tr.wf
        have hctx' : checkPositivityStep.VLCtx.NoIndConsts
            (decl.types.map (·.name)) R'.mlctx.vlctx := by
          apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
          rfl
        have Hrec := ih R' Hstats' hctx'
          (hopened.trExpr R'.checking.tr.wf R'.mlctx_wf.tr.wf)
        exact Hrec.mono fun result hrec target htarget => by
          rcases hrec target htarget with ⟨htarget, hrecursive⟩
          rcases Hdom.source_defeq with ⟨domLevel, hdomEq⟩
          rcases hbodyEq with ⟨bodyType, hbodyEq⟩
          exact ⟨htarget, .forallE
            (by simpa [Hstats.levels] using hsourceExposed)
            (by simpa [Hstats.levels] using hdomEq)
            (by simpa [Hstats.levels] using hbodyEq)
            hrecursive⟩
    · cases normalized <;> try { simp at hforall }
      all_goals
        change (Except.ok (AddInductive.isValidIndApp? stats _)).WF _
        exact Except.WF.pure fun target hvalid => by
          rcases checkPositivityStep.isValidIndApp?_some hvalid with
            ⟨htargetLt, _⟩
          have htargetDecl : target < decl.types.length := by
            rw [← Hstats.types_size]
            exact htargetLt
          refine ⟨htargetDecl, .direct
            (by simpa [Hstats.levels] using hsourceExposed)
            (Hstats.validIndAppAtTarget hexposed hvalid htargetDecl
              hlit hctx hproj)⟩

end isRecArg.loop

theorem isRecArg.refinesRecursor
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hwhnf : WhnfLParamsCompat)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s i e' e''},
      TrProj Delta.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htype : TrExpr R.venv recLparams R.mlctx.vlctx type type') :
    (AddInductive.isRecArg stats type c).WF
      (fun result => ∀ target, result = some target →
        ∃ htarget : target < decl.types.length,
        decl.RecursiveArgAtTarget R.venv recLparams.length
          (decl.types[target]'htarget).name
          R.mlctx.vlctx.toCtx depth type') := by
  unfold AddInductive.isRecArg
  have hread : ((read : AddInductive.M AddInductive.Context) c).WF
      (fun c' => c' = c) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  exact isRecArg.loop.refinesRecursor R Hstats hwhnf hconsume hlit hctx
    hproj htype

/-- Recursive-domain metadata interpreted at an explicit universe arity.
This is the second-pass analogue of `RecursorRecursiveDomain`; it is needed
while large-elimination recursors are being built under their fresh leading
universe parameter. -/
structure RecursorRecursiveDomainAt
    (env : VEnv) (decl : VInductDecl) (uvars : Nat) where
  fieldIndex : Nat
  ownerIdx : Nat
  owner_lt : ownerIdx < decl.types.length
  ctx : List VExpr
  depth : Nat
  domain : VExpr
  recursive : decl.RecursiveArgAtTarget env uvars
    (decl.types[ownerIdx]'owner_lt).name ctx depth domain

/-- Exact field-selection trace at the recursor universe arity. -/
inductive RecursorFieldSelectionsAt
    (env : VEnv) (decl : VInductDecl) (uvars : Nat) :
    Array Expr → Array Expr →
      List (RecursorRecursiveDomainAt env decl uvars) → Prop
  | nil : RecursorFieldSelectionsAt env decl uvars #[] #[] []
  | nonrecursive : RecursorFieldSelectionsAt env decl uvars bu u fields →
      RecursorFieldSelectionsAt env decl uvars (bu.push arg) u fields
  | recursive : RecursorFieldSelectionsAt env decl uvars bu u fields →
      cert.fieldIndex = bu.size →
      RecursorFieldSelectionsAt env decl uvars (bu.push arg) (u.push arg)
        (fields ++ [cert])

/-- Exact successful classifier decisions made while traversing constructor
fields.  Unlike `RecursorFieldSelectionsAt`, this trace retains the `none`
branches as well as the selected ordinals, so independently replayed passes
can later be compared by an operational alpha-invariance theorem. -/
inductive RecursorFieldDecisions (stats : AddInductive.InductiveStats)
    (root : AddInductive.Context) (source : Expr) :
    AddInductive.Context → Expr → Array Expr → Array Expr →
      List Nat → Prop
  | nil : RecursorFieldDecisions stats root source root source #[] #[] []
  | nonrecursive :
      RecursorFieldDecisions stats root source c
        (.forallE name dom body bi) bu u positions →
      AddInductive.isRecArg stats dom { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotations bi } = .ok none →
      RecursorFieldDecisions stats root source { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotations bi }
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))
        (bu.push (.fvar ⟨c.ngen.curr⟩)) u positions
  | recursive :
      RecursorFieldDecisions stats root source c
        (.forallE name dom body bi) bu u positions →
      AddInductive.isRecArg stats dom { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotations bi } = .ok (some target) →
      RecursorFieldDecisions stats root source { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotations bi }
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))
        (bu.push (.fvar ⟨c.ngen.curr⟩))
        (u.push (.fvar ⟨c.ngen.curr⟩)) (positions ++ [bu.size])

theorem RecursorFieldDecisions.positions_length
    (H : RecursorFieldDecisions stats root source c t bu u positions) :
    positions.length = u.size := by
  induction H with
  | nil => rfl
  | nonrecursive _ _ ih => exact ih
  | recursive _ _ ih => simp [ih]

theorem RecursorFieldDecisions.positions_lt
    (H : RecursorFieldDecisions stats root source c t bu u positions) :
    ∀ position ∈ positions, position < bu.size := by
  intro position hposition
  induction H with
  | nil => simp at hposition
  | nonrecursive _ _ ih =>
    have := ih hposition
    simp only [Array.size_push]
    omega
  | recursive _ _ ih =>
    simp only [List.mem_append, List.mem_singleton] at hposition
    rcases hposition with hposition | rfl
    · have := ih hposition
      simp only [Array.size_push]
      omega
    · simp only [Array.size_push]
      omega

/-- The decision mask is not merely cardinality metadata: its `j`th ordinal
selects the exact `j`th member of the recursive-field array from the complete
field array.  This formulation is independent of the fresh identifiers used
by a particular traversal and is therefore the pointwise companion to replay
compatibility. -/
theorem RecursorFieldDecisions.selected_at
    (H : RecursorFieldDecisions stats root source c t bu u positions)
    (j : Nat) (hj : j < u.size) :
    positions[j]! < bu.size ∧ u[j]! = bu[positions[j]!]! := by
  induction H generalizing j with
  | nil => simp at hj
  | @nonrecursive c name dom body bi bu u positions Hdecision _ ih =>
      rcases ih j hj with ⟨hposition, hselected⟩
      have hposition' : positions[j]! < (bu.push
          (.fvar ⟨c.ngen.curr⟩)).size := by
        simp only [Array.size_push]
        omega
      refine ⟨hposition', ?_⟩
      rw [getElem!_pos u j hj] at hselected ⊢
      rw [getElem!_pos bu positions[j]! hposition] at hselected
      rw [getElem!_pos (bu.push (.fvar ⟨c.ngen.curr⟩))
        positions[j]! hposition']
      simpa only [Array.getElem_push_lt hposition] using hselected
  | @recursive c name dom body bi bu u positions target Hdecision _ ih =>
      by_cases hold : j < u.size
      · rcases ih j hold with ⟨hposition, hselected⟩
        have hpositionBound : j < positions.length := by
          rw [Hdecision.positions_length]
          exact hold
        have hpositionAppendBound : j <
            (positions ++ [bu.size]).length := by
          simp only [List.length_append, List.length_singleton]
          omega
        have hpositionValue : (positions ++ [bu.size])[j]! =
            positions[j]! := by
          rw [getElem!_pos (positions ++ [bu.size]) j
            hpositionAppendBound, getElem!_pos positions j hpositionBound]
          exact List.getElem_append_left hpositionBound
        have hposition' : (positions ++ [bu.size])[j]! <
            (bu.push (.fvar ⟨c.ngen.curr⟩)).size := by
          rw [hpositionValue]
          simp only [Array.size_push]
          omega
        refine ⟨hposition', ?_⟩
        rw [hpositionValue]
        rw [getElem!_pos (u.push (.fvar ⟨c.ngen.curr⟩)) j (by
          simp only [Array.size_push]
          omega)]
        rw [Array.getElem_push_lt hold]
        rw [getElem!_pos u j hold] at hselected
        rw [getElem!_pos bu positions[j]! hposition] at hselected
        rw [getElem!_pos (bu.push (.fvar ⟨c.ngen.curr⟩))
          positions[j]! (by simp only [Array.size_push]; omega)]
        simpa only [Array.getElem_push_lt hposition] using hselected
      · have hjEq : j = u.size := by
          simp only [Array.size_push] at hj
          omega
        subst j
        have hpositionBound : u.size <
            (positions ++ [bu.size]).length := by
          simp [Hdecision.positions_length]
        have hpositionValue : (positions ++ [bu.size])[u.size]! =
            bu.size := by
          have hlast : (positions ++ [bu.size])[positions.length]! =
              bu.size := by simp
          simpa [Hdecision.positions_length] using hlast
        rw [hpositionValue]
        simp

theorem RecursorFieldDecisions.positions_ordered
    (H : RecursorFieldDecisions stats root source c t bu u positions) :
    positions.Pairwise (· < ·) := by
  induction H with
  | nil => simp
  | nonrecursive _ _ ih => exact ih
  | recursive H _ ih =>
    rw [List.pairwise_append]
    refine ⟨ih, by simp, ?_⟩
    intro old hold _ hnew
    simp only [List.mem_singleton] at hnew
    subst hnew
    exact H.positions_lt old hold

theorem RecursorFieldSelectionsAt.fields_length
    (H : RecursorFieldSelectionsAt env decl uvars bu u fields) :
    fields.length = u.size := by
  induction H with
  | nil => rfl
  | nonrecursive _ ih => exact ih
  | recursive _ _ ih => simp [ih]

theorem RecursorFieldSelectionsAt.positions_lt
    (H : RecursorFieldSelectionsAt env decl uvars bu u fields) :
    ∀ cert ∈ fields, cert.fieldIndex < bu.size := by
  induction H with
  | nil => simp
  | @nonrecursive bu u fields arg _ ih =>
    intro cert hmem
    have := ih cert hmem
    simp only [Array.size_push]
    omega
  | @recursive bu u fields arg cert _ hindex ih =>
    intro old hmem
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · have := ih old hmem
      simp only [Array.size_push]
      omega
    · simp only [Array.size_push, hindex]
      omega

theorem RecursorFieldSelectionsAt.positions_ordered
    (H : RecursorFieldSelectionsAt env decl uvars bu u fields) :
    (fields.map (·.fieldIndex)).Pairwise (· < ·) := by
  induction H with
  | nil => simp
  | nonrecursive _ ih => exact ih
  | @recursive bu u fields arg cert H hindex ih =>
    simp only [List.map_append, List.map_singleton]
    rw [List.pairwise_append]
    refine ⟨ih, by simp, ?_⟩
    intro old hold _ hnew
    simp only [List.mem_singleton] at hnew
    subst hnew
    rw [hindex]
    rcases List.mem_map.mp hold with ⟨oldCert, hmem, rfl⟩
    exact H.positions_lt oldCert hmem

/-- The target-indexed recursor trace retains the same pointwise alignment
between selected recursive fields and the complete constructor-field array
as its declaration-universe counterpart. -/
theorem RecursorFieldSelectionsAt.arguments_at_positions
    (H : RecursorFieldSelectionsAt env decl uvars bu u fields) :
    List.Forall₂ (fun cert arg =>
      ∃ h : cert.fieldIndex < bu.size, arg = bu[cert.fieldIndex]'h)
      fields u.toList := by
  induction H with
  | nil => exact .nil
  | @nonrecursive bu u fields arg H ih =>
    have lift : List.Forall₂ (fun cert selected =>
        ∃ h : cert.fieldIndex < (bu.push arg).size,
          selected = (bu.push arg)[cert.fieldIndex]'h)
        fields u.toList := by
      apply List.Forall₂.imp (R := fun cert selected =>
        ∃ h : cert.fieldIndex < bu.size,
          selected = bu[cert.fieldIndex]'h) (fun cert selected hhead => ?_) ih
      rcases hhead with ⟨hpos, heq⟩
      refine ⟨by simp; omega, ?_⟩
      rw [heq]
      exact (Array.getElem_push_lt hpos).symm
    exact lift
  | @recursive bu u fields arg cert H hindex ih =>
    have lift : List.Forall₂ (fun old selected =>
        ∃ h : old.fieldIndex < (bu.push arg).size,
          selected = (bu.push arg)[old.fieldIndex]'h)
        fields u.toList := by
      apply List.Forall₂.imp (R := fun old selected =>
        ∃ h : old.fieldIndex < bu.size,
          selected = bu[old.fieldIndex]'h) (fun old selected hhead => ?_) ih
      rcases hhead with ⟨hpos, heq⟩
      refine ⟨by simp; omega, ?_⟩
      rw [heq]
      exact (Array.getElem_push_lt hpos).symm
    rw [Array.toList_push]
    apply checkPositivityStep.forall₂_append lift
    apply List.Forall₂.cons
    · refine ⟨by simp [hindex], ?_⟩
      simpa [hindex] using (@Array.getElem_push_eq Expr bu arg).symm
    · exact .nil

/-- Replace every semantic certificate in a field-selection trace while
preserving its recorded concrete field ordinal.  The operational selection
arrays are unchanged; this is the bridge used to substitute the stronger
call-time recursive-domain certificates for the earlier classifier trace. -/
theorem RecursorFieldSelectionsAt.replace
    (H : RecursorFieldSelectionsAt env decl uvars bu u fields)
    (Haligned : List.Forall₂
      (fun old replacement =>
        old.fieldIndex = replacement.fieldIndex)
      fields replacements) :
    RecursorFieldSelectionsAt env decl uvars bu u replacements := by
  induction H generalizing replacements with
  | nil =>
    cases Haligned
    exact .nil
  | nonrecursive _ ih =>
    exact .nonrecursive (ih Haligned)
  | @recursive bu u fields arg cert H hindex ih =>
    rcases Lean4Lean.VerifyInductive.List.Forall₂.unsnoc Haligned with
      ⟨replacementPrefix, replacement, rfl, Hprefix, Hlast⟩
    apply RecursorFieldSelectionsAt.recursive (cert := replacement)
      (ih Hprefix)
    exact Hlast ▸ hindex

/-- Specialize a recursor-universe recursive-domain witness to the declaration
universe arity.  Zero is a valid specialization for every recursor universe;
the concrete field selection remains unchanged, while the semantic context
and domain are instantiated in lockstep. -/
def RecursorRecursiveDomainAt.toSource
    (cert : RecursorRecursiveDomainAt env decl uvars) :
    RecursorRecursiveDomain env decl where
  fieldIndex := cert.fieldIndex
  ownerIdx := cert.ownerIdx
  owner_lt := cert.owner_lt
  ctx := cert.ctx.map (VExpr.instL (List.replicate uvars .zero))
  depth := cert.depth
  domain := cert.domain.instL (List.replicate uvars .zero)
  recursive := cert.recursive.instL (List.replicate uvars .zero)
    (by simp [VLevel.WF])

@[simp] theorem RecursorRecursiveDomainAt.toSource_fieldIndex
    (cert : RecursorRecursiveDomainAt env decl uvars) :
    cert.toSource.fieldIndex = cert.fieldIndex := rfl

/-- Field selection is operationally universe-insensitive.  Specializing each
semantic domain therefore converts the second-pass trace directly into the
source-universe trace consumed by the independent iota specification. -/
theorem RecursorFieldSelectionsAt.toSource
    (H : RecursorFieldSelectionsAt env decl uvars bu u fields) :
    RecursorFieldSelections env decl bu u
      (fields.map RecursorRecursiveDomainAt.toSource) := by
  induction H with
  | nil => exact .nil
  | nonrecursive _ ih => exact .nonrecursive ih
  | @recursive bu u fields arg cert H hindex ih =>
    simpa using RecursorFieldSelections.recursive
      (cert := cert.toSource) ih hindex


end VerifyInductive
end Lean4Lean
