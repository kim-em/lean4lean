import Lean4Lean.Verify.Inductive.Recursor.Entries.Targets

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Exact certificate for a suffix of local declarations introduced by
`withLocalDecl`; its domains are recorded in the same outermost-to-innermost
order used by generated recursor telescopes. -/
inductive MLCtxLamPrefix : TypeChecker.MLCtx → Nat → List VExpr → Prop
  | nil (c : TypeChecker.MLCtx) : MLCtxLamPrefix c 0 []
  | cons : MLCtxLamPrefix c n domains →
      MLCtxLamPrefix (.vlam fv name type type' bi c) (n + 1)
        (domains ++ [type'])

theorem MLCtxLamPrefix.le
    (H : MLCtxLamPrefix c n domains) : n ≤ c.length := by
  induction H with
  | nil => simp
  | cons _ ih => simpa using Nat.succ_le_succ ih

/-- Every bounded prefix of an all-lambda checker context has an exact
`MLCtxLamPrefix` certificate. This packages the structural induction needed
when a later proof walks a recent suffix one declaration at a time. -/
theorem MLCtxOnlyLams.lamPrefix
    (H : MLCtxOnlyLams c) (n : Nat) (hn : n ≤ c.length) :
    ∃ domains, MLCtxLamPrefix c n domains := by
  induction n generalizing c with
  | zero => exact ⟨[], .nil c⟩
  | succ n ih =>
    cases c with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      rcases ih H.tail_vlam (Nat.le_of_succ_le_succ hn) with
        ⟨domains, Hprefix⟩
      exact ⟨domains ++ [type'], Hprefix.cons⟩
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

/-- Extend a `FrontScopeEmbedding` by a recent prefix of lambda declarations that was also
opened in a checker context aligned with the base scope. Each domain is the
checker translation transported along the alignment, so no runtime
translation is restricted, and the resulting scope stays aligned with the
checker context. -/
theorem MLCtxLamPrefix.extendFrontScopeEmbeddingAligned
    (H : MLCtxLamPrefix runtime n domains)
    (henv : env.WF)
    (Hwf : runtime.WF env Us)
    (Hbase : checkInductiveTypes.loopType.FrontScopeEmbedding env Us
      baseScope (runtime.dropN n H.le).vlctx)
    (hup : IsFVarUpSet
      (fun fv => fv ∈ runtime.fvarRevList n H.le ++ baseScope.fvars)
      runtime.vlctx)
    {chk : TypeChecker.MLCtx} (hchkWF : chk.WF env Us)
    (hn : n ≤ chk.length) (hagree : MLCtxTopAgree runtime chk n)
    (hbaseAlign : VLCtx.IsDefEq env Us.length baseScope (chk.dropN n hn).vlctx) :
    ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FrontScopeEmbedding env Us
          scope runtime.vlctx,
        scope.fvars = runtime.fvarRevList n H.le ++ baseScope.fvars ∧
        scope.drop Hscope.frontSourceDomains.length =
          baseScope.drop Hbase.frontSourceDomains.length ∧
        (∃ newDomains,
          newDomains.length = n ∧
          Hscope.frontSourceDomains =
            Hbase.frontSourceDomains ++ newDomains) ∧
        VLCtx.IsDefEq env Us.length scope chk.vlctx := by
  induction H generalizing chk with
  | nil runtime =>
    exact ⟨baseScope, Hbase,
      by simp [TypeChecker.MLCtx.fvarRevList], rfl, ⟨[], rfl, by simp⟩,
      by simpa using hbaseAlign⟩
  | @cons tail n domains fv name type type' bi Hprefix ih =>
    cases hagree with
    | @vlam _ chkTail _ hagreeTail _ _ _ _ t₂ _ =>
    have HruntimeWF := Hwf.tr.wf
    rcases Hwf with ⟨HtailWF, hfresh, Htype, HtypeType⟩
    rcases hchkWF with ⟨hchkTailWF, hfreshC, Htype₀, Htype₀Type⟩
    have hcurrentFresh : fv ∉ tail.vlctx.fvars :=
      HtailWF.tr.find?_eq_none.1 hfresh
    have htailUp : IsFVarUpSet
        (fun fv' =>
          fv' ∈ tail.fvarRevList n Hprefix.le ++ baseScope.fvars)
        tail.vlctx := by
      apply (IsFVarUpSet.congr HtailWF.tr.wf.fvwf ?_).mp hup.1
      intro fv' hfv'
      constructor
      · intro h
        rcases List.mem_cons.mp h with hcurrent | h
        · exact False.elim (hcurrentFresh (hcurrent ▸ hfv'))
        · exact h
      · exact List.mem_cons_of_mem _
    have hnTail : n ≤ chkTail.length := by simpa using hn
    rcases ih HtailWF Hbase htailUp hchkTailWF hnTail hagreeTail
        (by simpa using hbaseAlign) with
      ⟨tailScope, HtailScope, htailScopeFVars, htailBase,
        ⟨tailDomains, htailDomains, htailFront⟩, halignTail⟩
    have hdepsFull : ∀ dep ∈ type.fvarsList,
        dep ∈ fv :: tail.fvarRevList n Hprefix.le ++ baseScope.fvars := by
      exact hup.2 (by simp)
    have hdeps : type.fvarsList ⊆ tailScope.fvars := by
      intro dep hdep
      rw [htailScopeFVars]
      have hselected := hdepsFull dep hdep
      rcases List.mem_cons.mp hselected with hcurrent | hselected
      · exact False.elim (hcurrentFresh (hcurrent ▸ Htype.fvarsList hdep))
      · exact hselected
    have halignTailSymm := halignTail.symm henv.orderedStrong
    obtain ⟨narrowType, HnarrowType⟩ := Htype₀.defeqDFC henv halignTailSymm
    have hNU := Htype₀.uniq henv halignTailSymm HnarrowType
    have HnarrowIsType : env.IsType Us.length tailScope.toCtx narrowType :=
      (Htype₀Type.defeqU_l henv hchkTailWF.tr.wf.toCtx hNU).defeqDFC
        henv.ordered halignTailSymm.defeqCtx
    have Hweak : TrExprS env Us HtailScope.expanded type
        (narrowType.lift' HtailScope.shift) := by
      simpa using HnarrowType.weakFV' henv.orderedStrong HtailScope.lift
        HtailScope.context.wf
    have HtargetEq := Hweak.uniq henv HtailScope.context Htype
    have HtargetType : env.IsType Us.length HtailScope.expanded.toCtx
        type' :=
      HtypeType.defeqDFC henv.ordered
        (HtailScope.context.symm henv.orderedStrong).defeqCtx
    rcases HtargetType with ⟨u, HtargetType⟩
    have Hdomain : env.IsDefEq Us.length HtailScope.expanded.toCtx
        (narrowType.lift' HtailScope.shift) type' (.sort u) :=
      HtargetEq.of_r henv HtailScope.context.wf.toCtx HtargetType
    let Hnext := HtailScope.withIndex
      HruntimeWF
      hdeps name bi type HnarrowType Hdomain HnarrowIsType
    have hfreshScope : fv ∉ tailScope.fvars := by
      rw [halignTail.fvars]
      exact hchkTailWF.tr.find?_eq_none.1 hfreshC
    have hNU' := hNU.symm.defeqDFC henv.ordered halignTailSymm.defeqCtx
    obtain ⟨v, hv⟩ := HnarrowIsType
    refine ⟨_, Hnext, ?_, ?_, ⟨tailDomains ++ [narrowType], ?_, ?_⟩, ?_⟩
    · simp [htailScopeFVars, TypeChecker.MLCtx.fvarRevList]
    · dsimp [Hnext, checkInductiveTypes.loopType.FrontScopeEmbedding.withIndex]
      simpa only [List.length_append, List.length_singleton,
        List.drop_succ_cons] using htailBase
    · simp [htailDomains]
    · dsimp [Hnext, checkInductiveTypes.loopType.FrontScopeEmbedding.withIndex]
      rw [htailFront]
      simp [List.append_assoc]
    · exact halignTail.consAligned hfreshScope hdeps
        (hNU'.of_l henv halignTail.wf.toCtx hv)

/-- A list of executable constants and abstract constants installed in lockstep.
Each translation and typing premise is stated in
the environment at the exact point where that constant is introduced. -/
inductive AddConstants (safety : DefinitionSafety) :
    Environment → VEnv → List (ConstantInfo × VConstVal) →
      Environment → VEnv → Prop
  | nil : AddConstants safety env venv [] env venv
  | cons :
    env.find? ci.name = none →
    ¬ Kernel.Environment.primitives.contains ci.name →
    TrConstVal safety venv ci ci' →
    ci'.toVConstant.WF venv →
    venv.addConst ci.name ci'.toVConstant = some venv' →
    ci.deltaValue? = none →
    AddConstants safety (env.add ci) venv' rest outEnv outVEnv →
    AddConstants safety env venv ((ci, ci') :: rest) outEnv outVEnv

theorem AddConstants.quotInit_eq
    (H : AddConstants safety prodEnv venv entries outEnv outVEnv) :
    outEnv.quotInit = prodEnv.quotInit := by
  induction H with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => exact ih

theorem CheckingEnv.exists_addConst
    (H : CheckingEnv safety env venv) (hn : env.find? name = none)
    (ci' : VConstant) :
    ∃ venv', venv.addConst name ci' = some venv' := by
  unfold VEnv.addConst
  cases hfind : venv.constants name with
  | none => simp
  | some ci =>
    exfalso
    rcases H.find?_iff.mpr ⟨ci, hfind⟩ with ⟨source, hsource, _⟩
    rw [hn] at hsource
    contradiction

/-- The inner executable constructor fold installs a translated constructor
list in lockstep with its abstract constants.  Constructor metadata is kept
parametric because only the source name, type, level parameters, and safety
participate in the translation relation. -/
inductive ConstructorListEntries
    (mkInfo : Nat → Constructor → ConstructorVal) :
    Nat → List Constructor → List (ConstantInfo × VConstVal) → Prop
  | nil : ConstructorListEntries mkInfo start [] []
  | cons : ConstructorListEntries mkInfo (start + 1) ctors entries →
      ConstructorListEntries mkInfo start (ctor :: ctors)
        ((.ctorInfo (mkInfo start ctor), value) :: entries)

/-- Family-major source alignment of the complete constructor-entry batch. -/
inductive ConstructorTypeEntries
    (mkInfo : InductiveType → Nat → Constructor → ConstructorVal) :
    List InductiveType → List (ConstantInfo × VConstVal) → Prop
  | nil : ConstructorTypeEntries mkInfo [] []
  | cons : ConstructorListEntries (mkInfo owner) 0 owner.ctors head →
      ConstructorTypeEntries mkInfo owners tail →
      ConstructorTypeEntries mkInfo (owner :: owners) (head ++ tail)

/-- A lockstep installation preserves the checking relation. -/
theorem AddConstants.checking
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hchecking : CheckingEnv safety env venv) :
    CheckingEnv safety outEnv outVEnv := by
  induction H with
  | nil => exact hchecking
  | cons hn _ htr hwf hadd hdelta _ ih =>
    exact ih (hchecking.add hn htr.1 hwf hadd hdelta)

/-- A lockstep installation preserves the local checking invariants. -/
theorem AddConstants.validCore
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hvalid : CheckingEnv.ValidCore safety env venv) :
    CheckingEnv.ValidCore safety outEnv outVEnv := by
  induction H with
  | nil => exact hvalid
  | cons hn hnprim htr hwf hadd hdelta _ ih =>
    exact ih (hvalid.add hn hnprim htr.1 hwf hadd hdelta)

theorem AddConstants.abstract
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    venv.addConstVals (entries.map Prod.snd) = some outVEnv := by
  induction H with
  | nil => simp [VEnv.addConstVals]
  | cons _ _ htr _ hadd _ _ ih =>
    rw [List.map_cons, VEnv.addConstVals, ← htr.2, hadd]
    exact ih

theorem AddConstants.existsEntryOfValue
    {entries : List (ConstantInfo × VConstVal)}
    (hvalue : value ∈ entries.map Prod.snd) :
    ∃ info, (info, value) ∈ entries := by
  rcases List.mem_map.mp hvalue with ⟨⟨info, entryValue⟩, hentry, heq⟩
  simp only at heq
  subst entryValue
  exact ⟨info, hentry⟩

theorem AddConstants.le
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    venv ≤ outVEnv :=
  VEnv.addConstVals_le H.abstract

/-- A lockstep installation preserves lookups from its source kernel
environment. This low-level form is kept with `AddConstants`
so positional entry lookup does not depend on the nested compilation layer. -/
theorem AddConstants.preservesSourceFind
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hfind : env.find? name = some found) :
    outEnv.find? name = some found := by
  induction H with
  | nil => exact hfind
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    have hne : ci.name ≠ name := by
      intro heq
      subst name
      rw [hfind] at hn
      contradiction
    have hfreshMap : envHead.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    have hnextWF : (envHead.add ci).constants.WF := by
      change (envHead.constants.insert ci.name ci).WF
      exact hwf.insert ci.name ci hfreshMap
    apply ih hnextWF
    rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfind
    change (envHead.constants.insert ci.name ci).find?' name = some found
    rw [(hwf.insert ci.name ci hfreshMap).find?'_eq_find?, hwf.find?_insert]
    split
    · rename_i heq
      exact False.elim (hne (by simpa using heq))
    · exact hfind

theorem AddConstants.targetMapWF
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF) : outEnv.constants.WF := by
  induction H with
  | nil => exact hwf
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    have hfresh : envHead.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    exact ih (hwf.insert ci.name ci hfresh)

/-- A lockstep installation adds no stored equation. -/
theorem AddConstants.defeqs
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    ∀ df, outVEnv.defeqs df → venv.defeqs df := by
  induction H with
  | nil => exact fun _ h => h
  | cons _ _ _ _ hadd _ _ ih =>
    intro df hdf
    rw [← VEnv.addConst_defeqs hadd]
    exact ih df hdf

/-- Every entry of a lockstep fold is fresh in the fold's source
environment. -/
theorem AddConstants.entryFresh
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hentry : (info, value) ∈ entries) :
    env.find? info.name = none := by
  induction H with
  | nil => simp at hentry
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    simp only [List.mem_cons, Prod.mk.injEq] at hentry
    rcases hentry with ⟨rfl, rfl⟩ | htail
    · exact hn
    · have hfreshMap : envHead.constants.find? ci.name = none := by
        rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
      have hnextWF : (envHead.add ci).constants.WF := by
        change (envHead.constants.insert ci.name ci).WF
        exact hwf.insert ci.name ci hfreshMap
      have hnext := ih hnextWF htail
      cases hfind : envHead.find? info.name with
      | none => rfl
      | some found =>
        exfalso
        have hne : ci.name ≠ info.name := by
          intro heq
          rw [← heq, hn] at hfind
          contradiction
        have hpreserved : (envHead.add ci).find? info.name = some found := by
          rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfind
          change (envHead.constants.insert ci.name ci).find?' info.name =
            some found
          rw [(hwf.insert ci.name ci hfreshMap).find?'_eq_find?,
            hwf.find?_insert]
          split
          · rename_i heq
            exact False.elim (hne (by simpa using heq))
          · exact hfind
        rw [hpreserved] at hnext
        contradiction

/-- Every lookup in the output kernel environment either existed before the lockstep fold
or is one of its entries. -/
theorem AddConstants.entryOrigin
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hfind : outEnv.find? name = some found) :
    env.find? name = some found ∨
      ∃ entry ∈ entries, name = entry.1.name ∧ found = entry.1 := by
  induction H with
  | nil => exact Or.inl hfind
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    have hfreshMap : envHead.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    have hnextWF : (envHead.add ci).constants.WF := by
      change (envHead.constants.insert ci.name ci).WF
      exact hwf.insert ci.name ci hfreshMap
    rcases ih hnextWF hfind with hnext | ⟨entry, hentry, hname, hfound⟩
    · change (envHead.add ci).constants.find?' name = some found at hnext
      rw [hnextWF.find?'_eq_find?] at hnext
      change (envHead.constants.insert ci.name ci).find? name =
        some found at hnext
      rw [hwf.find?_insert] at hnext
      split at hnext
      · rename_i heq
        right
        simp only [Option.some.injEq] at hnext
        have hname : name = ci.name := (LawfulBEq.eq_of_beq heq).symm
        exact ⟨(ci, ci'), by simp, hname, hnext.symm⟩
      · left
        rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]
    · exact Or.inr ⟨entry, by simp [hentry], hname, hfound⟩

/-- Every executable entry of an `AddConstants` installation is present
with its exact metadata in the output environment. -/
theorem AddConstants.findEntry
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hentry : (info, value) ∈ entries) :
    outEnv.find? info.name = some info := by
  induction H with
  | nil => simp at hentry
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    simp only [List.mem_cons] at hentry
    have hfreshMap : envHead.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    have hnextWF : (envHead.add ci).constants.WF := by
      change (envHead.constants.insert ci.name ci).WF
      exact hwf.insert ci.name ci hfreshMap
    rcases hentry with hhead | htail
    · have hinstalled : outProd.find? ci.name = some ci := by
        apply Htail.preservesSourceFind hnextWF
        change (Lean4Lean.AddInductive.addConstant envHead ci).find? ci.name =
          some ci
        change (envHead.constants.insert ci.name ci).find?' ci.name = some ci
        rw [(hwf.insert ci.name ci hfreshMap).find?'_eq_find?, hwf.find?_insert]
        simp
      have hi : info = ci := congrArg Prod.fst hhead
      simpa [hi] using hinstalled
    · exact ih hnextWF htail

/-- Installing a batch containing no inductive headers preserves the
constructor-parameter agreement `ConstructorParameterAlignment`. Exact kernel-environment lookups are
transported through the lockstep fold; all abstract judgments use
the larger target environment of the same installation. -/
theorem AddConstants.preservesConstructorTyping
    (H : AddConstants installSafety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (Hsource : ConstructorParameterAlignment
      observer env venv)
    (hnind : ∀ (info : ConstantInfo) (value : VConstVal),
      (info, value) ∈ entries → ∀ inductiveValue,
        info ≠ .inductInfo inductiveValue) :
    ConstructorParameterAlignment observer outEnv outVEnv := by
  intro familyName familyInfo hfamily hvisible i hi
  rcases H.entryOrigin hwf hfamily with hold | hnew
  · rcases Hsource familyName familyInfo hold hvisible i hi with ⟨C⟩
    exact ⟨C.rebaseKernel (H.preservesSourceFind hwf C.lookup) H.le⟩
  · rcases hnew with ⟨entry, hentry, _hname, hinfo⟩
    exact False.elim (hnind entry.1 entry.2 hentry familyInfo hinfo.symm)

/-- Refinement of the executable recursor loop `declareRecursors.loop`. In addition to
the generated entries (`GeneratedRecursorsRange`) and their installation (`AddConstants`),
every recursor entry carries its typed rules (`TypedRecursorRulesRange`): the field
classification and recursive calls of each generated iota rule. -/
theorem AddInductive.declareRecursors.loop.typingWF
    {sourceVEnv currentVEnv envTypes envCtors : VEnv}
    {decl : VInductDecl} {indTypes : Array InductiveType}
    {parameterDecls : VLCtx}
    {recursors : Nat → VConstVal}
    (Hcard : RecursorCounts stats recInfos decl)
    (Hdecl : TrInductDeclCore sourceEnv lparams nparams
      indTypes.toList sourceIsUnsafe decl envTypes envCtors)
    {recLparams : List Name} {depth : Nat}
    (c : AddInductive.Context) (R : RecursorContextWF c recLparams)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams R.mlctx.vlctx
      stats decl depth)
    (hconsume : ConsumeTypeAnnotationsDefEq)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoBinderTypes c recInfos)
    (Hblueprints : RuleTemplatesMatch stats recInfos Horigins)
    (HblueprintSemantics : TypedRuleTemplates R decl stats
      recInfos elimLevel parameterDecls Horigins)
    (HminorSources : MinorsAndIndicesMatchSource stats indTypes Horigins)
    (HminorSemantics : TypedMinors R Horigins
      parameterDecls)
    (Hparams : FVarArrayIn c stats.params)
    (hnoalias : RecInfoBindings.NoAlias stats.params recInfos)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (hparameterUp : IsFVarUpSet
      (fun fv => fv ∈ ExprArrayFVarIds stats.params) R.mlctx.vlctx)
    (Hseed : ∀ owner (_howner : owner < indTypes.size),
      ∀ ctor, ctor ∈ indTypes[owner]!.ctors →
        ∃ tail tailTarget introTarget,
          ParameterPrefix stats 0 ctor.type tail ∧
          Nonempty
            (ConstructorOwnerNormalForm stats owner tail) ∧
          tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
          TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget ∧
          R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx tailTarget ∧
          TrExprS R.venv recLparams R.mlctx.vlctx
            (mkAppN (.const ctor.name stats.levels) stats.params)
            introTarget ∧
          R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx introTarget
            tailTarget)
    (numMinors numMotives : Nat) (all : List Name)
    (hnumMinors : numMinors = (recInfos.flatMap (·.minors)).size)
    (hnumMotives : numMotives = (recInfos.map (·.motive)).size)
    (k isUnsafe : Bool) (allowPrimitive : Bool)
    (hisUnsafe : isUnsafe = (c.safety != .safe))
    (hall : all = (indTypes.map (·.name)).toList)
    (hk : KEligible stats indTypes k)
    (dIdx : Nat) (hdone : dIdx ≤ indTypes.size)
    (env : Environment)
    (Hvalid : CheckingEnv.ValidCore c.safety env currentVEnv)
    (hle : sourceVEnv ≤ currentVEnv)
    (Htranslate : ∀ owner (_howner : owner < indTypes.size)
      (rules : List RecursorRule),
      TrConstVal c.safety sourceVEnv
          (.recInfo (AddInductive.declareRecursors.recursorInfo stats
            indTypes elimLevel recInfos numMinors numMotives all c.lctx k
            isUnsafe lparams owner rules)) (recursors owner) ∧
        (recursors owner).toVConstant.WF sourceVEnv)
    (hnprim : allowPrimitive = true →
      ∀ owner (_howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName indTypes[owner]!.name)) :
    (AddInductive.declareRecursors.loop stats indTypes elimLevel recInfos
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) numMinors
      numMotives all c.lctx k isUnsafe lparams allowPrimitive dIdx env
      (recursorMinorOffset indTypes dIdx) c).WF fun out =>
        ∃ outVEnv : VEnv,
        ∃ entries : List (ConstantInfo × VConstVal),
          out.2 = recursorMinorOffset indTypes indTypes.size ∧
          Nonempty (GeneratedRecursorsRange c.safety sourceVEnv lparams
            elimLevel c stats indTypes recInfos dIdx entries) ∧
          Nonempty (TypedRecursorRulesRange R decl stats
            indTypes recInfos Horigins elimLevel parameterDecls dIdx entries) ∧
          AddConstants c.safety env currentVEnv entries out.1 outVEnv ∧
          ∀ i (hi : i < entries.length), entries[i].2 = recursors (dIdx + i) := by
  rw [AddInductive.declareRecursors.loop]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    have Hrules := AddInductive.mkRecRulesFromTemplates.WF indTypes
      elimLevel stats recInfos dIdx (recInfos.map (·.motive))
      (recInfos.flatMap (·.minors)) c
    have HrulesState :
        ((liftM (AddInductive.mkRecRulesFromTemplates indTypes elimLevel
          stats recInfos dIdx (recInfos.map (·.motive))
          (recInfos.flatMap (·.minors))) :
            StateT Nat AddInductive.M (List RecursorRule))
          (recursorMinorOffset indTypes dIdx) c).WF fun out =>
            (out.1 = recInfos[dIdx]!.ruleTemplates.toList.map fun blueprint =>
              blueprint.instantiate indTypes stats (recInfos.map (·.motive))
                (recInfos.flatMap (·.minors))
                (AddInductive.getRecLevels elimLevel stats.levels) c.lctx) ∧
            out.2 = recursorMinorOffset indTypes dIdx := by
      change (((fun rules => (rules, recursorMinorOffset indTypes dIdx)) <$>
        AddInductive.mkRecRulesFromTemplates indTypes elimLevel stats
          recInfos dIdx (recInfos.map (·.motive))
          (recInfos.flatMap (·.minors)) c).WF _)
      exact Hrules.map fun _ hrules => ⟨hrules, rfl⟩
    simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift, bind,
      StateT.bind, ReaderT.bind, pure, ReaderT.pure,
      _root_.modify, MonadState.modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet]
    exact HrulesState.bind fun generated hrules => by
      have hsize : recInfos.size = indTypes.size := by
        rw [Hcard.records]
        simpa using
          (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl).symm
      have HgeneratedPair := Hblueprints.boundGeneratedRules
        HminorSources elimLevel HblueprintSemantics HminorSemantics Hbindings
        Hparams hnoalias hsize hcounts dIdx hidx
      rw [← hrules.1] at HgeneratedPair
      rcases HgeneratedPair with
        ⟨Hgenerated, ⟨HgeneratedMotive⟩, HgeneratedOrigins⟩
      let info := AddInductive.declareRecursors.recursorInfo stats indTypes
        elimLevel recInfos numMinors numMotives all c.lctx k isUnsafe
        lparams dIdx generated.1
      have hinfoName : info.name = Lean.mkRecName indTypes[dIdx]!.name := rfl
      have hstateNext : generated.2 + indTypes[dIdx]!.ctors.length =
          recursorMinorOffset indTypes (dIdx + 1) := by
        rw [hrules.2, recursorMinorOffset_step indTypes dIdx hidx]
      have hnormalize :
          ((env.checkName info.name allowPrimitive).bind fun a =>
            Except.pure (a, generated.2 + indTypes[dIdx]!.ctors.length)).bind (fun checked =>
              AddInductive.declareRecursors.loop stats indTypes elimLevel
                recInfos (recInfos.map (·.motive))
                (recInfos.flatMap (·.minors)) numMinors numMotives all c.lctx
                k isUnsafe lparams allowPrimitive (dIdx + 1)
                (AddInductive.addConstant env (.recInfo info)) checked.2 c) =
          (env.checkName info.name allowPrimitive).bind (fun _ =>
              AddInductive.declareRecursors.loop stats indTypes elimLevel
                recInfos (recInfos.map (·.motive))
                (recInfos.flatMap (·.minors)) numMinors numMotives all c.lctx
                k isUnsafe lparams allowPrimitive (dIdx + 1)
                (AddInductive.addConstant env (.recInfo info))
                  (recursorMinorOffset indTypes (dIdx + 1)) c) := by
        rw [hstateNext]
        cases env.checkName info.name allowPrimitive <;> rfl
      refine Except.WF.pureBind ?_
      rw [hnormalize]
      have Hname := checkName.WF Hvalid.tr.map_wf info.name allowPrimitive
      exact Hname.bind fun _ Hchecked => by
          let recursor := recursors dIdx
          rcases Htranslate dIdx hidx generated.1 with
            ⟨HtrSource, HwfSource⟩
          rcases CheckingEnv.exists_addConst Hvalid.tr Hchecked.1
              recursor.toVConstant with ⟨nextVEnv, hadd⟩
          have Htr : TrConstVal c.safety currentVEnv (.recInfo info) recursor :=
            HtrSource.mono hle
          have Hwf : recursor.toVConstant.WF currentVEnv :=
            HwfSource.mono hle
          have hname : info.name = recursor.name := Htr.2
          have haddInfo :
              currentVEnv.addConst info.name recursor.toVConstant =
                some nextVEnv := by
            simpa [hname] using hadd
          have hnprimInfo :
              ¬ Kernel.Environment.primitives.contains
                (ConstantInfo.recInfo info).name := by
            change ¬ Kernel.Environment.primitives.contains info.name
            cases hallow : allowPrimitive with
            | false =>
              intro hp
              have := Hchecked.2 hp
              simp [hallow] at this
            | true =>
              simpa [ConstantInfo.name, ConstantInfo.toConstantVal, info,
                AddInductive.declareRecursors.recursorInfo] using
                hnprim hallow dIdx hidx
          have HnextValid : CheckingEnv.ValidCore c.safety
              (env.add (.recInfo info)) nextVEnv :=
            Hvalid.add (ci := .recInfo info) Hchecked.1 hnprimInfo Htr.1 Hwf
              haddInfo rfl
          have hnextLe : sourceVEnv ≤ nextVEnv :=
            hle.trans (VEnv.addConst_le haddInfo)
          have Htail := AddInductive.declareRecursors.loop.typingWF Hcard
            Hdecl c R Hstats hconsume hlit hctx Hbindings Horigins
            Hblueprints HblueprintSemantics HminorSources HminorSemantics
            Hparams hnoalias hcounts hparameterUp Hseed numMinors numMotives
            all hnumMinors hnumMotives k isUnsafe
            allowPrimitive hisUnsafe hall hk (dIdx + 1) (by omega)
            (env.add (.recInfo info)) HnextValid hnextLe Htranslate hnprim
          exact Htail.mono fun out Hout => by
            rcases Hout with
              ⟨outVEnv, entries, hstate, ⟨Hrange⟩, ⟨HsemRange⟩,
                Hinstalled, Htargets⟩
            let entry : ConstantInfo × VConstVal := (.recInfo info, recursor)
            have Hentry : GeneratedRecursorEntry c.safety sourceVEnv lparams
                elimLevel c stats indTypes recInfos dIdx entry := by
              exact GeneratedRecursorEntry.ofRecursorInfo c.safety sourceVEnv
                lparams elimLevel c stats indTypes recInfos numMinors
                numMotives all hnumMinors hnumMotives k isUnsafe dIdx
                generated.1 recursor hisUnsafe hall hk
                HtrSource
                Hgenerated.bound hrules.1
            have Hrange' : GeneratedRecursorsRange c.safety sourceVEnv
                lparams elimLevel c stats indTypes recInfos dIdx
                (entry :: entries) := by
              refine {
                covered := by
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    Hrange.covered
                entry := ?_ }
              intro i hi
              cases i with
              | zero => simpa [entry] using Hentry
              | succ i =>
                have hi' : i < entries.length := by simpa using hi
                simpa [Nat.add_assoc, Nat.add_comm 1 i] using Hrange.entry i hi'
            have HsemRange' : TypedRecursorRulesRange R decl
                stats indTypes recInfos Horigins elimLevel parameterDecls dIdx
                (entry :: entries) := by
              refine {
                covered := by
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    HsemRange.covered
                entry := ?_ }
              intro i hi
              cases i with
              | zero =>
                exact ⟨info, by simp [entry], Hgenerated, ⟨by
                  simpa [info, AddInductive.declareRecursors.recursorInfo]
                    using HgeneratedMotive, by
                  intro localIndex hctor hrule
                  exact HgeneratedOrigins localIndex hctor hrule⟩⟩
              | succ i =>
                have hi' : i < entries.length := by simpa using hi
                have HtailEntry := HsemRange.entry i hi'
                have hownerOffset : dIdx + 1 + i = dIdx + (i + 1) := by
                  omega
                rw [hownerOffset] at HtailEntry
                rcases HtailEntry with
                  ⟨tailInfo, htailInfo, HtailRules, HtailMotive,
                    HtailOrigins⟩
                refine ⟨tailInfo, htailInfo, HtailRules, HtailMotive, ?_⟩
                intro localIndex hctor hrule
                exact HtailOrigins localIndex hctor hrule
            have Hinstalled' : AddConstants c.safety env currentVEnv
                (entry :: entries) out.1 outVEnv := by
              exact AddConstants.cons Hchecked.1
                hnprimInfo Htr Hwf haddInfo rfl Hinstalled
            refine ⟨outVEnv, entry :: entries, hstate, ⟨Hrange'⟩,
              ⟨HsemRange'⟩, Hinstalled', ?_⟩
            intro i hi
            cases i with
            | zero => rfl
            | succ i =>
              simpa [Nat.add_assoc, Nat.add_comm 1 i] using Htargets i (by simpa using hi)
  · rw [dif_neg hidx]
    have heq : dIdx = indTypes.size := by omega
    subst dIdx
    exact Except.WF.pure ⟨currentVEnv, [], rfl, ⟨
      { covered := by simpa [Hcard.records] using
          (show indTypes.size = recInfos.size from by
            have htypes := Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
              Hdecl
            have hsize : indTypes.size = decl.types.length := by
              simpa using htypes
            rw [hsize, ← Hcard.records])
        entry := by intro i hi; simp at hi }⟩, ⟨
      { covered := by simpa [Hcard.records] using
          (show indTypes.size = recInfos.size from by
            have htypes := Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
              Hdecl
            have hsize : indTypes.size = decl.types.length := by
              simpa using htypes
            rw [hsize, ← Hcard.records])
        entry := by intro i hi; simp at hi }⟩,
      .nil, by intro i hi; simp at hi⟩
termination_by indTypes.size - dIdx

/-- Install the chosen generator targets through the executable recursor declaration pass.
The executable's type check supplies their typing; the result records that every entry is
exactly its target, alongside the typed rules. -/
theorem AddInductive.declareRecursors.bindingWFOfTargets
    {envTypes envCtors : VEnv} {decl : VInductDecl}
    {indTypes : Array InductiveType} {parameterDecls : VLCtx}
    {currentVEnv : VEnv} {recLparams : List Name} {depth : Nat}
    (k : Bool)
    (hk : KEligible stats indTypes k)
    (Hvalid : CheckerEnv c.safety c.env currentVEnv)
    (R : RecursorContextWF c recLparams)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams R.mlctx.vlctx
      stats decl depth)
    (hconsume : ConsumeTypeAnnotationsDefEq)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (Hcard : RecursorCounts stats recInfos decl)
    (Hdecl : TrInductDeclCore sourceEnv c.lparams nparams
      indTypes.toList sourceIsUnsafe decl envTypes envCtors)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoBinderTypes c recInfos)
    (Hblueprints : RuleTemplatesMatch stats recInfos Horigins)
    (HblueprintSemantics : TypedRuleTemplates R decl stats
      recInfos elimLevel parameterDecls Horigins)
    (HminorSources : MinorsAndIndicesMatchSource stats indTypes Horigins)
    (HminorSemantics : TypedMinors R Horigins
      parameterDecls)
    (Hparams : FVarArrayIn c stats.params)
    (hnoalias : RecInfoBindings.NoAlias stats.params recInfos)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (hparameterUp : IsFVarUpSet
      (fun fv => fv ∈ ExprArrayFVarIds stats.params) R.mlctx.vlctx)
    (Hseed : ∀ owner (_howner : owner < indTypes.size),
      ∀ ctor, ctor ∈ indTypes[owner]!.ctors →
        ∃ tail tailTarget introTarget,
          ParameterPrefix stats 0 ctor.type tail ∧
          Nonempty
            (ConstructorOwnerNormalForm stats owner tail) ∧
          tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
          TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget ∧
          R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx tailTarget ∧
          TrExprS R.venv recLparams R.mlctx.vlctx
            (mkAppN (.const ctor.name stats.levels) stats.params)
            introTarget ∧
          R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx introTarget
            tailTarget)
    (targets : TrRecursorTypes currentVEnv c.lparams elimLevel c
      stats indTypes recInfos → Nat → VExpr)
    (Hcanonical : ∀ (T : TrRecursorTypes currentVEnv c.lparams elimLevel c
      stats indTypes recInfos) owner (_howner : owner < indTypes.size),
      TrExprS currentVEnv (AddInductive.getRecLevelParams elimLevel c.lparams) []
        (AddInductive.declareRecursors.recursorType stats recInfos c.lctx owner)
        (targets T owner))
    (hnotPartial : c.safety ≠ .partial)
    (hnprim : c.allowPrimitive = true →
      ∀ owner (_howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName indTypes[owner]!.name)) :
    (AddInductive.declareRecursors stats indTypes elimLevel recInfos k
      c.lparams c).WF
      fun outEnv =>
        ∃ outVEnv : VEnv,
        ∃ entries : List (ConstantInfo × VConstVal),
          Nonempty (GeneratedRecursors c.safety currentVEnv c.lparams
            elimLevel c stats indTypes recInfos entries) ∧
          Nonempty (TypedRecursorRulesRange R decl stats
            indTypes recInfos Horigins elimLevel parameterDecls 0 entries) ∧
          AddConstants c.safety c.env currentVEnv entries outEnv
            outVEnv ∧
          ∃ T : TrRecursorTypes currentVEnv c.lparams elimLevel c
            stats indTypes recInfos,
          ∀ i (hi : i < entries.length), entries[i].2 = {
            name := Lean.mkRecName indTypes[i]!.name
            uvars := (AddInductive.getRecLevelParams elimLevel c.lparams).length
            type := targets T i } := by
  unfold AddInductive.declareRecursors
  simp only [getLCtx, readThe, read]
  simp only [bind, ReaderT.bind]
  have Hcheck :
        (AddInductive.declareRecursors.checkRecursorTypes stats indTypes
          elimLevel recInfos (recInfos.flatMap (·.minors)).size
          (recInfos.map (·.motive)).size (indTypes.map (·.name)).toList
          c.lctx k (c.safety != .safe) c.lparams 0 c).WF fun _ =>
            TrRecursorTypes currentVEnv c.lparams elimLevel c
              stats indTypes recInfos := by
      simpa using
        (AddInductive.declareRecursors.checkRecursorTypes.trRecursorTypesWF
          Hvalid hnotPartial stats indTypes elimLevel recInfos
          (recInfos.flatMap (·.minors)).size
          (recInfos.map (·.motive)).size
          (indTypes.map (·.name)).toList c.lctx k (c.safety != .safe)
          c.lparams)
  refine Hcheck.bind fun _ Htypes => ?_
  have Hloop := AddInductive.declareRecursors.loop.typingWF
      (elimLevel := elimLevel) Hcard Hdecl c R Hstats hconsume hlit
      hctx Hbindings Horigins Hblueprints HblueprintSemantics
      HminorSources HminorSemantics Hparams hnoalias hcounts hparameterUp Hseed
      (recInfos.flatMap (·.minors)).size
      (recInfos.map (·.motive)).size (indTypes.map (·.name)).toList
      rfl rfl k
      (c.safety != .safe) c.allowPrimitive rfl rfl hk 0 (by omega) c.env
      Hvalid.toValidCore VEnv.LE.rfl
      (fun owner howner rules => Htypes.recursorInfoTranslationOfTarget
        Hvalid.tr.wf k owner howner rules (Hcanonical Htypes owner howner)) hnprim
  change ((Prod.fst <$> AddInductive.declareRecursors.loop stats indTypes
      elimLevel recInfos (recInfos.map (·.motive))
      (recInfos.flatMap (·.minors)) (recInfos.flatMap (·.minors)).size
      (recInfos.map (·.motive)).size (indTypes.map (·.name)).toList c.lctx
      k (c.safety != .safe) c.lparams c.allowPrimitive 0 c.env 0 c).WF _)
  exact Hloop.map fun out Hout => by
    rcases Hout with
      ⟨outVEnv, entries, _hstate, ⟨Hrange⟩, ⟨HsemRange⟩,
        Hinstalled, Htargets⟩
    have hsize : entries.length = recInfos.size := by
      simpa using Hrange.covered
    exact ⟨outVEnv, entries, ⟨Hrange.atZero hsize⟩, ⟨HsemRange⟩,
      Hinstalled, Htypes, by simpa using Htargets⟩

end VerifyInductive
end Lean4Lean
