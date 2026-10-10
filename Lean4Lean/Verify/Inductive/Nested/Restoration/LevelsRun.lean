import Lean4Lean.Verify.Inductive.Nested.Restoration.Levels
import Lean4Lean.Verify.Inductive.Nested.Restoration.TableAgreement
import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceConstructorTypes

/-! The universe arguments of the lowered constructor types of a validated nested run
(the `NestedRun` part of the source's `Lowering/Levels.lean`). -/

namespace Lean4Lean

open InductiveSignature

namespace VerifyInductive

open Lean hiding Environment Exception
open Kernel

/-- **Universe arguments of the lowered constructor types of a validated
nested run.** Every auxiliary family or auxiliary constructor name occurs in
every lowered constructor type (of the source families and of the auxiliary
families alike) at the universe parameters of the declaration. -/
theorem NestedRun.loweredConstructorLevelsAll
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes) :
    ∀ lowered ∈ E.lowered.loweredDecl.types, ∀ lc ∈ lowered.ctors,
      lc.type.ConstLevelsAt
        (familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
        (VLevel.params sourceDecl.uvars) := by
  let names := familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length)
  -- the auxiliary names are fresh in the source header environment
  have hnodup :
      (familyNames E.lowered.loweredDecl.types ++
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  rcases E.restorationTablesRestoring wf Hsources with
    ⟨envTypes, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion,
      _hparamsSize, _D, _Hrestoring⟩
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hnames : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      names := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hfresh : ∀ name ∈ names, envTypes.constants name = none := by
    intro name hname
    apply hfreshAll
    rw [← hnames] at hname
    exact List.mem_append_left _ hname
  have HsourceCore := E.sourceCore.core
  rw [E.sourceCoreDecl_eq] at HsourceCore
  have htypesEq : E.sourceCore.envTypes = envTypes :=
    Option.some.inj (HsourceCore.typesAdded.symm.trans hadded)
  have hordered := henvTypes.ordered
  -- the lowering run and its translations
  let safety := if isUnsafe then DefinitionSafety.unsafe else .safe
  let P := E.lowered
  have henv : P.c.env = sourceProdEnv := E.lowered_env
  have hlparams : P.c.lparams = lparams := E.lowered_lparams
  have hnparams : P.nparams = nparams := E.lowered_nparams
  have hinitial : P.initialEnv = ves.venv safety := by
    simpa only [safety] using E.lowered_initialEnv
  have hisUnsafe : P.isUnsafe = isUnsafe := E.lowered_isUnsafe_source
  have HcP : ContextWF P.c := E.loweredContextWF
  let initialState := E.initialState
  have Hlower : NestedLoweringOutputClosed P.c.env
      E.validationFuel.inductiveFuel P.nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result := E.loweringAtContext
  rcases Hlower with ⟨finalState, Hrun, Hcache, Hparams⟩
  let Hpack := E.phases
  let R := Hpack.constructors
  let Hprod := Hpack.recursors
  have Hsource : TrInductDeclCore P.initialEnv P.c.lparams P.nparams
      sourceTypes P.isUnsafe sourceDecl E.sourceCore.envTypes
        E.sourceCore.envCtors := by
    simpa only [hinitial, hlparams, hnparams, hisUnsafe, safety,
      E.sourceCoreDecl_eq] using E.sourceCore.core
  have Htarget : TrInductDeclCore P.initialEnv P.c.lparams P.nparams
      result.types P.isUnsafe P.loweredDecl Hpack.headers.context.venv
        R.ctorVEnv := R.core
  have Hmetadata : SourcePrefixOfLowered sourceDecl P.loweredDecl := by
    simpa only [E.sourceCoreDecl_eq] using E.sourceCore.checked
  have wfP : ves.WF P.c.env := by
    simpa only [henv] using wf
  have HbaseWF : P.initialEnv.WF := by
    simpa only [hinitial, safety] using (wf.tr (safety := safety)).wf
  have HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst P.initialEnv P.c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (P.loweredDecl.types.take sourceTypes.length) := by
    simpa only [hinitial, hlparams, safety] using E.sourceCore.sourceHeaders
  have HsourceAdded : P.initialEnv.addConstVals
      ((P.loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some E.sourceCore.envTypes := by
    simpa only [hinitial, safety] using E.sourceCore.sourceAdded
  have HsourceTypesWF : E.sourceCore.envTypes.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF Hsource HbaseWF
  have HtargetTypesWF : Hpack.headers.context.venv.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF Htarget HbaseWF
  have Htranslations : ClosedNestedOccurrenceTypings
      E.sourceCore.envTypes P.c.lparams result E.auxiliarySelection := by
    rw [← E.auxiliaryVEnv_eq_sourceCore]
    simpa only [hlparams] using E.auxiliaryTranslations
  have hempty : initialState.nestedAux = #[] := rfl
  rcases Hrun.auxiliaryFamilySources (R := R) Hcache Hparams wfP
      hinitial HcP Hsources HsourceHeaders HsourceAdded HsourceTypesWF
      hempty E.auxiliarySelection Htranslations Htarget with ⟨N, -⟩
  have hparamsSize : result.params.size = P.nparams := Hrun.resultParamsSize
  have HliftLv : NestedExpansionLeafLiftAbove sourceDecl.nparams
      (VExpr.LevelLeaf names (VLevel.params sourceDecl.uvars)) :=
    VExpr.levelLeaf_liftAbove names (VLevel.params sourceDecl.uvars) sourceDecl.nparams
  have hsourceLength : sourceTypes.length = sourceDecl.types.length :=
    TrInductDeclCore.types_length Hsource
  have hloweredLength : result.types.length = P.loweredDecl.types.length :=
    TrInductDeclCore.types_length Htarget
  -- the source families
  have hprefix : ∀ lowered ∈ P.loweredDecl.types.take sourceDecl.types.length,
      ∀ lc ∈ lowered.ctors, lc.type.ConstLevelsAt names
        (VLevel.params sourceDecl.uvars) := by
    have hsourceFree : ∀ family ∈ sourceDecl.types, ∀ sc ∈ family.ctors,
        sc.type.containsAnyConst names = false := by
      intro family hfamily sc hsc
      obtain ⟨T, -, hT⟩ :=
        Lean4Lean.List.Forall₂.forall_exists_r HsourceCore.types family hfamily
      obtain ⟨C, -, hC⟩ := Lean4Lean.List.Forall₂.forall_exists_r hT.ctors sc hsc
      obtain ⟨u, hu⟩ := hC.wf
      rw [htypesEq] at hu
      exact (hu.noFreshConsts hordered hfresh (by intro _ h; simp at h)).1
    have Hexpansions := NestedLoweringOutputClosed.sourceExpansionsAboveLvls HliftLv
      ⟨finalState, Hrun, Hcache, Hparams⟩ Hsource Htarget Hmetadata Hsources hempty
      HbaseWF
      (fun Htrace Hctx selection _ Harity Hdepth _ HtargetParams _ HsourceExpr
          HtargetExpr hlvls =>
        Htrace.levelLeaf P.recursors.lparamsNodup Hsource.uvars
          (hparamsSize.trans Hsource.nparams.symm) HliftLv Hctx selection Harity
          Hdepth HtargetParams HsourceExpr HtargetExpr hlvls)
    intro lowered hlowered lc hlc
    obtain ⟨family, hfamily, Hfamily⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_r Hexpansions lowered hlowered
    obtain ⟨sc, hsc, Hctor⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_r Hfamily.constructors lc hlc
    exact Hctor.type.constLevelsAt (fun h => h) (hsourceFree family hfamily sc hsc)
  -- the auxiliary families
  have hsuffix : ∀ lowered ∈ P.loweredDecl.types.drop sourceDecl.types.length,
      ∀ lc ∈ lowered.ctors, lc.type.ConstLevelsAt names
        (VLevel.params sourceDecl.uvars) := by
    intro lowered hlowered lc hlc
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hlowered
    have hgeneratedLength := N.length
    simp only [List.length_drop] at hi
    have hresult : sourceTypes.length + i < result.types.length := by omega
    have htarget : sourceTypes.length + i < P.loweredDecl.types.length := by omega
    have hgenerated : i < N.generated.length := by omega
    have hloweredEq : lowered = P.loweredDecl.types[sourceTypes.length + i] := by
      rw [← hget, List.getElem_drop]
      congr 1
      omega
    rcases N.sourceAt i hgenerated hresult htarget with ⟨Horigin, Nsource, -⟩
    have HtargetType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
      Htarget (sourceTypes.length + i) hresult htarget
    have Hmap := Hrun.resultAuxMapModelsFresh (by simpa using hempty)
    have Hexpansion := Horigin.abstractExpansionAboveLvls HliftLv Nsource
      HtargetType Hmap HbaseWF Hsource.uvars HsourceTypesWF HtargetTypesWF
      Hrun.resultParamsSize Hsource.nparams.symm
      (fun Htrace Hctx selection _ Harity Hdepth _ HtargetParams _ HsourceExpr
          HtargetExpr hlvls =>
        Htrace.levelLeaf P.recursors.lparamsNodup Hsource.uvars
          (hparamsSize.trans Hsource.nparams.symm) HliftLv Hctx selection Harity
          Hdepth HtargetParams HsourceExpr HtargetExpr (hlvls.trans Hrun.lvls))
    rw [hloweredEq] at hlc
    obtain ⟨sc, hsc, Hctor⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_r Hexpansion.constructors lc hlc
    have hscFree : sc.type.containsAnyConst names = false := by
      obtain ⟨C, -, hC⟩ := Lean4Lean.List.Forall₂.forall_exists_r
        Nsource.translation.ctors sc hsc
      have h := hC.type
      rw [htypesEq] at h
      exact checkPositivityStep.TrExprS.noFreshConstsAtCheckingEnv henvTypes.orderedStrong hfresh
        (Delta := []) (by trivial) h
    exact Hctor.type.constLevelsAt (fun h => h) hscFree
  intro lowered hlowered
  rw [← List.take_append_drop sourceDecl.types.length P.loweredDecl.types] at hlowered
  rcases List.mem_append.mp hlowered with h | h
  · exact hprefix lowered h
  · exact hsuffix lowered h

/-- `loweredConstructorLevelsAll` for the source families. -/
theorem NestedRun.loweredConstructorLevels
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes) :
    ∀ lowered ∈ E.lowered.loweredDecl.types.take sourceDecl.types.length,
      ∀ lc ∈ lowered.ctors,
        lc.type.ConstLevelsAt
          (familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
          (VLevel.params sourceDecl.uvars) :=
  fun lowered hlowered =>
    E.loweredConstructorLevelsAll wf Hsources lowered (List.mem_of_mem_take hlowered)

/-- `loweredConstructorLevelsAll` for the auxiliary families. -/
theorem NestedRun.loweredAuxiliaryConstructorLevels
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes) :
    ∀ lowered ∈ E.lowered.loweredDecl.types.drop sourceDecl.types.length,
      ∀ lc ∈ lowered.ctors,
        lc.type.ConstLevelsAt
          (familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
          (VLevel.params sourceDecl.uvars) :=
  fun lowered hlowered =>
    E.loweredConstructorLevelsAll wf Hsources lowered (List.mem_of_mem_drop hlowered)

/-- `loweredConstructorLevels` at the restoration heads of any specialisation
list whose head names are the auxiliary family and constructor names (as for
the specialisations of `NestedRun.loweredConstructors_of_lowering`): the
universe-level premise of `loweredConstructors_of_lowering`. -/
theorem NestedRun.loweredConstructorLevels_heads
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    {auxiliaries : List ContainerSpecialization}
    (hheadNames : auxiliaries.flatMap (·.headNames) =
      familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length)) :
    ∀ lowered ∈ E.lowered.loweredDecl.types.take sourceDecl.types.length,
      ∀ lc ∈ lowered.ctors,
        lc.type.ConstLevelsAt
          ((compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary))
          (VLevel.params sourceDecl.uvars) := by
  rw [compilationRestoration_heads_auxiliary, hheadNames]
  exact E.loweredConstructorLevels wf Hsources

end VerifyInductive

end Lean4Lean
