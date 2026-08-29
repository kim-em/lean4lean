import Lean4Lean.Verify.Inductive.CompletedConstructorReplay
import Lean4Lean.Verify.Inductive.Nested.Compilation
import Lean4Lean.Verify.Inductive.Recursor.ReplayCompat
import Lean4Lean.Verify.Inductive.TypeAnnotations

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Complete output of the executable recursor suffix, indexed only by the
sound completed-constructor boundary.  In particular, this result does not
require a valid header-only environment or an ordinary `AddConstants` trace
for primitive family and constructor names. -/
structure CompletedRecursorPhasesResult
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv : Environment}
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (outEnv : Environment) where
  elimLevel : Level
  elimLevelAdmissible : AddInductive.AdmissibleElimLevel c.lparams elimLevel
  lparamsNodup : c.lparams.Nodup
  recInfos : Array AddInductive.RecInfo
  localContext : AddInductive.Context
  localWF : BindingContextWF localContext
  localExtends : BindingContextLE { c with
    env := ctorEnv
    typeCheckerLParams := some <|
      AddInductive.getRecLevelParams elimLevel c.lparams } localContext
  recursorDepth : Nat
  recursorWF : RecursorContextWF localContext
    (AddInductive.getRecLevelParams elimLevel c.lparams)
  recursorEnv : recursorWF.venv = R.context.venv
  parameterSuffix : RecursorParameterContextSuffix recursorWF stats
    recursorDepth
  parameterDecls : parameterSuffix.parameterDecls =
    (R.materializedFinal.parameterSuffix.toRecursorContext
      elimLevelAdmissible).parameterDecls
  validStats : RecursorValidAppStatsWF recursorWF.venv
    (AddInductive.getRecLevelParams elimLevel c.lparams)
    recursorWF.mlctx.vlctx stats decl recursorDepth
  noIndConsts : VLCtx.NoIndConsts (decl.types.map (·.name))
    recursorWF.mlctx.vlctx
  bindings : RecInfoBindings localContext recInfos
  origins : RecInfoTypeOrigins localContext recInfos
  blueprints : RecInfoRuleBlueprintOrigins stats recInfos origins
  blueprintSemantics : RecInfoRuleBlueprintSemanticOrigins recursorWF decl
    stats recInfos elimLevel parameterSuffix.parameterDecls origins
  minorSources : RecInfoMinorSourceAlignment stats indTypes origins
  minorSemantics : RecInfoMinorSemanticAlignment recursorWF origins
    parameterSuffix.parameterDecls
  majorTypes : RecursorTranslatedOriginTypes recursorWF origins.majorTypes
  majorShapes : RecInfoMajorTypeShapes stats recInfos origins.majorTypes
  motiveTypes : RecursorTranslatedOriginTypes recursorWF origins.motiveTypes
  motiveShapes : RecInfoMotiveTypeShapes localContext recInfos
    origins.motiveTypes elimLevel
  motiveTelescopes : RecInfoMotiveTelescopes recursorWF stats decl
    (R.materializedFinal.parameterSuffix.toRecursorContext
      elimLevelAdmissible).parameterDecls.toCtx recInfos elimLevel
  indexRows : RecursorTranslatedOriginTypeRows recursorWF origins.indexTypes
  params : BoundFVarArray localContext stats.params
  noAlias : bindings.NoAlias params
  outerOrder : RecInfoOuterOrder recursorWF params bindings
  arities : RecInfoArities stats recInfos
  minorCounts : forall i, i < recInfos.size ->
    recInfos[i]!.minors.size = indTypes[i]!.ctors.length
  cardinality : RecursorCardinalityCertificate stats recInfos decl
  outVEnv : VEnv
  entries : List (ConstantInfo × VConstVal)
  generated : GeneratedRecursors localContext.safety R.context.venv
    localContext.lparams elimLevel localContext stats indTypes recInfos entries
  ruleSemantics : GeneratedRecursorRuleSemanticsRange
    recursorWF decl stats indTypes recInfos origins elimLevel
      parameterSuffix.parameterDecls 0 entries
  installed : AddConstants localContext.safety localContext.env
    R.context.venv entries outEnv outVEnv
  closed : MutualInductivesClosed outEnv

/-- The concrete constructor and recursor installation traces preserve the
persistent constructor-owner invariant through the complete inductive block.
Constructor entries obtain owners from the formation trace, while generated
recursor entries are definitionally `recInfo` and therefore add no new
constructor metadata. -/
theorem CompletedRecursorPhasesResult.constructorOwnersPresent
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (hsource : ConstructorOwnersPresent c.env) :
    ConstructorOwnersPresent outEnv := by
  have hctor : ConstructorOwnersPresent H.localContext.env := by
    rw [H.localExtends.env_eq]
    exact R.constructorOwnersPresent hsource
  have hwf : H.localContext.env.constants.WF := by
    rw [H.localExtends.env_eq]
    exact R.context.checking.tr.map_wf
  apply (AtomicAddConstants.ofAddConstants H.installed).constructorOwnersPresent
    hwf hctor
  intro entry hentry info hinfo
  have hne := H.generated.nonConstructor entry.1 entry.2 (by simpa using hentry) info
  exact False.elim (hne hinfo)

/-- The exact `getElimLevel`/`mkRecInfos`/`declareRecursors` suffix, entered
from a completed and valid constructor context.  This is shared by ordinary
and atomic primitive formation. -/
theorem CompletedConstructorPhases.recursorPhasesWF
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv : Environment}
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (hclosed : MutualInductivesClosed ctorEnv)
    (hlparams : c.lparams.Nodup)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hnotPartial : c.safety ≠ .partial)
    (hnprim : c.allowPrimitive = true ->
      forall owner (howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName indTypes[owner]!.name)) :
    ((AddInductive.getElimLevel stats indTypes >>= fun elimLevel =>
      AddInductive.withTypeCheckerLParams
        (AddInductive.getRecLevelParams elimLevel c.lparams) do
        let kTarget ← AddInductive.isKTarget stats indTypes
        AddInductive.mkRecInfos stats indTypes elimLevel fun recInfos =>
          AddInductive.declareRecursors stats indTypes elimLevel recInfos
            kTarget c.lparams)
      { c with env := ctorEnv }).WF fun outEnv =>
        Nonempty (CompletedRecursorPhasesResult R outEnv) := by
  apply R.getElimLevelMkRecInfosWF hlparams
    Lean4Lean.recursorConsumeTypeAnnotationsCompat hlit
    (Q := fun outEnv => Nonempty (CompletedRecursorPhasesResult R outEnv))
    (k := fun elimLevel kTarget recInfos =>
      AddInductive.declareRecursors stats indTypes elimLevel recInfos kTarget
        c.lparams)
  intro elimLevel hElim kTarget localContext localDepth recInfos Rlocal henvLocal
    HsuffixLocal hparameterDeclsLocal HstatsLocal hctxLocal Hbindings
    Horigins Hblueprints HblueprintSemantics HminorSources HminorSemantics HmajorTypes HmajorShapes
    HmotiveTypes HmotiveShapes Htelescopes HindexRows Hparams hnoalias
    houterOrder Harities HminorCounts Hcard Hle
  have Hvalid : CheckingEnv.Valid localContext.safety localContext.env
      R.context.venv := by
    rw [Hle.safety_eq, Hle.env_eq]
    exact R.context.checking
  have Hcore : TrInductDeclCore sourceEnv localContext.lparams nparams
      indTypes.toList isUnsafe decl R.headerVEnv R.context.venv := by
    rw [Hle.lparams_eq]
    exact R.core
  have Hseed : forall owner (howner : owner < indTypes.size),
      forall ctor, ctor ∈ indTypes[owner]!.ctors ->
        exists tail tailTarget introTarget,
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
    HstatsLocal Lean4Lean.recursorConsumeTypeAnnotationsCompat
    hlit.available hctxLocal Hcard Hcore Hbindings
    Horigins Hblueprints HblueprintSemantics HminorSources HminorSemantics
    Hparams hnoalias HminorCounts HsuffixLocal.parameterFVarsUp Hseed (by
      rw [Hle.safety_eq]
      exact hnotPartial) (by
        intro hallow
        exact hnprim (Hle.allowPrimitive_eq ▸ hallow))
  have hclosedLocal : MutualInductivesClosed localContext.env := by
    rw [Hle.env_eq]
    exact hclosed
  have Hrecursors' :
      (AddInductive.declareRecursors stats indTypes elimLevel recInfos
        kTarget c.lparams localContext).WF fun outEnv =>
          ∃ outVEnv : VEnv,
          ∃ entries : List (ConstantInfo × VConstVal),
            Nonempty (GeneratedRecursors localContext.safety R.context.venv
              localContext.lparams elimLevel localContext stats indTypes
              recInfos entries) ∧
            Nonempty (GeneratedRecursorRuleSemanticsRange Rlocal decl stats
              indTypes recInfos Horigins elimLevel
                HsuffixLocal.parameterDecls 0 entries) ∧
            AddConstants localContext.safety localContext.env R.context.venv
              entries outEnv outVEnv := by
    simpa only [Hle.lparams_eq] using Hrecursors
  exact Hrecursors'.mono fun outEnv Hout => by
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
      bindings := Hbindings
      origins := Horigins
      blueprints := Hblueprints
      blueprintSemantics := HblueprintSemantics
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

end VerifyInductive
end Lean4Lean
