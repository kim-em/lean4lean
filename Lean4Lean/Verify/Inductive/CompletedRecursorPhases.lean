import Lean4Lean.Verify.Inductive.CompletedRecursorConstruction
import Lean4Lean.Verify.Inductive.Recursor.CanonicalConstruction
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
    (outEnv : Environment) extends CompletedRecursorConstruction R where
  outVEnv : VEnv
  entries : List (ConstantInfo × VConstVal)
  generated : GeneratedRecursors localContext.safety
    R.context.venv
    localContext.lparams elimLevel localContext stats indTypes recInfos entries
  ruleSemantics : GeneratedRecursorRuleSemanticsRange
    recursorWF decl stats indTypes recInfos origins elimLevel
      parameterSuffix.parameterDecls 0 entries
  installed : AddConstants localContext.safety localContext.env
    R.context.venv
    entries outEnv outVEnv
  closed : MutualInductivesClosed outEnv
  canonicalTargets : ∀ i (hi : i < entries.length),
    entries[i].2 = toCompletedRecursorConstruction.nativeTarget i

/-- Installation retains the exact ordered generator output; equality is
established by choosing these targets before the loop, not by translation uniqueness. -/
theorem CompletedRecursorPhasesResult.canonicalRecursors
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    H.entries.map Prod.snd = H.toCompletedRecursorConstruction.generationInstance.recursors := by
  have hsize : H.entries.length = H.toCompletedRecursorConstruction.generationSignature.families.size := by
    rw [H.generated.length, H.cardinality.records]
    change decl.types.length = H.toCompletedRecursorConstruction.consumedGeneration.signature.families.size
    rw [H.toCompletedRecursorConstruction.consumedGeneration.familyCount]
    exact (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core).symm
  apply List.ext_getElem
  · simp [InductiveSignature.Instance.recursors, hsize]
  · intro i hi hi'
    have hiEntry : i < H.entries.length := by simpa using hi
    have hiFamily : i < H.toCompletedRecursorConstruction.generationSignature.families.size := by
      simpa [InductiveSignature.Instance.recursors] using hi'
    simp only [List.getElem_map]
    rw [H.canonicalTargets i hiEntry]
    simp [CompletedRecursorConstruction.nativeTarget, hiFamily,
      InductiveSignature.Instance.recursors]

/-- Every emitted recursor carries the single bit selected by the executable
K check before the recursor loop. -/
theorem CompletedRecursorPhasesResult.generated_k
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    (H.generated.entry owner howner).info.k = H.kTarget :=
  (H.generated.entry owner howner).kChecked.unique H.kTargetChecked
    H.localContext

/-- The installed recursor rules are literally the builds of the blueprints
retained by `mkRecInfos`, as `declareRecursors.loop` constructs them through
`mkRecRulesFromBlueprints` in the recursor-construction local context. -/
theorem CompletedRecursorPhasesResult.generated_rules_eq
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    (H.generated.entry owner howner).info.rules =
      H.recInfos[owner]!.ruleBlueprints.toList.map fun blueprint =>
        blueprint.build indTypes stats (H.recInfos.map (·.motive))
          (H.recInfos.flatMap (·.minors))
          (AddInductive.getRecLevels H.elimLevel stats.levels)
          H.localContext.lctx :=
  (H.generated.entry owner howner).rules_eq

/-- Each installed recursor has exactly one rule per retained blueprint. -/
theorem CompletedRecursorPhasesResult.generated_rules_length
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    (H.generated.entry owner howner).info.rules.length =
      H.recInfos[owner]!.ruleBlueprints.size := by
  rw [H.generated_rules_eq owner howner]
  simp

/-- Rule-wise form of `generated_rules_eq`. -/
theorem CompletedRecursorPhasesResult.rulesLiteral
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    (i : Nat) (hi : i < (H.generated.entry owner howner).info.rules.length) :
    (H.generated.entry owner howner).info.rules[i] =
      (H.recInfos[owner]!.ruleBlueprints[i]!).build indTypes stats
        (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
        (AddInductive.getRecLevels H.elimLevel stats.levels)
        H.localContext.lctx := by
  have hsize := H.generated_rules_length owner howner
  have hi' : i < H.recInfos[owner]!.ruleBlueprints.size := hsize ▸ hi
  simp only [H.generated_rules_eq owner howner, List.getElem_map,
    Array.getElem_toList, getElem!_pos H.recInfos[owner]!.ruleBlueprints i hi']

/-- The recursor safety metadata agrees with the source declaration because
both flags originate in the same declaration checking context. -/
theorem CompletedRecursorPhasesResult.generated_isUnsafe
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    (H.generated.entry owner howner).info.isUnsafe = decl.isUnsafe := by
  rw [(H.generated.entry owner howner).isUnsafe, H.localExtends.safety_eq,
    ← H.sourceSafety, R.core.isUnsafe]

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

/-- The recursor phase adds no constructor: every constructor of the output is old, or a new
constructor of the declaration with its safety flag and a certified type. -/
theorem CompletedRecursorPhasesResult.ctorOrigin
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (hfind : outEnv.find? name = some (.ctorInfo ci)) :
    c.env.find? name = some (.ctorInfo ci) ∨
      (ci.isUnsafe = isUnsafe ∧ CtorTelescopeAt R.headerVEnv ci) := by
  have hwf : H.localContext.env.constants.WF := by
    rw [H.localExtends.env_eq]
    exact R.context.checking.tr.map_wf
  have h := (AtomicAddConstants.ofAddConstants H.installed).ctors_of_noCtor hwf
    (fun e he info => H.generated.nonConstructor e.1 e.2 (by simpa using he) info) hfind
  rw [H.localExtends.env_eq] at h
  exact R.ctorOrigin h

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
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.context.venv stats.indConsts)
    {hsourceSafety : isUnsafe = (c.safety != .safe)}
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
  intro elimLevel hElim hElimRun kTarget hkTarget localContext localDepth recInfos Rlocal henvLocal
    HsuffixLocal hparameterDeclsLocal HstatsLocal hctxLocal Hbindings
    Horigins Hblueprints HblueprintSemantics HminorSources HminorSemantics HmajorTypes HmajorShapes
    HmotiveTypes HmotiveShapes Htelescopes HindexRows Hparams hnoalias
    houterOrder Harities HminorCounts Hcard Hle
  have Hvalid : CheckingEnv.Valid localContext.safety localContext.env
      R.context.venv := by
    rw [Hle.safety_eq, Hle.env_eq]
    exact R.context.checking
  have Hcore : TrInductDeclCore sourceEnv localContext.lparams nparams
      indTypes.toList isUnsafe decl R.headerVEnv R.ctorVEnv := by
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
        HtailType, Hintro, HintroType, _⟩
    exact ⟨tail, tailTarget, introTarget, Hprefix, Hnormal, HtailFVars,
      Htail, HtailType, Hintro, HintroType⟩
  let construction (T : RecursorTypeTranslations R.context.venv localContext.lparams
      elimLevel localContext stats indTypes recInfos) :
      CompletedRecursorConstruction R := {
    sourceSafety := hsourceSafety
    recursorTypes := T
    elimLevel := elimLevel
    elimLevelAdmissible := hElim
    elimLevelChecked := hElimRun
    lparamsNodup := hlparams
    kTarget := kTarget
    kTargetChecked := hkTarget
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
  }
  have Hrecursors := AddInductive.declareRecursors.bindingSemanticWFOfTargets
    (elimLevel := elimLevel) kTarget hkTarget Hvalid Rlocal.toBindingContextWF Rlocal
    HstatsLocal Lean4Lean.recursorConsumeTypeAnnotationsCompat
    (by simpa only [henvLocal] using hlit) hctxLocal Hcard Hcore Hbindings
    Horigins Hblueprints HblueprintSemantics HminorSources HminorSemantics
    Hparams hnoalias HminorCounts HsuffixLocal.parameterFVarsUp Hseed
    (fun T owner => ((construction T).nativeTarget owner).type) (by
      intro T owner howner
      simpa only [Hle.lparams_eq] using (construction T).canonicalTypeTranslations owner howner) (by
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
            Nonempty (GeneratedRecursors localContext.safety
              R.context.venv
              localContext.lparams elimLevel localContext stats indTypes
              recInfos entries) ∧
            Nonempty (GeneratedRecursorRuleSemanticsRange Rlocal decl stats
              indTypes recInfos Horigins elimLevel
                HsuffixLocal.parameterDecls 0 entries) ∧
            AddConstants localContext.safety localContext.env
              R.context.venv
              entries outEnv outVEnv ∧
            ∃ T : RecursorTypeTranslations R.context.venv localContext.lparams
              elimLevel localContext stats indTypes recInfos,
            ∀ i (hi : i < entries.length), entries[i].2 = {
              name := Lean.mkRecName indTypes[i]!.name
              uvars := (AddInductive.getRecLevelParams elimLevel c.lparams).length
              type := ((construction T).nativeTarget i).type } := by
    simpa only [Hle.lparams_eq] using Hrecursors
  exact Hrecursors'.mono fun outEnv Hout => by
    rcases Hout with
      ⟨outVEnv, entries, ⟨Hgenerated⟩, ⟨HruleSemantics⟩, Hinstalled, T, Htargets⟩
    exact ⟨{
      toCompletedRecursorConstruction := construction T
      outVEnv := outVEnv
      entries := entries
      generated := Hgenerated
      ruleSemantics := HruleSemantics
      installed := Hinstalled
      closed := Hgenerated.closesMutuals Hinstalled Hvalid.tr.map_wf
        hclosedLocal
      canonicalTargets := by
        intro i hi
        have hbound : i < indTypes.size := by
          have hc := Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hcore
          rw [Hgenerated.length, Hcard.records] at hi
          simp only [Array.length_toList] at hc
          omega
        rw [Htargets i hi]
        exact ((construction T).nativeTarget_eq i hbound).symm }⟩

end VerifyInductive
end Lean4Lean
