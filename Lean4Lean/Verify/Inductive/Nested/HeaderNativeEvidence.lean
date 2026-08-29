import Lean4Lean.Verify.Inductive.Nested.CanonicalRestorationReplay
import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterValidationSoundness

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-! # Native source-header reconstruction for nested declarations -/

/-- The original mutual headers form the literal prefix of the lowered
abstract block.  Splitting ordinary header installation at that queue
boundary constructs the source-shaped abstract header environment and the
complete positional source translation without choosing a source declaration
or translating any constructor. -/
theorem NestedLoweringResultClosed.sourceHeaderPrefix
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Htarget : TrInductDeclCore sourceVEnv lparams nparams result.types
      isUnsafe loweredDecl targetEnvTypes targetEnvCtors)
    (hempty : initialState.nestedAux = #[]) :
    ∃ sourceEnvTypes,
      sourceVEnv.addConstVals
          ((loweredDecl.types.take sourceTypes.length).map
            VInductiveType.toVConstVal) = some sourceEnvTypes ∧
      List.Forall₂
        (fun source target => TrSourceConst sourceVEnv lparams source.name
          source.type target.toVConstVal)
        sourceTypes (loweredDecl.types.take sourceTypes.length) := by
  have hsourceLE : sourceTypes.length ≤ result.types.length :=
    H.toResult.sourceTypes_length_le
  have hloweredLength : loweredDecl.types.length = result.types.length :=
    (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Htarget).symm
  have hprefixLength :
      (loweredDecl.types.take sourceTypes.length).length =
        sourceTypes.length := by
    simp [hloweredLength, hsourceLE]
  have htypeConstants : loweredDecl.typeConstants =
      (loweredDecl.types.take sourceTypes.length).map
          VInductiveType.toVConstVal ++
        (loweredDecl.types.drop sourceTypes.length).map
          VInductiveType.toVConstVal := by
    simp only [VInductDecl.typeConstants, ← List.map_append,
      List.take_append_drop]
  have htypesAdded := Htarget.typesAdded
  rw [htypeConstants] at htypesAdded
  rcases VEnv.addConstVals_append_inv htypesAdded with
    ⟨sourceEnvTypes, HsourceAdded, _HgeneratedAdded⟩
  refine ⟨sourceEnvTypes, HsourceAdded, ?_⟩
  apply List.forall₂_of_getElem hprefixLength.symm
  intro familyIdx hsource htarget
  have hfamily : familyIdx < sourceTypes.length := hsource
  rcases H.sourceHeaderTranslationAtFresh hempty Htarget familyIdx hfamily with
    ⟨hdecl, Hheader⟩
  have hdeclEq : hdecl =
      Nat.lt_of_lt_of_le hsource (by simpa [hloweredLength] using hsourceLE) :=
    Subsingleton.elim _ _
  subst hdecl
  simpa only [List.getElem_take] using Hheader

private theorem restoredHeaderValidationValidAux
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    {remainingSources : List InductiveType}
    {remainingTargets : List VInductiveType}
    {currentProdEnv targetProdEnv : Environment}
    {currentVEnv targetVEnv : VEnv}
    (Hvalidation : ConstructorValidationStateTrace
      (fun indType source target => ConstructorValidationHeaderStep loweredEnv
        (sourceTypes.map (fun type => type.name)) indType.name source target)
      remainingSources currentProdEnv targetProdEnv)
    (Htranslations : List.Forall₂
      (fun source target => TrSourceConst sourceVEnv c.lparams source.name
        source.type target.toVConstVal)
      remainingSources remainingTargets)
    (HsourceMem : ∀ source ∈ remainingSources, source ∈ sourceTypes)
    (HtargetMem : ∀ target ∈ remainingTargets,
      target ∈ loweredDecl.types)
    (Hvalid : CheckingEnv.Valid c.safety currentProdEnv currentVEnv)
    (Hle : sourceVEnv ≤ currentVEnv)
    (Hadded : currentVEnv.addConstVals
      (remainingTargets.map VInductiveType.toVConstVal) = some targetVEnv) :
    CheckingEnv.Valid c.safety targetProdEnv targetVEnv := by
  induction Htranslations generalizing currentProdEnv currentVEnv
      targetProdEnv with
  | nil =>
      cases Hvalidation
      have heq : currentVEnv = targetVEnv := by
        simpa [VEnv.addConstVals] using Option.some.inj Hadded
      exact heq ▸ Hvalid
  | @cons source target sources targets Hheader Htail ih =>
      cases Hvalidation with
      | cons HvalidationHead HvalidationTail =>
          have hsourceGlobal : source ∈ sourceTypes :=
            HsourceMem source (by simp)
          rcases List.mem_iff_getElem.mp hsourceGlobal with
            ⟨familyIdx, hfamily, heq⟩
          rcases Hlower.sourceFinalMappingAtFreshAligned hempty hfamily with
            ⟨_fvars, _mappingState, loweredTarget, _loweredState, _hparams,
              _hnodup, _hsize, Hmapping, htarget⟩
          obtain ⟨hresultFamily, htargetEq⟩ :=
            _root_.getElem?_eq_some_iff.mp htarget
          have hresultArray : familyIdx < result.types.toArray.size := by
            simpa using hresultFamily
          rcases Hprod.findSourceHeaderAt Hc familyIdx hresultArray with
            ⟨installedInfo, hinstalledLookup, hinstalledName, hinstalledType,
              _hinstalledCtors, _hinstalledAll, hinstalledLevels,
              _hinstalledParams, hinstalledUnsafe⟩
          have hinstalledLookup' : loweredEnv.find? source.name =
              some (.inductInfo installedInfo) := by
            subst source
            rw [← Hmapping.name]
            simpa [htargetEq] using hinstalledLookup
          have holdInfo : HvalidationHead.oldInfo = installedInfo :=
            ConstantInfo.inductInfo.inj
              (Option.some.inj
                (HvalidationHead.lookup.symm.trans hinstalledLookup'))
          have HheadTr : TrConstVal c.safety sourceVEnv
              (.inductInfo { HvalidationHead.oldInfo with
                all := sourceTypes.map (fun type => type.name) })
              target.toVConstVal := by
            subst source
            apply Lean4Lean.VerifyInductive.TrSourceConst.inductInfo Hheader
            · simpa [holdInfo] using hinstalledLevels
            · calc
                HvalidationHead.oldInfo.name = installedInfo.name := by
                  rw [holdInfo]
                _ = loweredTarget.name := by
                  simpa [htargetEq] using hinstalledName
                _ = sourceTypes[familyIdx].name := Hmapping.name
            · calc
                HvalidationHead.oldInfo.type = installedInfo.type := by
                  rw [holdInfo]
                _ = loweredTarget.type := by
                  simpa [htargetEq] using hinstalledType
                _ = sourceTypes[familyIdx].type := Hmapping.type
            · have holdUnsafe : HvalidationHead.oldInfo.isUnsafe =
                  isUnsafe := by
                calc
                  HvalidationHead.oldInfo.isUnsafe =
                      installedInfo.isUnsafe := by rw [holdInfo]
                  _ = isUnsafe := hinstalledUnsafe
              simpa [holdUnsafe] using hvisible
          have hname : HvalidationHead.oldInfo.name =
              target.name := by
            exact HheadTr.2
          simp only [List.map_cons, VEnv.addConstVals] at Hadded
          cases hadd : currentVEnv.addConst target.name
              target.toVConstVal.toVConstant with
          | none => simp [hadd] at Hadded
          | some nextVEnv =>
            simp only [hadd] at Hadded
            have hfresh : currentProdEnv.find?
                HvalidationHead.oldInfo.name = none :=
              find?_none_of_contains_false Hvalid.tr.map_wf
                HvalidationHead.fresh
            have HheadTr' := HheadTr.mono Hle
            have hnprim : ¬ Kernel.Environment.primitives.contains
                HvalidationHead.oldInfo.name := by
              rw [hname]
              apply Hheaders.installed.valueNonprimitive
              rw [Hheaders.values]
              simp only [VInductDecl.typeConstants]
              exact List.mem_map.mpr
                ⟨target, HtargetMem target (by simp), rfl⟩
            have HvalidNext : CheckingEnv.Valid c.safety
                (currentProdEnv.add
                  (.inductInfo { HvalidationHead.oldInfo with
                    all := sourceTypes.map (fun type => type.name) }))
                  nextVEnv :=
              Hvalid.add (ci := .inductInfo { HvalidationHead.oldInfo with
                  all := sourceTypes.map (fun type => type.name) })
                (ci' := target.toVConstVal.toVConstant) hfresh hnprim
                HheadTr'.1 (Hheader.wf.mono Hle)
                (by simpa [HheadTr'.2] using hadd) rfl
            rw [HvalidationHead.output] at HvalidationTail
            apply ih HvalidationTail
            · intro nextSource hmem
              exact HsourceMem nextSource (by simp [hmem])
            · intro nextTarget hmem
              exact HtargetMem nextTarget (by simp [hmem])
            · exact HvalidNext
            · exact Hle.trans (VEnv.addConst_le hadd)
            · exact Hadded

/-- The executable header-only side environment used by nested auxiliary
validation models exactly the abstract source-header prefix selected by the
lowering queue.  It is reconstructed directly from lowering, ordinary
production, and the actual header-installation trace; no restoration or
final-assembly certificate is involved. -/
theorem RestoredHeaderValidationEnvironment.validOfLowering
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (Hvalidation : RestoredHeaderValidationEnvironment loweredEnv c.env
      (sourceTypes.map (fun type => type.name)) sourceTypes validationEnv)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    ∃ sourceEnvTypes,
      sourceVEnv.addConstVals
          ((loweredDecl.types.take sourceTypes.length).map
            VInductiveType.toVConstVal) = some sourceEnvTypes ∧
      CheckingEnv.Valid c.safety validationEnv sourceEnvTypes := by
  rcases Hlower.sourceHeaderPrefix R.core hempty with
    ⟨sourceEnvTypes, Hadded, Htranslations⟩
  refine ⟨sourceEnvTypes, Hadded, ?_⟩
  apply restoredHeaderValidationValidAux Hlower Hc Hprod hempty hvisible
    Hvalidation.headers Htranslations
  · intro source hsource
    exact hsource
  · intro target htarget
    exact List.mem_of_mem_take htarget
  · have Hbase : CheckingEnv.Valid c.safety c.env sourceVEnv := by
      rw [← Hheaders.sourceContextVEnv]
      exact Hheaders.sourceContext.checking
    exact Hbase
  · exact VEnv.LE.rfl
  · exact Hadded

end VerifyInductive
end Lean4Lean
