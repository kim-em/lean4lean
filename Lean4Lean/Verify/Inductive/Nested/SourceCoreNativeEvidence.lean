import Lean4Lean.Verify.Inductive.Nested.HeaderNativeEvidence
import Lean4Lean.Verify.Inductive.Nested.EndToEnd

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-! # Native source-core reconstruction for nested declarations -/

/-- Two retained executions of the deterministic source-header restoration
fold have the same endpoint. -/
theorem ConstructorValidationStateTrace.headerTarget_eq
    (Hleft : ConstructorValidationStateTrace
      (fun indType : InductiveType => fun source target =>
        ConstructorValidationHeaderStep loweredEnv
        allIndNames indType.name source target)
      types sourceEnv leftTarget)
    (Hright : ConstructorValidationStateTrace
      (fun indType : InductiveType => fun source target =>
        ConstructorValidationHeaderStep loweredEnv
        allIndNames indType.name source target)
      types sourceEnv rightTarget) :
    leftTarget = rightTarget := by
  induction Hleft generalizing rightTarget with
  | nil =>
    cases Hright
    rfl
  | @cons head tail sourceEnv middleEnv leftTarget Hhead Htail ih =>
    cases Hright with
    | @cons _ _ _ rightMiddle rightTarget HrightHead HrightTail =>
      have holdInfo : HrightHead.oldInfo = Hhead.oldInfo := by
        have hci := Option.some.inj
          (HrightHead.lookup.symm.trans Hhead.lookup)
        exact ConstantInfo.inductInfo.inj hci
      rw [HrightHead.output, holdInfo, ← Hhead.output] at HrightTail
      exact ih HrightTail

private theorem installRestoredSourceConstructors
    (Hvalid : CheckingEnv.Valid safety currentProdEnv currentVEnv)
    (Hle : canonicalEnv ≤ currentVEnv)
    (Hsource : RestoredSourceConstructorTrace result loweredEnv lparams safety
      canonicalEnv names traceProdEnv traceTargetEnv sources constructors)
    (Hvalidation : ConstructorValidationStateTrace
      (ConstructorValidationConstructorStep result loweredEnv false)
      names currentProdEnv targetProdEnv) :
    ∃ targetVEnv,
      currentVEnv.addConstVals constructors = some targetVEnv ∧
      CheckingEnv.Valid safety targetProdEnv targetVEnv := by
  induction Hsource generalizing currentProdEnv currentVEnv targetProdEnv with
  | nil =>
    cases Hvalidation
    exact ⟨currentVEnv, by simp [VEnv.addConstVals], Hvalid⟩
  | cons Hstep Hsemantic Hrest ih =>
    cases Hvalidation with
    | cons HvalidationHead HvalidationTail =>
      have holdInfo : HvalidationHead.oldInfo = Hstep.oldInfo := by
        have hci := Option.some.inj
          (HvalidationHead.lookup.symm.trans Hstep.lookup)
        exact ConstantInfo.ctorInfo.inj hci
      have hinfo :
          { HvalidationHead.oldInfo with type :=
              (result.restoreNested loweredEnv
                HvalidationHead.oldInfo.type) } =
            Hstep.restored.newInfo := by
        rw [Hstep.restored.newInfo_eq, holdInfo]
      have hname : HvalidationHead.oldInfo.name =
          Hstep.restored.newInfo.name := by
        simpa using congrArg (fun info : ConstructorVal => info.name) hinfo
      have hconstructorName : Hstep.restored.newInfo.name =
          Hsemantic.constructor.name := by
        simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using
          Hsemantic.restoredTranslation.2
      have hfreshRestored : currentProdEnv.find?
          Hstep.restored.newInfo.name = none :=
        find?_none_of_contains_false Hvalid.tr.map_wf
          (by simpa [hname] using HvalidationHead.fresh)
      have hfreshProd : currentProdEnv.find?
          Hsemantic.constructor.name = none := by
        simpa [← hconstructorName] using hfreshRestored
      have habstractFresh :
          currentVEnv.constants Hsemantic.constructor.name = none := by
        cases hfind : currentVEnv.constants Hsemantic.constructor.name with
        | none => rfl
        | some value =>
          rcases Hvalid.tr.find?_iff.mpr ⟨value, hfind⟩ with
            ⟨info, hinfoFind, _hvisible⟩
          rw [hfreshProd] at hinfoFind
          contradiction
      rcases VEnv.addConst_eq_none
          (ci := Hsemantic.constructor.toVConstant) habstractFresh with
        ⟨nextVEnv, hadd⟩
      have HheadTr := Hsemantic.restoredTranslation.mono Hle
      have hnprim : ¬ Kernel.Environment.primitives.contains
          Hstep.restored.newInfo.name := by
        simpa [← hname] using HvalidationHead.notPrimitive rfl
      have HvalidNext : CheckingEnv.Valid safety
          (currentProdEnv.add (.ctorInfo Hstep.restored.newInfo)) nextVEnv :=
        Hvalid.add (ci := .ctorInfo Hstep.restored.newInfo)
          (ci' := Hsemantic.constructor.toVConstant)
          hfreshRestored hnprim
          HheadTr.1 (Hsemantic.sourceTranslation.wf.mono Hle)
          (by simpa [ConstantInfo.name, ConstantInfo.toConstantVal,
            hconstructorName] using hadd) rfl
      rw [HvalidationHead.output, hinfo] at HvalidationTail
      rcases ih HvalidNext (Hle.trans (VEnv.addConst_le hadd))
          HvalidationTail with ⟨targetVEnv, Hadded, HtargetValid⟩
      exact ⟨targetVEnv, by
        simp [VEnv.addConstVals, hadd, Hadded], HtargetValid⟩

private theorem installRestoredSourceFamilies
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv sourceTypesVEnv : VEnv}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Howners : ConstructorOwnersPresent c.env)
    (HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst sourceVEnv c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (loweredDecl.types.take sourceTypes.length))
    (HsourceAdded : sourceVEnv.addConstVals
      ((loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some sourceTypesVEnv)
    (HvalidationValid : CheckingEnv.Valid c.safety auxiliaryHeaderEnv
      sourceTypesVEnv)
    (HparameterRun :
      Lean4Lean.validateRestoredConstructorParameters.run auxiliaryHeaderEnv
        c.lparams c.safety validationFuel sourceTypes result = .ok ())
    (hempty : initialState.nestedAux = #[])
    (Hrestoration : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      remainingSources restorationSource restorationTarget)
    (Hvalidation : ConstructorValidationStateTrace
      (ConstructorValidationConstructorFamilyStep result loweredEnv false)
      remainingSources currentProdEnv targetProdEnv)
    (HremainingHeaders : List.Forall₂
      (fun source target => TrSourceConst sourceVEnv c.lparams source.name
        source.type target.toVConstVal)
      remainingSources remainingTargets)
    (HsourceMem : ∀ source ∈ remainingSources, source ∈ sourceTypes)
    (Hvalid : CheckingEnv.Valid c.safety currentProdEnv currentVEnv)
    (Hle : sourceTypesVEnv ≤ currentVEnv) :
    ∃ owners targetVEnv,
      owners.map VInductiveTypeSkeleton.toVConstVal =
        remainingTargets.map VInductiveType.toVConstVal ∧
      currentVEnv.addConstVals
        (owners.flatMap VInductiveTypeSkeleton.ctors) = some targetVEnv ∧
      CheckingEnv.Valid c.safety targetProdEnv targetVEnv ∧
      List.Forall₂
        (TrInductiveTypeSkeleton sourceVEnv sourceTypesVEnv c.lparams)
        remainingSources owners := by
  induction Hrestoration generalizing currentProdEnv currentVEnv
      targetProdEnv remainingTargets with
  | nil =>
      cases Hvalidation
      cases HremainingHeaders
      exact ⟨[], currentVEnv, rfl, by simp [VEnv.addConstVals], Hvalid,
        .nil⟩
  | cons Hstep HrestorationTail ih =>
      cases Hvalidation with
      | cons HvalidationHead HvalidationTail =>
        cases HremainingHeaders with
        | @cons source target sources targets Hheader HheadersTail =>
          have hsourceGlobal : _ ∈ sourceTypes :=
            HsourceMem _ List.mem_cons_self
          rcases List.mem_iff_getElem.mp hsourceGlobal with
            ⟨familyIdx, hfamily, hsourceEq⟩
          cases hsourceEq
          rcases Hlower.sourceConstructorSemanticsAtFreshOfValidation Hc
              Hprod Hsources Howners HsourceHeaders HsourceAdded
              HvalidationValid HparameterRun hempty familyIdx hfamily
              Hstep with ⟨constructors, Hconstructors⟩
          have holdInfo : HvalidationHead.oldInfo = Hstep.oldInfo := by
            have hci := Option.some.inj
              (HvalidationHead.lookup.symm.trans Hstep.lookup)
            exact ConstantInfo.inductInfo.inj hci
          have HvalidationConstructors := HvalidationHead.constructors
          rw [holdInfo] at HvalidationConstructors
          rcases installRestoredSourceConstructors Hvalid Hle Hconstructors
              HvalidationConstructors with
            ⟨middleVEnv, HconstructorsAdded, HmiddleValid⟩
          rcases ih HvalidationTail HheadersTail (fun source hsource =>
              HsourceMem source (by simp [hsource])) HmiddleValid
              (Hle.trans (VEnv.addConstVals_le HconstructorsAdded)) with
            ⟨owners, targetVEnv, HownerHeaders, HrestAdded, HtargetValid,
              Htypes⟩
          let owner' : VInductiveTypeSkeleton := {
            toVConstVal := target.toVConstVal
            ctors := constructors }
          have Howner : TrInductiveTypeSkeleton sourceVEnv sourceTypesVEnv
              c.lparams sourceTypes[familyIdx] owner' := by
            exact ⟨Hheader, Hconstructors.forall₂⟩
          refine ⟨owner' :: owners, targetVEnv, ?_, ?_, HtargetValid,
            .cons Howner Htypes⟩
          · simp [owner', HownerHeaders]
          · simpa [owner', VEnv.addConstVals_append] using
              VEnv.addConstVals_append HconstructorsAdded HrestAdded

/-- Source declaration and canonical header/constructor stages synthesized
from the exact lowering, restoration, and validation executions. -/
structure NativeNestedSourceCoreResult
    (sourceVEnv : VEnv) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (loweredDecl : VInductDecl) (safety : DefinitionSafety)
    (validationEnv auxiliaryHeaderEnv : Environment) where
  sourceDecl : VInductDecl
  envTypes : VEnv
  envCtors : VEnv
  sourceHeaders : List.Forall₂
    (fun source target => TrSourceConst sourceVEnv lparams source.name
      source.type target.toVConstVal)
    sourceTypes (loweredDecl.types.take sourceTypes.length)
  sourceAdded : sourceVEnv.addConstVals
    ((loweredDecl.types.take sourceTypes.length).map
      VInductiveType.toVConstVal) = some envTypes
  sourceTypeValues : sourceDecl.typeConstants =
    (loweredDecl.types.take sourceTypes.length).map
      VInductiveType.toVConstVal
  core : TrInductDeclCore sourceVEnv lparams nparams sourceTypes isUnsafe
    sourceDecl envTypes envCtors
  materialized : MaterializedInductivePrefix sourceDecl loweredDecl
  headerValidationValid : CheckingEnv.Valid safety auxiliaryHeaderEnv envTypes
  validationValid : CheckingEnv.Valid safety validationEnv envCtors

/-- Reconstruct the complete ordinary source core used by nested verification
from the actual producer and side-validation traces.  In particular, neither
the declaration nor its constructor translations are supplied by a caller. -/
theorem NestedLoweringResultClosed.nativeSourceCore
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
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (Hrestoration : RestoredNestedDeclarationsResult result loweredEnv c.env
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) sourceTypes
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 ((), outEnv))
    (HconstructorValidation : RestoredConstructorValidationEnvironment result
      loweredEnv c.env (sourceTypes.map (·.name)) false sourceTypes
      constructorValidationEnv)
    (HheaderValidation : RestoredHeaderValidationEnvironment loweredEnv c.env
      (sourceTypes.map (·.name)) sourceTypes auxiliaryHeaderEnv)
    (HparameterRun :
      Lean4Lean.validateRestoredConstructorParameters.run auxiliaryHeaderEnv
        c.lparams c.safety validationFuel sourceTypes result = .ok ())
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    Nonempty (NativeNestedSourceCoreResult sourceVEnv c.lparams nparams
      sourceTypes isUnsafe loweredDecl c.safety constructorValidationEnv
        auxiliaryHeaderEnv) := by
  rcases Hlower.sourceHeaderPrefix R.core hempty with
    ⟨sourceTypesVEnv, HsourceAdded, HsourceHeaders⟩
  rcases HheaderValidation.validOfLowering Hlower Hc Hprod hempty
      hvisible with
    ⟨headerVEnv, HheaderAdded, HheaderValid⟩
  have hheaderVEnv : headerVEnv = sourceTypesVEnv := by
    exact Option.some.inj (HheaderAdded.symm.trans HsourceAdded)
  subst headerVEnv
  have hheaderProdEnv : HconstructorValidation.headerEnv = auxiliaryHeaderEnv :=
    HconstructorValidation.headers.headerTarget_eq HheaderValidation.headers
  have HconstructorTrace := HconstructorValidation.constructors
  rw [hheaderProdEnv] at HconstructorTrace
  rcases installRestoredSourceFamilies Hlower Hc Hprod Hsources Howners
      HsourceHeaders HsourceAdded HheaderValid HparameterRun hempty
      Hrestoration.inductives HconstructorTrace
      HsourceHeaders (fun source hsource => hsource) HheaderValid
      VEnv.LE.rfl with
    ⟨owners, envCtors, HownerHeaders, HconstructorsAdded,
      HvalidationValid, Htypes⟩
  let skeleton : VInductDeclSkeleton := {
    uvars := c.lparams.length
    nparams := nparams
    types := owners
    isUnsafe := isUnsafe }
  have HtypesAdded : sourceVEnv.addConstVals skeleton.typeConstants =
      some sourceTypesVEnv := by
    change sourceVEnv.addConstVals
      (owners.map VInductiveTypeSkeleton.toVConstVal) = some sourceTypesVEnv
    rw [HownerHeaders]
    exact HsourceAdded
  have Hcore : TrInductDeclSkeletonCore sourceVEnv c.lparams nparams
      sourceTypes isUnsafe skeleton sourceTypesVEnv envCtors := {
    uvars := rfl
    nparams := rfl
    isUnsafe := rfl
    typesAdded := HtypesAdded
    ctorsAdded := by
      simpa [skeleton, VInductDeclSkeleton.constructorConstants] using
        HconstructorsAdded
    types := Htypes }
  have hsourceLength : skeleton.types.length ≤ loweredDecl.types.length := by
    have hownersLength : owners.length = sourceTypes.length :=
      (Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Htypes).symm
    rw [show skeleton.types.length = owners.length by rfl, hownersLength]
    calc
      sourceTypes.length ≤ result.types.length :=
        Hlower.toResult.sourceTypes_length_le
      _ = loweredDecl.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
  rcases VInductDeclSkeleton.materializeExpandedPrefix skeleton loweredDecl
      hsourceLength with ⟨sourceDecl, Hmaterialize, Hmaterialized⟩
  have HsourceCore :=
    Lean4Lean.VerifyInductive.TrInductDeclSkeletonCore.materialized Hcore
      Hmaterialize
  have hsourceTypeValues : sourceDecl.typeConstants =
      (loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal := by
    calc
      sourceDecl.typeConstants = skeleton.typeConstants := by
        rw [← VInductDecl.toSkeleton_typeConstants sourceDecl,
          VInductDeclSkeleton.materialize_toSkeleton Hmaterialize]
      _ = owners.map VInductiveTypeSkeleton.toVConstVal := rfl
      _ = _ := HownerHeaders
  exact ⟨{
    sourceDecl := sourceDecl
    envTypes := sourceTypesVEnv
    envCtors := envCtors
    sourceHeaders := HsourceHeaders
    sourceAdded := HsourceAdded
    sourceTypeValues := hsourceTypeValues
    core := HsourceCore
    materialized := Hmaterialized
    headerValidationValid := HheaderValid
    validationValid := HvalidationValid }⟩

end VerifyInductive
end Lean4Lean
