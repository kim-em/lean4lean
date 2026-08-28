import Lean4Lean.Verify.Inductive.Nested.Compilation
import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterValidation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

private theorem validationHeadersValid
    {Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes traceProdEnv tracePrimaryEnv}
    (Hvalid : CheckingEnv.Valid safety currentProdEnv currentVEnv)
    (Hle : sourceVEnv ≤ currentVEnv)
    (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
      sourceVEnv envTypes envCtors Htrace owners recursors)
    (Hvalidation : ConstructorValidationStateTrace
      (fun indType source target => ConstructorValidationHeaderStep loweredEnv
        allIndNames indType.name source target)
      sourceTypes currentProdEnv targetProdEnv)
    (Htranslated : ∀ indType stepSource stepTarget (owner : VInductiveType)
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        indType stepSource stepTarget), indType ∈ sourceTypes →
      (Hheader : TrSourceConst sourceVEnv lparams indType.name indType.type
        owner.toVConstVal) →
      TrConstVal safety sourceVEnv
        (.inductInfo Hstep.restored.header.newInfo) owner.toVConstVal)
    (Hnonprimitive : ∀ owner ∈ owners,
      ¬ Kernel.Environment.primitives.contains owner.name)
    (Hadded : currentVEnv.addConstVals
      (owners.map VInductiveType.toVConstVal) = some envTypes) :
    CheckingEnv.Valid safety targetProdEnv envTypes := by
  induction Hsource generalizing targetProdEnv currentProdEnv currentVEnv with
  | nil =>
    cases Hvalidation
    simp only [List.map_nil] at Hadded
    have heq : currentVEnv = envTypes := by
      simpa [VEnv.addConstVals] using Option.some.inj Hadded
    exact heq ▸ Hvalid
  | @cons indType stepSource middleSource tailTypesSource stepTarget owner
      tailOwners tailRecursors Hstep Htail Hheader Hconstructors Hrecursor
      Hrest ih =>
    cases Hvalidation with
    | cons HvalidationHead HvalidationTail =>
      have holdInfo : HvalidationHead.oldInfo = Hstep.oldInfo := by
        have hci := Option.some.inj
          (HvalidationHead.lookup.symm.trans Hstep.lookup)
        exact ConstantInfo.inductInfo.inj hci
      have hinfo :
          { HvalidationHead.oldInfo with all := allIndNames } =
            Hstep.restored.header.newInfo := by
        rw [Hstep.restored.header.restored, holdInfo]
      have HheadTr := Htranslated indType stepSource middleSource owner Hstep
        (by simp) Hheader
      have hname : HvalidationHead.oldInfo.name =
          Hstep.restored.header.newInfo.name := by
        simpa using congrArg (fun info : InductiveVal => info.name) hinfo
      simp only [List.map_cons, VEnv.addConstVals] at Hadded
      cases hadd : currentVEnv.addConst owner.name owner.toVConstVal.toVConstant with
      | none => simp [hadd] at Hadded
      | some nextVEnv =>
        simp only [hadd] at Hadded
        have hfresh : currentProdEnv.find?
            Hstep.restored.header.newInfo.name = none :=
          find?_none_of_contains_false Hvalid.tr.map_wf
            (by simpa [hname] using HvalidationHead.fresh)
        have HheadTr' := HheadTr.mono Hle
        have hownerName : Hstep.restored.header.newInfo.name = owner.name := by
          simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using HheadTr.2
        have hnprim : ¬ Kernel.Environment.primitives.contains
            Hstep.restored.header.newInfo.name := by
          rw [hownerName]
          exact Hnonprimitive owner (by simp)
        have HvalidNext : CheckingEnv.Valid safety
            (currentProdEnv.add (.inductInfo Hstep.restored.header.newInfo))
            nextVEnv :=
          Hvalid.add (ci := .inductInfo Hstep.restored.header.newInfo)
            (ci' := owner.toVConstVal.toVConstant) hfresh
            hnprim
            HheadTr'.1 (Hheader.wf.mono Hle)
            (by simpa [HheadTr'.2] using hadd) rfl
        rw [HvalidationHead.output, hinfo] at HvalidationTail
        have HleNext : sourceVEnv ≤ nextVEnv :=
          Hle.trans (VEnv.addConst_le hadd)
        apply ih HvalidNext HleNext HvalidationTail
        · intro nextInd nextSource nextTarget nextOwner Hnext hmem HnextHeader
          exact Htranslated nextInd nextSource nextTarget nextOwner Hnext
            (by simp [hmem]) HnextHeader
        · intro nextOwner hmem
          exact Hnonprimitive nextOwner (by simp [hmem])
        · exact Hadded

private theorem validationConstructorFamilyValid
    (Hvalid : CheckingEnv.Valid safety currentProdEnv currentVEnv)
    (Hle : canonicalEnv ≤ currentVEnv)
    (Hsource : RestoredSourceConstructorTrace result loweredEnv
      lparams safety canonicalEnv names traceProdEnv traceTargetEnv
      sources constructors)
    (Hvalidation : ConstructorValidationStateTrace
      (ConstructorValidationConstructorStep result loweredEnv)
      names currentProdEnv targetProdEnv)
    (Hnonprimitive : ∀ constructor ∈ constructors,
      ¬ Kernel.Environment.primitives.contains constructor.name)
    (Hadded : currentVEnv.addConstVals constructors = some targetVEnv) :
    CheckingEnv.Valid safety targetProdEnv targetVEnv := by
  induction Hsource generalizing currentProdEnv currentVEnv targetProdEnv with
  | nil =>
    cases Hvalidation
    have heq : currentVEnv = targetVEnv := by
      simpa [VEnv.addConstVals] using Option.some.inj Hadded
    exact heq ▸ Hvalid
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
      simp only [VEnv.addConstVals] at Hadded
      cases hadd : currentVEnv.addConst Hsemantic.constructor.name
          Hsemantic.constructor.toVConstant with
      | none => simp [hadd] at Hadded
      | some nextVEnv =>
        simp only [hadd] at Hadded
        have hname : HvalidationHead.oldInfo.name =
            Hstep.restored.newInfo.name := by
          simpa using congrArg (fun info : ConstructorVal => info.name) hinfo
        have hfresh : currentProdEnv.find? Hstep.restored.newInfo.name = none :=
          find?_none_of_contains_false Hvalid.tr.map_wf
            (by simpa [hname] using HvalidationHead.fresh)
        have HheadTr := Hsemantic.restoredTranslation.mono Hle
        have hconstructorName : Hstep.restored.newInfo.name =
            Hsemantic.constructor.name := by
          simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using HheadTr.2
        have hnprim : ¬ Kernel.Environment.primitives.contains
            Hstep.restored.newInfo.name := by
          rw [hconstructorName]
          exact Hnonprimitive Hsemantic.constructor (by simp)
        have HvalidNext : CheckingEnv.Valid safety
            (currentProdEnv.add (.ctorInfo Hstep.restored.newInfo))
            nextVEnv :=
          Hvalid.add (ci := .ctorInfo Hstep.restored.newInfo)
            (ci' := Hsemantic.constructor.toVConstant) hfresh hnprim
            HheadTr.1 (Hsemantic.sourceTranslation.wf.mono Hle)
            (by
              simpa [ConstantInfo.name, ConstantInfo.toConstantVal,
                hconstructorName] using hadd) rfl
        rw [HvalidationHead.output, hinfo] at HvalidationTail
        have HleNext : canonicalEnv ≤ nextVEnv :=
          Hle.trans (VEnv.addConst_le hadd)
        apply ih HvalidNext HleNext HvalidationTail
        · intro constructor hmem
          exact Hnonprimitive constructor (by simp [hmem])
        · exact Hadded

private theorem validationConstructorsValid
    {Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes traceProdEnv tracePrimaryEnv}
    (Hvalid : CheckingEnv.Valid safety currentProdEnv currentVEnv)
    (Hle : envTypes ≤ currentVEnv)
    (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
      sourceVEnv envTypes envCtors Htrace owners recursors)
    (Hvalidation : ConstructorValidationStateTrace
      (ConstructorValidationConstructorFamilyStep result loweredEnv)
      sourceTypes currentProdEnv targetProdEnv)
    (Hnonprimitive : ∀ constructor ∈ owners.flatMap VInductiveType.ctors,
      ¬ Kernel.Environment.primitives.contains constructor.name)
    (Hadded : currentVEnv.addConstVals
      (owners.flatMap VInductiveType.ctors) = some envCtors) :
    CheckingEnv.Valid safety targetProdEnv envCtors := by
  induction Hsource generalizing currentProdEnv currentVEnv targetProdEnv with
  | nil =>
    cases Hvalidation
    simp only [List.flatMap_nil] at Hadded
    have heq : currentVEnv = envCtors := by
      simpa [VEnv.addConstVals] using Option.some.inj Hadded
    exact heq ▸ Hvalid
  | @cons indType stepSource middleSource tailTypesSource stepTarget owner
      tailOwners tailRecursors Hstep Htail Hheader Hconstructors Hrecursor
      Hrest ih =>
    cases Hvalidation with
    | cons HvalidationHead HvalidationTail =>
      have holdInfo : HvalidationHead.oldInfo = Hstep.oldInfo := by
        have hci := Option.some.inj
          (HvalidationHead.lookup.symm.trans Hstep.lookup)
        exact ConstantInfo.inductInfo.inj hci
      have HvalidationConstructors := HvalidationHead.constructors
      rw [holdInfo] at HvalidationConstructors
      simp only [List.flatMap_cons] at Hadded
      rcases VEnv.addConstVals_append_inv Hadded with
        ⟨familyVEnv, HfamilyAdded, HtailAdded⟩
      have HfamilyValid := validationConstructorFamilyValid Hvalid Hle
        Hconstructors HvalidationConstructors
        (fun constructor hmem => Hnonprimitive constructor (by simp [hmem]))
        HfamilyAdded
      have HleFamily : envTypes ≤ familyVEnv :=
        Hle.trans (VEnv.addConstVals_le HfamilyAdded)
      apply ih HfamilyValid HleFamily HvalidationTail
      · intro constructor hmem
        exact Hnonprimitive constructor (by simp [hmem])
      · exact HtailAdded

theorem AddConstants.valueNonprimitive
    (H : AddConstants safety prodEnv venv entries outProdEnv outVEnv)
    (hvalue : value ∈ entries.map Prod.snd) :
    ¬ Kernel.Environment.primitives.contains value.name := by
  induction H with
  | nil => simp at hvalue
  | cons hn hnprim htr hwf hadd hdelta Htail ih =>
    simp only [List.map_cons, List.mem_cons] at hvalue
    rcases hvalue with hhead | htail
    · subst value
      simpa [htr.2] using hnprim
    · exact ih htail

/-- The side restoration used by native constructor-parameter validation is
itself a valid checking environment for the canonical post-constructor
abstract environment.  The proof follows the retained source semantic trace
in mutual-header order and then constructor order; no environment-locality
claim is assumed. -/
theorem RestoredConstructorValidationEnvironment.valid
    {Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes traceProdEnv tracePrimaryEnv}
    (H : RestoredConstructorValidationEnvironment result loweredEnv
      sourceProdEnv allIndNames sourceTypes validationEnv)
    (Hvalid : CheckingEnv.Valid safety sourceProdEnv sourceVEnv)
    (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
      sourceVEnv envTypes envCtors Htrace owners recursors)
    (Htranslated : ∀ indType stepSource stepTarget (owner : VInductiveType)
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        indType stepSource stepTarget), indType ∈ sourceTypes →
      (Hheader : TrSourceConst sourceVEnv lparams indType.name indType.type
        owner.toVConstVal) →
      TrConstVal safety sourceVEnv
        (.inductInfo Hstep.restored.header.newInfo) owner.toVConstVal)
    (Htypes : AddConstants safety sourceProdEnv sourceVEnv typeEntries
      canonicalTypesProdEnv envTypes)
    (htypeValues : typeEntries.map Prod.snd =
      owners.map VInductiveType.toVConstVal)
    (Hconstructors : AddConstants safety canonicalTypesProdEnv envTypes
      constructorEntries canonicalCtorsProdEnv envCtors)
    (hconstructorValues : constructorEntries.map Prod.snd =
      owners.flatMap VInductiveType.ctors) :
    CheckingEnv.Valid safety validationEnv envCtors := by
  have HheadersValid := validationHeadersValid Hvalid VEnv.LE.rfl Hsource
    H.headers Htranslated (fun owner howner => by
      apply Htypes.valueNonprimitive
      rw [htypeValues]
      exact List.mem_map.mpr ⟨owner, howner, rfl⟩) (by
        rw [← htypeValues]
        exact Htypes.abstract)
  exact validationConstructorsValid HheadersValid VEnv.LE.rfl Hsource
    H.constructors (fun constructor hconstructor => by
      apply Hconstructors.valueNonprimitive
      rw [hconstructorValues]
      exact hconstructor) (by
        rw [← hconstructorValues]
        exact Hconstructors.abstract)

end VerifyInductive
end Lean4Lean
