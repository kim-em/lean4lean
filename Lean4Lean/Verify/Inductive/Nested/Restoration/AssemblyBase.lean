import Lean4Lean.Verify.Inductive.Nested.Restoration.Base
import Lean4Lean.Verify.Inductive.Nested.Restoration.RunOfRestoration
import Lean4Lean.Verify.Inductive.Nested.Restoration.SideEnvironment.ConstructorEnvironment
import Lean4Lean.Verify.Inductive.Nested.Lowering.Expansion.Data

/-! # The rule-free restored block of a nested run

`NestedRun.assemblyBase` builds the `RestoredBlockBase` of a nested run: the target version of
the source branch's `existsValidatedExactRestoration`, `RestoredBlockBase.ofReplay`,
`assemblyBaseOfFormation` and `assemblyBaseValid` (`Install/FromRun.lean`). The restored
constants are replayed in dependency order (`RestorationInDependencyOrder`) and installed in
the abstract stages `BlockStages` (the source's `BlockInstallation` without its concrete side
and case eliminators). The restored recursor types are translated by the recursor-type
validation pass in the constructor side environment, a checker environment of the projection
stage (`ValidationEnvironment.validProjected`, `CheckerEnv.ofSideExtension`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-! ### The recursor-type validation pass, per recursor -/

/-- The recursor-type pass translates the restored type of a source recursor to a type. -/
theorem validateRestoredRecursorTypes.translation_of_run
    {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    (C : CheckerEnv safety env venv) {loweredEnv : Environment} {fuel : FuelConfig}
    {result : ElimNestedInductive.Result} {recNameMap : NameMap Name} {allIndNames : List Name}
    {types : List InductiveType} {auxRecNames : List Name} {indType : InductiveType}
    {oldInfo : RecursorVal}
    (hrun : Lean4Lean.validateRestoredRecursorTypes.run env loweredEnv
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (htype : indType ∈ types)
    (hlookup : loweredEnv.find? (Lean.mkRecName indType.name) =
      some (.recInfo oldInfo)) :
    let newRecName := recNameMap.getD (Lean.mkRecName indType.name)
      (Lean.mkRecName indType.name)
    let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
      (Lean.mkRecName indType.name) newRecName oldInfo
    ∃ target, TrExprS venv restored.levelParams [] restored.type target ∧
      venv.IsType restored.levelParams.length [] target := by
  have hcheck := validateRestoredRecursorTypes.run.WF C loweredEnv fuel result recNameMap
    allIndNames types auxRecNames hrun (Lean.mkRecName indType.name)
    (List.mem_append_left _ (List.mem_map.mpr ⟨indType, htype, rfl⟩))
  obtain ⟨recInfo, hfind, T, hT, hty⟩ := validateRestoredRecursorTypes.check.WF C loweredEnv
    fuel result recNameMap allIndNames _ hcheck
  cases ConstantInfo.recInfo.inj (Option.some.inj (hfind.symm.trans hlookup))
  exact ⟨T, hT, hty⟩

/-- The recursor-type pass translates the restored type of an auxiliary recursor to a type. -/
theorem validateRestoredRecursorTypes.auxiliaryTranslation_of_run
    {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    (C : CheckerEnv safety env venv) {loweredEnv : Environment} {fuel : FuelConfig}
    {result : ElimNestedInductive.Result} {recNameMap : NameMap Name} {allIndNames : List Name}
    {types : List InductiveType} {auxRecNames : List Name} {recName : Name}
    {oldInfo : RecursorVal}
    (hrun : Lean4Lean.validateRestoredRecursorTypes.run env loweredEnv
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (hrec : recName ∈ auxRecNames)
    (hlookup : loweredEnv.find? recName = some (.recInfo oldInfo)) :
    let newRecName := recNameMap.getD recName recName
    let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
      recName newRecName oldInfo
    ∃ target, TrExprS venv restored.levelParams [] restored.type target ∧
      venv.IsType restored.levelParams.length [] target := by
  have hcheck := validateRestoredRecursorTypes.run.WF C loweredEnv fuel result recNameMap
    allIndNames types auxRecNames hrun recName (List.mem_append_right _ hrec)
  obtain ⟨recInfo, hfind, T, hT, hty⟩ := validateRestoredRecursorTypes.check.WF C loweredEnv
    fuel result recNameMap allIndNames _ hcheck
  cases ConstantInfo.recInfo.inj (Option.some.inj (hfind.symm.trans hlookup))
  exact ⟨T, hT, hty⟩

/-- Telescope-translation form of the pointwise source recursor translation (the source
branch's `restoredSourceTelescopeAtFreshOfValidation`). -/
theorem NestedLoweringOutputClosed.restoredSourceTelescopeAtFreshOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envCtors : VEnv} {ctorEnv loweredEnv validationEnv : Environment}
    {result : ElimNestedInductive.Result} {sourceTypes : List InductiveType}
    {loweredSourceEnv : Environment} {fuel : Nat} {auxRecNames : List Name}
    {validationSafety : DefinitionSafety} {validationFuel : FuelConfig}
    {R : RecursorInput c stats loweredDecl nparams isUnsafe depth sourceVEnv
      result.types.toArray ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorInstallation R loweredEnv)
    (Hvalid : CheckerEnv validationSafety validationEnv envCtors)
    (Hrun : Lean4Lean.validateRestoredRecursorTypes.run validationEnv
      loweredEnv validationSafety validationFuel result
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) sourceTypes auxRecNames = .ok ())
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hentry : familyIdx < Hprod.entries.length)
    {stepSource stepTarget : Environment}
    (Hstep : RestoredInductiveStep result loweredEnv
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) sourceTypes[familyIdx]
        stepSource stepTarget) :
    ∃ targetType, Expr.ForallTelescopeTypeTranslation envCtors
      Hstep.restored.recursor.oldInfo.levelParams []
      Hstep.restored.recursor.restored.newInfo.type
      (result.nparams + (Hprod.recInfos.map (·.motive)).size +
        (Hprod.recInfos.flatMap (·.minors)).size +
        Hprod.recInfos[familyIdx]!.indices.size + 1)
      targetType := by
  have holdRecName : Lean.mkRecName sourceTypes[familyIdx].name =
      Lean.mkRecName result.types.toArray[familyIdx]!.name := by
    rcases H.sourceResolvedMappingAtFreshAligned hempty hfamily with
      ⟨_fvars, _stepState, mappedTarget, _loweredState, _hparams, _hnodup,
        _hsize, Hmapping, hmappedTarget⟩
    obtain ⟨hresult, hmappedEq⟩ := _root_.getElem?_eq_some_iff.mp hmappedTarget
    have harray : result.types.toArray[familyIdx]! = mappedTarget := by
      simp [hresult, hmappedEq]
    rw [harray, Hmapping.name]
  rcases Hprod.restoredSourceTelescopeAlignment familyIdx hentry
      Hstep.restored.recursor holdRecName H.toResult.resultNParams H.resultParamsSize with
    ⟨Hrecursor⟩
  have Htel := Hrecursor.restoredForallTelescope
  rcases validateRestoredRecursorTypes.translation_of_run Hvalid Hrun
      (List.getElem_mem hfamily)
      Hstep.restored.recursor.lookup with ⟨targetType, Htr, Htype⟩
  rw [← Hstep.restored.recursor.restored.produced] at Htr Htype
  rw [Hstep.restored.recursor.restored.restoration.levelParams] at Htr Htype
  exact ⟨targetType, by
    simpa only [Nat.add_assoc] using
      Expr.ForallTelescopeTypeTranslation.ofTrExprS Htel Htr Htype⟩

/-- The recursor-type pass translates the auxiliary recursor of one restoration step (the
source branch's `AuxiliaryRecursorGeneratedAlignment.recursorStepOfValidation`). -/
theorem AuxiliaryRecursorGeneratedAlignment.recursorStepOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envCtors : VEnv} {indTypes : Array InductiveType}
    {ctorEnv loweredEnv validationEnv stepSource stepTarget : Environment}
    {result : ElimNestedInductive.Result} {auxRec : NameMap Name} {allIndNames : List Name}
    {oldRecName : Name} {validationFuel : FuelConfig} {validationTypes : List InductiveType}
    {auxRecNames : List Name}
    {R : RecursorInput c stats loweredDecl nparams isUnsafe depth sourceVEnv indTypes ctorEnv}
    {Hprod : RecursorInstallation R loweredEnv}
    {Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName stepSource stepTarget}
    (A : AuxiliaryRecursorGeneratedAlignment Hprod Hstep)
    (Hvalid : CheckerEnv c.safety validationEnv envCtors)
    (Hrun : Lean4Lean.validateRestoredRecursorTypes.run validationEnv
      loweredEnv c.safety validationFuel result auxRec
      allIndNames validationTypes auxRecNames = .ok ())
    (hrec : oldRecName ∈ auxRecNames) :
    Nonempty (AuxiliaryRecursorTranslation c.safety envCtors envCtors Hstep) := by
  rcases validateRestoredRecursorTypes.auxiliaryTranslation_of_run Hvalid Hrun
      hrec Hstep.lookup with ⟨targetType, Htranslation, Htype⟩
  rw [← Hstep.restored.produced] at Htranslation Htype
  have Hmetadata := Hprod.restoredSourceRecursorMetadata A.ownerIdx
    A.entry_lt Hstep A.oldRecName_eq
  have Hsafety : c.safety ≤
      (ConstantInfo.recInfo Hstep.restored.newInfo).safety := by
    simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
      ConstantInfo.isPartial, Hstep.restored.restoration.isUnsafe] using
        Hmetadata.1
  exact ⟨AuxiliaryRecursorTranslation.ofTypeTranslation targetType Hsafety
    Htranslation Htype⟩

/-- Fold the recursor-type validation over the auxiliary restoration fold (the source
branch's `AuxiliaryRecursorGeneratedAlignments.recursorTraceOfValidation`). -/
theorem AuxiliaryRecursorGeneratedAlignments.recursorTraceOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envCtors : VEnv} {indTypes : Array InductiveType}
    {ctorEnv loweredEnv validationEnv sourceProdEnv targetProdEnv : Environment}
    {result : ElimNestedInductive.Result} {auxRec : NameMap Name} {allIndNames : List Name}
    {names : List Name} {validationFuel : FuelConfig} {validationTypes : List InductiveType}
    {auxRecNames : List Name}
    {R : RecursorInput c stats loweredDecl nparams isUnsafe depth sourceVEnv indTypes ctorEnv}
    {Hprod : RecursorInstallation R loweredEnv}
    {Htrace : FoldSteps
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceProdEnv targetProdEnv}
    (H : AuxiliaryRecursorGeneratedAlignments Hprod Htrace)
    (Hvalid : CheckerEnv c.safety validationEnv envCtors)
    (Hrun : Lean4Lean.validateRestoredRecursorTypes.run validationEnv
      loweredEnv c.safety validationFuel result auxRec
      allIndNames validationTypes auxRecNames = .ok ())
    (Hnames : ∀ name ∈ names, name ∈ auxRecNames)
    (priorRecursors : List VConstVal) :
    ∃ finalRecursors, AuxiliaryRecursorTranslations c.safety envCtors
      envCtors Htrace priorRecursors finalRecursors := by
  induction H generalizing priorRecursors with
  | nil sourceEnv => exact ⟨priorRecursors, .nil sourceEnv priorRecursors⟩
  | @cons oldRecName stepSource middleEnv tail targetEnv Hstep Htail A Hrest ih =>
      rcases A.recursorStepOfValidation Hvalid Hrun
          (Hnames oldRecName (by simp)) with ⟨Hhead⟩
      have HtailNames : ∀ name ∈ tail, name ∈ auxRecNames := by
        intro name hname
        exact Hnames name (by simp [hname])
      rcases ih HtailNames (priorRecursors ++ [Hhead.recursor]) with
        ⟨finalRecursors, Hfinal⟩
      exact ⟨finalRecursors,
        AuxiliaryRecursorTranslations.cons Hstep Htail Hhead Hfinal⟩

/-- The abstract stages of a dependency-order replay (the source branch's
`RestorationInDependencyOrder.existsBlockInstallation` without its concrete installation and
case eliminators): the headers and constructors are the declaration's, and the recursors are
added to the projection stage. -/
theorem RestorationInDependencyOrder.existsBlockStages
    {safety : DefinitionSafety} {sourceProdEnv outProdEnv : Environment}
    {sourceVEnv envTypes envCtors : VEnv} {owners : List VInductiveType}
    {primaryRecursors auxiliaryRecursors : List VConstVal}
    {primitiveEntries nondeltaEntries : List ConstantInfo}
    (projections : List VProjectionEntry)
    (H : RestorationInDependencyOrder safety sourceProdEnv outProdEnv
      sourceVEnv envTypes (envCtors.addProjections projections) owners
        primaryRecursors auxiliaryRecursors)
    (Hchecking : CheckingEnv safety sourceProdEnv sourceVEnv)
    (HprojectedWF : (envCtors.addProjections projections).WF)
    (Hprimitive : FreshNonprimitiveExtension false sourceProdEnv
      primitiveEntries outProdEnv)
    (Hnondelta : FreshExtension sourceProdEnv nondeltaEntries outProdEnv)
    (hnondelta : ∀ entry ∈ nondeltaEntries, entry.deltaValue? = none)
    (htypesAbstract : sourceVEnv.addConstVals
      (H.typeEntries.map Prod.snd) = some envTypes)
    (hconstructorsAbstract : envTypes.addConstVals
      (H.constructorEntries.map Prod.snd) = some envCtors) :
    ∃ recursorVEnv, ∃ S : BlockStages sourceVEnv H.typeEntries H.constructorEntries
      H.recursorEntries projections recursorVEnv,
      S.venvTypes = envTypes ∧ S.venvCtors = envCtors := by
  rcases H.existsCanonicalFresh Hchecking.map_wf with
    ⟨canonicalProdEnv, HcanonicalFresh, -⟩
  have HcanonicalFresh' : FreshExtension sourceProdEnv
      (H.typeEntries.map Prod.fst ++ (H.constructorEntries.map Prod.fst ++
        H.recursorEntries.map Prod.fst)) canonicalProdEnv := by
    simpa [List.map_append, List.append_assoc] using HcanonicalFresh
  rcases HcanonicalFresh'.split_append with
    ⟨prodTypes, HtypesFresh, HafterTypes⟩
  rcases HafterTypes.split_append with
    ⟨prodCtors, HconstructorsFresh, HrecursorsFresh⟩
  have hnonprimitive := H.canonicalNonprimitive Hprimitive Hchecking.map_wf
  have hnondeltaCanonical := H.canonicalNondelta Hnondelta
    Hchecking.map_wf hnondelta
  have HtypesAdded : AddConstants safety sourceProdEnv sourceVEnv
      H.typeEntries prodTypes envTypes := by
    apply AddConstants.ofFreshAbstract HtypesFresh
      (fun entry hentry => (H.types entry hentry).1)
      (fun entry hentry => (H.types entry hentry).2)
    · intro entry hentry
      exact hnonprimitive entry (by simp [hentry])
    · intro entry hentry
      exact hnondeltaCanonical entry (by simp [hentry])
    · exact htypesAbstract
    · exact VEnv.LE.rfl
  have HcheckingTypes : CheckingEnv safety prodTypes envTypes :=
    HtypesAdded.checking Hchecking
  have HconstructorsAdded : AddConstants safety prodTypes envTypes
      H.constructorEntries prodCtors envCtors := by
    apply AddConstants.ofFreshAbstract HconstructorsFresh
      (fun entry hentry => (H.constructors entry hentry).1)
      (fun entry hentry => (H.constructors entry hentry).2)
    · intro entry hentry
      exact hnonprimitive entry (by simp [hentry])
    · intro entry hentry
      exact hnondeltaCanonical entry (by simp [hentry])
    · exact hconstructorsAbstract
    · exact VEnv.LE.rfl
  have HcheckingProjected : CheckingEnv safety prodCtors
      (envCtors.addProjections projections) :=
    (HconstructorsAdded.checking HcheckingTypes).addProjections HprojectedWF
  rcases AddConstants.exists_ofFresh HrecursorsFresh
      (fun entry hentry => (H.recursors entry hentry).1)
      (fun entry hentry => (H.recursors entry hentry).2)
      (fun entry hentry => hnonprimitive entry (by simp [hentry]))
      (fun entry hentry => hnondeltaCanonical entry (by simp [hentry]))
      HcheckingProjected VEnv.LE.rfl with ⟨recursorVEnv, HrecursorsAdded⟩
  exact ⟨recursorVEnv, {
    venvTypes := envTypes
    venvCtors := envCtors
    abstract_types := htypesAbstract
    abstract_ctors := hconstructorsAbstract
    recursorsAdded := {
      abstract := HrecursorsAdded.abstract
      name_eq := fun entry hentry => (H.recursors entry hentry).1.2 } }, rfl, rfl⟩

end VerifyInductive
end Lean4Lean
