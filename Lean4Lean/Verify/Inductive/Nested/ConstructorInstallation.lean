import Lean4Lean.Verify.Inductive.Nested.Restoration

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

structure RestoredConstructorInstallationSemantics
    (safety : DefinitionSafety)
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (sourceVEnv targetVEnv : VEnv) where
  constructor : VConstVal
  translated : TrConstVal safety sourceVEnv
    (.ctorInfo Hstep.restored.newInfo) constructor
  wf : constructor.toVConstant.WF sourceVEnv
  installed : sourceVEnv.addConst constructor.name constructor.toVConstant =
    some targetVEnv

theorem RestoredConstructorInstallationSemantics.checking
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv targetProdEnv : Environment}
    {ctorName : Name}
    {Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv}
    {sourceVEnv targetVEnv : VEnv}
    (H : RestoredConstructorInstallationSemantics safety Hstep sourceVEnv
      targetVEnv)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv) :
    CheckingEnv safety targetProdEnv targetVEnv := by
  have hprodFresh : sourceProdEnv.find?
      Hstep.restored.newInfo.name = none :=
    find?_none_of_contains_false Hvalid.map_wf Hstep.restored.fresh
  have Hadd : sourceVEnv.addConst Hstep.restored.newInfo.name
      H.constructor.toVConstant = some targetVEnv := by
    have hname : Hstep.restored.newInfo.name = H.constructor.name := by
      simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using
        H.translated.2
    rw [hname]
    exact H.installed
  have Hnext := CheckingEnv.add
    (ci := .ctorInfo Hstep.restored.newInfo)
    (ci' := H.constructor.toVConstant) Hvalid hprodFresh H.translated.1
    H.wf Hadd rfl
  have htarget : targetProdEnv = sourceProdEnv.add
      (.ctorInfo Hstep.restored.newInfo) :=
    congrArg Prod.snd Hstep.restored.output
  rwa [htarget]

/-- Build the installation payload for a restored constructor.  All metadata
and freshness facts are derived; the only restoration-specific semantic
premise is translation of the restored concrete type to the original
abstract constructor type. -/
theorem RestoredConstructorStep.installationOfMetadata
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (constructor : VConstVal)
    (Hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
    (Huvars : Hstep.oldInfo.levelParams.length = constructor.uvars)
    (Hname : Hstep.oldInfo.name = constructor.name)
    (Htype : TrExprS sourceVEnv Hstep.oldInfo.levelParams []
      Hstep.restored.newInfo.type constructor.type)
    (Hwf : constructor.toVConstant.WF sourceVEnv) :
    ∃ targetVEnv,
      Nonempty (RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  have hprodFresh : sourceProdEnv.find?
      Hstep.restored.newInfo.name = none :=
    find?_none_of_contains_false Hvalid.map_wf Hstep.restored.fresh
  have Htranslated := Hstep.restored.restoration.translatedOfMetadata
    Hsafety Huvars Hname Htype
  rcases CheckingEnv.exists_addConst Hvalid hprodFresh
      constructor.toVConstant with ⟨targetVEnv, Hinstalled⟩
  have Hinstalled' : sourceVEnv.addConst constructor.name
      constructor.toVConstant = some targetVEnv := by
    rw [← Htranslated.2]
    exact Hinstalled
  exact ⟨targetVEnv, ⟨{
    constructor := constructor
    translated := Htranslated
    wf := Hwf
    installed := Hinstalled' }⟩⟩

/-- Compatibility form for non-nested callers which already translate the
old constructor in the target environment. -/
theorem RestoredConstructorStep.installation
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (constructor : VConstVal)
    (Hold : TrConstVal safety sourceVEnv
      (.ctorInfo Hstep.oldInfo) constructor)
    (Htype : TrExprS sourceVEnv Hstep.oldInfo.levelParams []
      Hstep.restored.newInfo.type constructor.type)
    (Hwf : constructor.toVConstant.WF sourceVEnv) :
    ∃ targetVEnv,
      Nonempty (RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  apply Hstep.installationOfMetadata Hvalid constructor
  · exact Hold.1.1
  · simpa [ConstantInfo.levelParams, ConstantInfo.toConstantVal] using
      Hold.1.2.1
  · simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using Hold.2
  · exact Htype
  · exact Hwf

inductive RestoredConstructorInstallationTrace
    (safety : DefinitionSafety) :
    ∀ {names sourceProdEnv targetProdEnv},
      StateForMTrace (RestoredConstructorStep result loweredEnv)
        names sourceProdEnv targetProdEnv →
      VEnv → List VConstVal → VEnv → Prop
  | nil (sourceProdEnv : Environment) (sourceVEnv : VEnv) :
      RestoredConstructorInstallationTrace safety
        (StateForMTrace.nil (P := RestoredConstructorStep result loweredEnv)
          (source := sourceProdEnv)) sourceVEnv [] sourceVEnv
  | cons
      (Hstep : RestoredConstructorStep result loweredEnv ctorName
        sourceProdEnv middleProdEnv)
      (Htail : StateForMTrace (RestoredConstructorStep result loweredEnv)
        names middleProdEnv targetProdEnv)
      (Hsemantic : RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv middleVEnv)
      (Hrest : RestoredConstructorInstallationTrace safety Htail middleVEnv
        constructors targetVEnv) :
      RestoredConstructorInstallationTrace safety (.cons Hstep Htail)
        sourceVEnv (Hsemantic.constructor :: constructors) targetVEnv

theorem RestoredConstructorInstallationTrace.translatedFresh
    {names : List Name} {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace (RestoredConstructorStep result loweredEnv)
      names sourceProdEnv targetProdEnv}
    {sourceVEnv targetVEnv : VEnv} {constructors : List VConstVal}
    (H : RestoredConstructorInstallationTrace safety Htrace sourceVEnv
      constructors targetVEnv)
    (hsourceWF : sourceProdEnv.constants.WF) :
    ∃ entries,
      ∃ Hfresh : FreshConstantTrace sourceProdEnv entries targetProdEnv,
        TranslatedFreshConstantTrace safety Hfresh sourceVEnv constructors
          targetVEnv := by
  induction H with
  | nil => exact ⟨[], .nil, .nil _ _⟩
  | @cons ctorName sourceProdEnv middleProdEnv names targetProdEnv
      sourceVEnv middleVEnv constructors targetVEnv Hstep Htail Hsemantic
      Hrest ih =>
    let ci : ConstantInfo := .ctorInfo Hstep.restored.newInfo
    have hfresh : sourceProdEnv.find? ci.name = none :=
      find?_none_of_contains_false hsourceWF Hstep.restored.fresh
    have hmiddle : middleProdEnv = sourceProdEnv.add ci :=
      congrArg Prod.snd Hstep.restored.output
    have hmiddleWF : middleProdEnv.constants.WF :=
      hmiddle.symm ▸ constantsWF_add_checked hsourceWF hfresh
    rcases ih hmiddleWF with
      ⟨entries, Hfresh, Htranslated⟩
    have HtranslatedTail :
        ∃ Hfresh' : FreshConstantTrace (sourceProdEnv.add ci) entries
            targetProdEnv,
          TranslatedFreshConstantTrace safety Hfresh' middleVEnv constructors
            targetVEnv := by
      exact hmiddle ▸ ⟨Hfresh, Htranslated⟩
    rcases HtranslatedTail with ⟨Hfresh', Htranslated'⟩
    exact ⟨ci :: entries, .cons hfresh Hfresh',
      .cons hfresh Hfresh' Hsemantic.translated Hsemantic.wf
        Hsemantic.installed Htranslated'⟩

theorem RestoredConstructorInstallationTrace.checking
    {names : List Name} {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace (RestoredConstructorStep result loweredEnv)
      names sourceProdEnv targetProdEnv}
    {sourceVEnv targetVEnv : VEnv} {constructors : List VConstVal}
    (H : RestoredConstructorInstallationTrace safety Htrace sourceVEnv
      constructors targetVEnv)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv) :
    CheckingEnv safety targetProdEnv targetVEnv := by
  induction H with
  | nil => exact Hvalid
  | cons Hstep Htail Hsemantic Hrest ih =>
    exact ih (Hsemantic.checking Hvalid)

/-- One source constructor paired with the exact operational restoration
step that installs it.  Source translation is stated in the canonical
post-header environment, not the production interleaved environment. -/
structure RestoredSourceConstructorSemantics
    (lparams : List Name) (safety : DefinitionSafety) (canonicalEnv : VEnv)
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (source : Constructor) where
  constructor : VConstVal
  sourceTranslation : TrSourceConst canonicalEnv lparams source.name
    source.type constructor
  restoredTranslation : TrConstVal safety canonicalEnv
    (.ctorInfo Hstep.restored.newInfo) constructor

/-- Positional source-constructor semantics for the exact constructor
restoration fold of one family. -/
inductive RestoredSourceConstructorTrace
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment)
    (lparams : List Name) (safety : DefinitionSafety) (canonicalEnv : VEnv) :
    List Name → Environment → Environment →
      List Constructor → List VConstVal → Prop
  | nil (sourceProdEnv : Environment) :
      RestoredSourceConstructorTrace result loweredEnv lparams safety canonicalEnv
        [] sourceProdEnv sourceProdEnv [] []
  | cons
      (Hstep : RestoredConstructorStep result loweredEnv ctorName
        sourceProdEnv middleProdEnv)
      (Hsemantic : RestoredSourceConstructorSemantics lparams safety
        canonicalEnv Hstep source)
      (Hrest : RestoredSourceConstructorTrace result loweredEnv lparams safety canonicalEnv
        names middleProdEnv targetProdEnv sources constructors) :
      RestoredSourceConstructorTrace result loweredEnv lparams safety canonicalEnv
        (ctorName :: names) sourceProdEnv targetProdEnv (source :: sources)
        (Hsemantic.constructor :: constructors)

theorem RestoredSourceConstructorTrace.forall₂
    (H : RestoredSourceConstructorTrace result loweredEnv lparams safety canonicalEnv names
      sourceProdEnv targetProdEnv sources constructors) :
    List.Forall₂ (fun source constructor =>
      TrSourceConst canonicalEnv lparams source.name source.type constructor)
      sources constructors := by
  induction H with
  | nil => exact .nil
  | cons Hstep Hsemantic Hrest ih =>
    exact .cons Hsemantic.sourceTranslation ih


end VerifyInductive
end Lean4Lean
