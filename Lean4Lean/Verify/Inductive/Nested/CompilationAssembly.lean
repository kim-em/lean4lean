import Lean4Lean.Verify.Inductive.Nested.Compilation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- Assemble nested compilation from the exact primary and auxiliary
installation traces.  The final name-uniqueness proof is reconstructed from
the structural primary layout and the translated freshness trace; callers do
not supply a permutation of an arbitrary production trace. -/
theorem RestoredNestedDeclarationsResult.canonicalNestedCompilationOfLayouts
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames types auxRecNames out)
    (Hprimary : RestoredInductiveInstallationTrace safety H.inductives
      sourceEnv primaryConstants primaryVEnv)
    (HauxInstall : RestoredRecursorInstallationTrace safety H.auxiliaries
      primaryVEnv auxiliaryConstants outVEnv)
    (layout : RestoredPrimaryConstantLayout primaryConstants)
    (envTypes envCtors : VEnv) (main : VInductiveType)
    (rest : List VInductiveType)
    (htypesSource : decl.types = main :: rest)
    (primaryRecursors auxiliaryRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq)
    (HprimaryRecursors : RestoredPrimaryRecursorCertificate decl result
      loweredEnv auxRec allIndNames safety H.inductives Hprimary
      primaryRecursors)
    (HprimaryRules : NestedIotaBuildCertificate decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules) primaryRules)
    (hprimaryLength : primaryRules.length = decl.ownedConstructors.length)
    (htypesAdded : sourceEnv.addConstVals decl.typeConstants = some envTypes)
    (hctorsAdded : envTypes.addConstVals decl.constructorConstants =
      some envCtors)
    (Hauxiliary : RestoredAuxiliarySemanticTrace decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules) main safety trEnv H.auxiliaries
      [] [] auxiliaryRecursors auxiliaryRules)
    (htypesLayout : layout.types = decl.typeConstants)
    (hctorsLayout : layout.ctors = decl.constructorConstants)
    (hprimaryLayout : layout.recursors = primaryRecursors)
    (hauxLayout : auxiliaryConstants = auxiliaryRecursors)
    (hsourceWF : sourceProdEnv.constants.WF) :
    Nonempty (NestedCompilationCertificate sourceEnv decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules)) := by
  let block := canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
    primaryRules auxiliaryRules
  have Haux : AuxiliaryRestorationPrefix decl block main auxiliaryRecursors
      auxiliaryRules := by
    exact Hauxiliary.prefix (AuxiliaryRestorationPrefix.empty decl block main)
  rcases H.translatedFreshOfInstallation Hprimary HauxInstall hsourceWF with
    ⟨entries, Hfresh, Htranslated⟩
  have hinstalledNames :
      (primaryConstants ++ auxiliaryConstants).map (·.name) =
        entries.map (·.name) := Htranslated.names
  have horder :
      (decl.typeConstants ++ decl.constructorConstants ++
          (primaryRecursors ++ auxiliaryRecursors)) ~
        primaryConstants ++ auxiliaryConstants := by
    rw [← htypesLayout, ← hctorsLayout, ← hprimaryLayout, ← hauxLayout]
    simpa only [List.append_assoc] using
      layout.grouped.append_right auxiliaryConstants
  have hnames : List.Nodup
      ((block.types ++ block.ctors ++ block.recursors).map (·.name)) := by
    have htarget : List.Nodup
        ((primaryConstants ++ auxiliaryConstants).map (·.name)) := by
      rw [hinstalledNames]
      exact Hfresh.namesNodup hsourceWF
    have hmapped := horder.map (·.name)
    exact hmapped.nodup_iff.mpr htarget
  exact ⟨NestedCompilationCertificate.ofRestoration sourceEnv envTypes
    envCtors decl block main rest htypesSource primaryRecursors
    auxiliaryRecursors primaryRules auxiliaryRules
    HprimaryRecursors.recursorCertificate HprimaryRules hprimaryLength Haux
    rfl rfl htypesAdded hctorsAdded rfl rfl hnames⟩

/-- Final abstract installation endpoint for a canonically restored nested
block.  Both the block installation and its nested-compilation judgment are
derived from the same exact primary/auxiliary traces and primary layout. -/
theorem RestoredNestedDeclarationsResult.addInductOfLayouts
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames types auxRecNames out)
    (Hprimary : RestoredInductiveInstallationTrace safety H.inductives
      sourceEnv primaryConstants primaryVEnv)
    (HauxInstall : RestoredRecursorInstallationTrace safety H.auxiliaries
      primaryVEnv auxiliaryConstants outVEnv)
    (layout : RestoredPrimaryConstantLayout primaryConstants)
    (envTypes envCtors : VEnv) (main : VInductiveType)
    (rest : List VInductiveType)
    (htypesSource : decl.types = main :: rest)
    (primaryRecursors auxiliaryRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq)
    (HprimaryRecursors : RestoredPrimaryRecursorCertificate decl result
      loweredEnv auxRec allIndNames safety H.inductives Hprimary
      primaryRecursors)
    (HprimaryRules : NestedIotaBuildCertificate decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules) primaryRules)
    (hprimaryLength : primaryRules.length = decl.ownedConstructors.length)
    (Hauxiliary : RestoredAuxiliarySemanticTrace decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules) main safety trEnv H.auxiliaries
      [] [] auxiliaryRecursors auxiliaryRules)
    (htypesLayout : layout.types = decl.typeConstants)
    (hctorsLayout : layout.ctors = decl.constructorConstants)
    (hprimaryLayout : layout.recursors = primaryRecursors)
    (hauxLayout : auxiliaryConstants = auxiliaryRecursors)
    (Hformation : decl.NestedFormationWF sourceEnv)
    (Hsource : TrInductDeclCore sourceEnv lparams nparams sourceTypes
      isUnsafe decl envTypes envCtors)
    (hnonempty : sourceTypes ≠ [])
    (hsourceWF : sourceProdEnv.constants.WF)
    (HtypesWF : ∀ ci ∈ decl.typeConstants,
      ci.toVConstant.WF sourceEnv)
    (HctorsWF : ∀ ci ∈ decl.constructorConstants,
      ci.toVConstant.WF envTypes)
    (HrecursorsWF : ∀ ci ∈ primaryRecursors ++ auxiliaryRecursors,
      ci.toVConstant.WF envCtors)
    (HrulesWF : ∀ df ∈ primaryRules ++ auxiliaryRules,
      df.WF outVEnv) :
    VEnv.AddInduct sourceEnv decl
      (outVEnv.addDefEqRules (primaryRules ++ auxiliaryRules)) := by
  let block := canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
    primaryRules auxiliaryRules
  have Hcompile := H.canonicalNestedCompilationOfLayouts Hprimary HauxInstall
    layout envTypes envCtors main rest htypesSource primaryRecursors
    auxiliaryRecursors primaryRules auxiliaryRules HprimaryRecursors
    HprimaryRules hprimaryLength Hsource.typesAdded Hsource.ctorsAdded
    Hauxiliary htypesLayout hctorsLayout hprimaryLayout hauxLayout hsourceWF
  rcases H.translatedFreshOfInstallation Hprimary HauxInstall hsourceWF with
    ⟨_entries, _Hfresh, Htranslated⟩
  have horder : block.types ++ block.ctors ++ block.recursors ~
      primaryConstants ++ auxiliaryConstants := by
    change decl.typeConstants ++ decl.constructorConstants ++
        (primaryRecursors ++ auxiliaryRecursors) ~
      primaryConstants ++ auxiliaryConstants
    rw [← htypesLayout, ← hctorsLayout, ← hprimaryLayout, ← hauxLayout]
    simpa only [List.append_assoc] using
      layout.grouped.append_right auxiliaryConstants
  let Hblock : RestoredBlockCertificate sourceEnv block := {
    constants := primaryConstants ++ auxiliaryConstants
    outVEnv := outVEnv
    order := horder
    installed := Htranslated.abstract
    typesWF := by
      simpa [block, canonicalRestoredBlock] using HtypesWF
    ctorsWF := by
      intro targetEnv hadded
      have hadded' : sourceEnv.addConstVals decl.typeConstants =
          some targetEnv := by
        simpa [block, canonicalRestoredBlock] using hadded
      have htarget : targetEnv = envTypes :=
        (Option.some.inj (Hsource.typesAdded.symm.trans hadded')).symm
      subst targetEnv
      simpa [block, canonicalRestoredBlock] using HctorsWF
    recursorsWF := by
      intro targetTypes targetCtors htypesAdded hctorsAdded
      have htypesAdded' : sourceEnv.addConstVals decl.typeConstants =
          some targetTypes := by
        simpa [block, canonicalRestoredBlock] using htypesAdded
      have htargetTypes : targetTypes = envTypes :=
        (Option.some.inj (Hsource.typesAdded.symm.trans htypesAdded')).symm
      subst targetTypes
      have hctorsAdded' : envTypes.addConstVals decl.constructorConstants =
          some targetCtors := by
        simpa [block, canonicalRestoredBlock] using hctorsAdded
      have htargetCtors : targetCtors = envCtors :=
        (Option.some.inj (Hsource.ctorsAdded.symm.trans hctorsAdded')).symm
      subst targetCtors
      simpa [block, canonicalRestoredBlock] using HrecursorsWF
    rulesWF := by
      simpa [block, canonicalRestoredBlock] using HrulesWF }
  rcases Hcompile with ⟨Hcompile⟩
  simpa [block, canonicalRestoredBlock] using
    Hblock.addInductOfNestedFormation Hformation Hsource hnonempty Hcompile

/-- Mutual-safe final abstract installation.  The executable restoration
order is intentionally absent from the semantic installation premise:
`Hcanonical` installs the exact restored production/abstract pairs in the
dependency order `types ++ constructors ++ recursors`.  A separate fresh
production trace relates this canonical production map to the environment
actually returned by restoration; see `AddConstants.checkingOfFreshPermutation`.
-/
theorem RestoredNestedDeclarationsResult.addInductOfCanonicalInstallation
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames types auxRecNames out)
    (Hcanonical : AddConstants safety sourceProdEnv sourceEnv
      canonicalEntries canonicalProdEnv outVEnv)
    (primaryConstants auxiliaryConstants : List VConstVal)
    (hcanonicalValues : canonicalEntries.map Prod.snd =
      primaryConstants ++ auxiliaryConstants)
    (layout : RestoredPrimaryConstantLayout primaryConstants)
    (envTypes envCtors : VEnv) (main : VInductiveType)
    (rest : List VInductiveType)
    (htypesSource : decl.types = main :: rest)
    (primaryRecursors auxiliaryRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq)
    (HprimaryRecursors : RestoredPrimaryRecursorSemanticTrace decl safety
      envCtors H.inductives (main :: rest) primaryRecursors)
    (HprimaryRules : NestedIotaBuildCertificate decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules) primaryRules)
    (hprimaryLength : primaryRules.length = decl.ownedConstructors.length)
    (Hauxiliary : RestoredAuxiliarySemanticTrace decl
      (canonicalRestoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules) main safety trEnv H.auxiliaries
      [] [] auxiliaryRecursors auxiliaryRules)
    (htypesLayout : layout.types = decl.typeConstants)
    (hctorsLayout : layout.ctors = decl.constructorConstants)
    (hprimaryLayout : layout.recursors = primaryRecursors)
    (hauxLayout : auxiliaryConstants = auxiliaryRecursors)
    (Hformation : decl.NestedFormationWF sourceEnv)
    (Hsource : TrInductDeclCore sourceEnv lparams nparams sourceTypes
      isUnsafe decl envTypes envCtors)
    (hnonempty : sourceTypes ≠ [])
    (HtypesWF : ∀ ci ∈ decl.typeConstants,
      ci.toVConstant.WF sourceEnv)
    (HctorsWF : ∀ ci ∈ decl.constructorConstants,
      ci.toVConstant.WF envTypes)
    (HrecursorsWF : ∀ ci ∈ primaryRecursors ++ auxiliaryRecursors,
      ci.toVConstant.WF envCtors)
    (HrulesWF : ∀ df ∈ primaryRules ++ auxiliaryRules,
      df.WF outVEnv) :
    VEnv.AddInduct sourceEnv decl
      (outVEnv.addDefEqRules (primaryRules ++ auxiliaryRules)) := by
  let block := canonicalRestoredBlock decl primaryRecursors
    auxiliaryRecursors primaryRules auxiliaryRules
  have horder : block.types ++ block.ctors ++ block.recursors ~
      canonicalEntries.map Prod.snd := by
    change decl.typeConstants ++ decl.constructorConstants ++
        (primaryRecursors ++ auxiliaryRecursors) ~
      canonicalEntries.map Prod.snd
    rw [hcanonicalValues, ← htypesLayout, ← hctorsLayout,
      ← hprimaryLayout, ← hauxLayout]
    simpa only [List.append_assoc] using
      layout.grouped.append_right auxiliaryConstants
  have hnames : List.Nodup
      ((block.types ++ block.ctors ++ block.recursors).map (·.name)) := by
    exact (horder.map (·.name)).nodup_iff.mpr
      (VEnv.addConstVals_names_nodup Hcanonical.abstract)
  have Haux : AuxiliaryRestorationPrefix decl block main auxiliaryRecursors
      auxiliaryRules := by
    exact Hauxiliary.prefix (AuxiliaryRestorationPrefix.empty decl block main)
  let Hcompile : NestedCompilationCertificate sourceEnv decl block :=
    NestedCompilationCertificate.ofRestoration sourceEnv envTypes envCtors
      decl block main rest htypesSource primaryRecursors auxiliaryRecursors
      primaryRules auxiliaryRules
      (HprimaryRecursors.recursorCertificate htypesSource) HprimaryRules
      hprimaryLength Haux rfl rfl Hsource.typesAdded Hsource.ctorsAdded rfl rfl
      hnames
  let Hblock : RestoredBlockCertificate sourceEnv block := {
    constants := canonicalEntries.map Prod.snd
    outVEnv := outVEnv
    order := horder
    installed := Hcanonical.abstract
    typesWF := by
      simpa [block, canonicalRestoredBlock] using HtypesWF
    ctorsWF := by
      intro targetEnv hadded
      have hadded' : sourceEnv.addConstVals decl.typeConstants =
          some targetEnv := by
        simpa [block, canonicalRestoredBlock] using hadded
      have htarget : targetEnv = envTypes :=
        (Option.some.inj (Hsource.typesAdded.symm.trans hadded')).symm
      subst targetEnv
      simpa [block, canonicalRestoredBlock] using HctorsWF
    recursorsWF := by
      intro targetTypes targetCtors htypesAdded hctorsAdded
      have htypesAdded' : sourceEnv.addConstVals decl.typeConstants =
          some targetTypes := by
        simpa [block, canonicalRestoredBlock] using htypesAdded
      have htargetTypes : targetTypes = envTypes :=
        (Option.some.inj (Hsource.typesAdded.symm.trans htypesAdded')).symm
      subst targetTypes
      have hctorsAdded' : envTypes.addConstVals decl.constructorConstants =
          some targetCtors := by
        simpa [block, canonicalRestoredBlock] using hctorsAdded
      have htargetCtors : targetCtors = envCtors :=
        (Option.some.inj (Hsource.ctorsAdded.symm.trans hctorsAdded')).symm
      subst targetCtors
      simpa [block, canonicalRestoredBlock] using HrecursorsWF
    rulesWF := by
      simpa [block, canonicalRestoredBlock] using HrulesWF }
  simpa [block, canonicalRestoredBlock] using
    Hblock.addInductOfNestedFormation Hformation Hsource hnonempty Hcompile

end VerifyInductive
end Lean4Lean
