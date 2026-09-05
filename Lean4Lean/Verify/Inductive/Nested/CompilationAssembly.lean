import Lean4Lean.Verify.Inductive.Nested.Compilation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive
/-- Assemble the abstract nested extension from its actual dependency stages.
Projection metadata is installed between constructors and recursors, exactly
as in `VInductBlock.install`; no flattened pre-projection installation is used
as a surrogate for this semantic trace. -/
theorem RestoredNestedDeclarationsResult.addInductOfStagedInstallation
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames types auxRecNames out)
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
    (Hformation : decl.NestedFormationWF sourceEnv)
    (Hsource : TrInductDeclCore sourceEnv lparams nparams sourceTypes
      isUnsafe decl envTypes envCtors)
    (hnonempty : sourceTypes ≠ [])
    (HrecursorsAdded :
      (envCtors.addProjections decl.projectionEntries).addConstVals
        (primaryRecursors ++ auxiliaryRecursors) = some outVEnv)
    (HtypesWF : ∀ ci ∈ decl.typeConstants,
      ci.toVConstant.WF sourceEnv)
    (HctorsWF : ∀ ci ∈ decl.constructorConstants,
      ci.toVConstant.WF envTypes)
    (HrecursorsWF : ∀ ci ∈ primaryRecursors ++ auxiliaryRecursors,
      ci.toVConstant.WF
        (envCtors.addProjections decl.projectionEntries))
    (HrulesWF : ∀ df ∈ primaryRules ++ auxiliaryRules,
      df.WF outVEnv) :
    VEnv.AddInduct sourceEnv decl
      (outVEnv.addDefEqRules (primaryRules ++ auxiliaryRules)) := by
  let block := canonicalRestoredBlock decl primaryRecursors
    auxiliaryRecursors primaryRules auxiliaryRules
  have hnames : List.Nodup
      ((block.types ++ block.ctors ++ block.recursors).map (·.name)) := by
    have hraw : ∃ rawOut,
        envCtors.addConstVals (primaryRecursors ++ auxiliaryRecursors) =
          some rawOut := by
      rw [VEnv.addProjections_addConstVals] at HrecursorsAdded
      cases hraw : envCtors.addConstVals
          (primaryRecursors ++ auxiliaryRecursors) with
      | none => simp [hraw] at HrecursorsAdded
      | some rawOut => exact ⟨rawOut, rfl⟩
    rcases hraw with ⟨rawOut, hraw⟩
    have hall : sourceEnv.addConstVals
        (decl.typeConstants ++ decl.constructorConstants ++
          (primaryRecursors ++ auxiliaryRecursors)) = some rawOut := by
      simp [VEnv.addConstVals_append, Hsource.typesAdded,
        Hsource.ctorsAdded, hraw]
    simpa [block, canonicalRestoredBlock] using
      VEnv.addConstVals_names_nodup hall
  have Haux : AuxiliaryRestorationPrefix decl block main auxiliaryRecursors
      auxiliaryRules := by
    exact Hauxiliary.prefix (AuxiliaryRestorationPrefix.empty decl block main)
  let Hcompile : NestedCompilationCertificate sourceEnv decl block :=
    NestedCompilationCertificate.ofRestoration sourceEnv envTypes envCtors
      decl block main rest htypesSource primaryRecursors auxiliaryRecursors
      primaryRules auxiliaryRules
      (HprimaryRecursors.recursorCertificate htypesSource) HprimaryRules
      hprimaryLength Haux rfl rfl rfl Hsource.typesAdded Hsource.ctorsAdded rfl rfl
      hnames
  have HblockWF : block.WF sourceEnv := by
    refine ⟨envTypes, envCtors, outVEnv, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [block, canonicalRestoredBlock] using Hsource.typesAdded
    · simpa [block, canonicalRestoredBlock] using Hsource.ctorsAdded
    · simpa [block, canonicalRestoredBlock] using HrecursorsAdded
    ·
      simpa [block, canonicalRestoredBlock] using HtypesWF
    ·
      simpa [block, canonicalRestoredBlock] using HctorsWF
    ·
      simpa [block, canonicalRestoredBlock] using HrecursorsWF
    · simpa [block, canonicalRestoredBlock] using HrulesWF
  have Hinstall : block.install sourceEnv = some
      (outVEnv.addDefEqRules (primaryRules ++ auxiliaryRules)) := by
    simp [VInductBlock.install, block, canonicalRestoredBlock,
      Hsource.typesAdded, Hsource.ctorsAdded, HrecursorsAdded]
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      Hsource
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty Hsource hnonempty)
  exact .intro
    ⟨Lean4Lean.TrInductDecl.sourceWF Htranslated,
      .nested Hformation VEnv.LE.rfl⟩
    Hcompile.compilesTo HblockWF Hinstall

end VerifyInductive
end Lean4Lean
