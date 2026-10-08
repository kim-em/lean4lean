import Lean4Lean.Verify.Inductive.Nested.Restoration.Translations
import Lean4Lean.Verify.Inductive.Nested.Restoration.FreshExtensions

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive
/-- Assemble the abstract nested extension from its actual dependency stages.
Projection metadata is installed between constructors and recursors, exactly
as in `VInductBlock.install`; no flattened pre-projection installation is used
as a surrogate for this semantic trace. -/
theorem NestedRestorationFolds.addInductOfInstallation
    (H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames types auxRecNames out)
    (envTypes envCtors : VEnv)
    (primaryRecursors auxiliaryRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq)
    (es : List (Name × InductiveSignature.CaseSchema))
    (Hcanonical : CompiledInductive sourceEnv decl
      { restoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules with eliminators := es })
    (Hformation : decl.NestedFormationWF sourceEnv)
    (Hsource : TrInductDeclCore sourceEnv lparams nparams sourceTypes
      isUnsafe decl envTypes envCtors)
    (hnonempty : sourceTypes ≠ [])
    (HrecursorsAdded :
      ((envCtors.addEliminators es).addProjections decl.projectionEntries).addConstVals
        (primaryRecursors ++ auxiliaryRecursors) = some outVEnv)
    (HtypesWF : ∀ ci ∈ decl.typeConstants,
      ci.toVConstant.WF sourceEnv)
    (HctorsWF : ∀ ci ∈ decl.constructorConstants,
      ci.toVConstant.WF envTypes)
    (HrecursorsWF : ∀ ci ∈ primaryRecursors ++ auxiliaryRecursors,
      ci.toVConstant.WF
        ((envCtors.addEliminators es).addProjections decl.projectionEntries))
    (HrulesWF : ∀ df ∈ primaryRules ++ auxiliaryRules,
      df.WF outVEnv)
    (Helim : VInductBlock.EliminatorsWF sourceEnv decl (decl.caseBlock es)) :
    VEnv.AddInduct sourceEnv decl
      (outVEnv.addDefEqRules (primaryRules ++ auxiliaryRules)) := by
  let block : VInductBlock := { restoredBlock decl primaryRecursors
    auxiliaryRecursors primaryRules auxiliaryRules with eliminators := es }
  have hnames : List.Nodup
      ((block.types ++ block.ctors ++ block.recursors).map (·.name)) := by
    have hraw : ∃ rawOut,
        envCtors.addConstVals (primaryRecursors ++ auxiliaryRecursors) =
          some rawOut := by
      rw [VEnv.addProjections_addConstVals, VEnv.addEliminators_addConstVals] at HrecursorsAdded
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
    simpa [block, restoredBlock] using
      VEnv.addConstVals_names_nodup hall
  have HblockWF : block.WF sourceEnv := by
    refine ⟨envTypes, envCtors, outVEnv, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [block, restoredBlock] using Hsource.typesAdded
    · simpa [block, restoredBlock] using Hsource.ctorsAdded
    · simpa [block, restoredBlock] using HrecursorsAdded
    ·
      simpa [block, restoredBlock] using HtypesWF
    ·
      simpa [block, restoredBlock] using HctorsWF
    ·
      simpa [block, restoredBlock] using HrecursorsWF
    · simpa [block, restoredBlock] using HrulesWF
  have Hinstall : block.install sourceEnv = some
      (outVEnv.addDefEqRules (primaryRules ++ auxiliaryRules)) := by
    simp [VInductBlock.install, block, restoredBlock,
      Hsource.typesAdded, Hsource.ctorsAdded, HrecursorsAdded]
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      Hsource
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty Hsource hnonempty)
  exact .intro
    ⟨Lean4Lean.TrInductDecl.sourceWF Htranslated,
      .nested Hformation VEnv.LE.rfl⟩
    ⟨rfl, rfl, rfl, hnames, Hcanonical⟩ HblockWF
    (Helim.congr_block rfl rfl rfl rfl) Hinstall

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Turn an abstract inductive installation obtained from exact nested
restoration into the concrete implementation-refinement boundary. Source
lookup preservation, final production/abstract alignment, and delta
conservativity are consequences of the restoration trace. The producer supplies
declaration origins and recursor provenance for the same source and target. -/
theorem NestedRestorationFolds.addInductConcrete
    (H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames types auxRecNames out)
    (Habstract : VEnv.AddInduct sourceVEnv decl targetVEnv)
    (Hchecking : CheckingEnv safety out.2 targetVEnv)
    (Hprovenance : NewRecursorsAligned safety
      sourceProdEnv.constants sourceVEnv out.2.constants targetVEnv)
    (hsourceWF : sourceProdEnv.constants.WF)
    (Horigins : InductInfosFromDecl sourceProdEnv.constants
      out.2.constants decl) :
    AddInduct safety sourceProdEnv.constants sourceVEnv decl
      out.2.constants targetVEnv := by
  rcases H.freshTraceNondelta hsourceWF with
    ⟨entries, Hfresh, hnondelta⟩
  cases Habstract with
  | intro Hdecl Hcompile Hblock Helim Hinstall =>
      apply AddInduct.intro _ Hdecl Hcompile Hblock Hinstall Horigins
      · intro name ci hfind
        exact Hfresh.preservesSourceMapFind hsourceWF hfind
      · intro _HsourceAligned
        exact Hchecking.aligned
      · exact Hfresh.deltaConservative hsourceWF hnondelta
      · exact Hprovenance
      · exact Helim

end VerifyInductive
end Lean4Lean
