import Lean4Lean.Verify.Inductive.PrimitiveSemanticRun
import Lean4Lean.Verify.Inductive.CompletedEquationAssembly

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Close a skeleton-free primitive run against the independent inductive
specification, reconstructing its equation batch canonically. -/
theorem SemanticPrimitiveRunWithStatsResult.addInductCanonical
    (Hrun : SemanticPrimitiveRunWithStatsResult c stats nparams depth
      sourceEnv indTypes isUnsafe outEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      isUnsafe) :
    ∃ decl : VInductDecl, ∃ finalVEnv : VEnv,
      VEnv.AddInduct sourceEnv decl finalVEnv := by
  rcases Hrun with ⟨decl, _ctorEnv, _R, ⟨Hrecursors⟩⟩
  have hnonempty : indTypes.toList ≠ [] := by
    rcases Hshape with ⟨_, _, _, hbool | ⟨binderName, binderInfo, hnat⟩⟩
    · simp [hbool]
    · simp [hnat]
  rcases Hrecursors.canonicalCompletedRuleTranslation with ⟨T⟩
  exact ⟨decl, Hrecursors.outVEnv.addDefEqRules T.rules,
    Hrecursors.addInductOfOrdinaryCompilation T.rules T.rulesWF hnonempty
      T.compilation⟩

/-- Declaration-facing skeleton-free primitive refinement, retaining the
source checker-context equalities needed by environment composition. -/
theorem VerifiedSemanticPrimitiveInductiveRunResult.addInductCanonical
    (Hrun : VerifiedSemanticPrimitiveInductiveRunResult source nparams types
      numNested outEnv) :
    ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
      c'.env = source.env ∧
      c'.safety = source.safety ∧
      c'.lparams = source.lparams ∧
      ∃ decl : VInductDecl, ∃ finalVEnv : VEnv,
        VEnv.AddInduct Hc'.venv decl finalVEnv := by
  rcases Hrun with
    ⟨c', stats, depth, commonParams, commonLevel, Hc', henv, hsafety,
      hlparams, Hsemantic, Hshape, Hphases⟩
  rcases Hphases.addInductCanonical Hshape with
    ⟨decl, finalVEnv, Hadd⟩
  exact ⟨c', Hc', henv, hsafety, hlparams, decl, finalVEnv, Hadd⟩

end VerifyInductive
end Lean4Lean
