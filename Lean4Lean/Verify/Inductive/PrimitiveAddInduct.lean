import Lean4Lean.Verify.Inductive.PrimitiveRunWithStats
import Lean4Lean.Verify.Inductive.CompletedEquationAssembly

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A completed canonical primitive run refines the independent inductive
specification.  The equation batch is reconstructed from the completed
recursor phase, after the atomic primitive header/constructor prefix has
restored a valid abstract context. -/
theorem VerifiedPrimitiveInductiveRunResult.addInductCanonical
    (Hrun : VerifiedPrimitiveInductiveRunResult source skeleton envTypes
      types numNested outEnv) :
    ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
      ∃ decl : VInductDecl, ∃ finalVEnv : VEnv,
        VEnv.AddInduct Hc'.venv decl finalVEnv := by
  rcases Hrun with ⟨c', stats, decl, depth, Hc', Hdecl, Hmaterialized,
    ctorEnv, R, hnonempty, ⟨Hrecursors⟩⟩
  rcases Hrecursors.canonicalCompletedRuleTranslation with ⟨T⟩
  exact ⟨c', Hc', decl, Hrecursors.outVEnv.addDefEqRules T.rules,
    Hrecursors.addInductOfOrdinaryCompilation T.rules T.rulesWF hnonempty
      T.compilation⟩

end VerifyInductive
end Lean4Lean
