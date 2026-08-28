import Lean4Lean.Verify.Inductive.PrimitiveSemanticAddInduct
import Lean4Lean.Verify.Inductive.Run.SemanticSpecification

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Primitive Bool/Nat checking produces the same independent source
translation and `AddInduct` judgment as the ordinary checker path.  The
primitive installation strategy is an executable detail and does not change
the abstract specification. -/
theorem SemanticPrimitiveRunWithStatsResult.independentSpecification
    (Hrun : SemanticPrimitiveRunWithStatsResult c stats nparams depth
      sourceEnv indTypes isUnsafe outEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      isUnsafe)
    (hproj : ProjectionConstPreservation) :
    Nonempty (InductiveSpecificationResult sourceEnv c.lparams nparams
      indTypes.toList isUnsafe) := by
  rcases Hrun with ⟨decl, _ctorEnv, R, ⟨Hrecursors⟩⟩
  have hnonempty : indTypes.toList ≠ [] := by
    rcases Hshape with ⟨_, _, _, hbool | ⟨binderName, binderInfo, hnat⟩⟩
    · simp [hbool]
    · simp [hnat]
  rcases Hrecursors.canonicalCompletedRuleTranslation hproj with ⟨T⟩
  exact ⟨{
    decl := decl
    envTypes := R.headerVEnv
    envCtors := R.context.venv
    finalVEnv := Hrecursors.outVEnv.addDefEqRules T.rules
    source := R.core
    extension := Hrecursors.addInductOfOrdinaryCompilation T.rules
      T.rulesWF hnonempty T.compilation }⟩

end VerifyInductive
end Lean4Lean
