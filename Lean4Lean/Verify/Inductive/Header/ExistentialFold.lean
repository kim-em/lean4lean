import Lean4Lean.Verify.Inductive.Header.Existential
import Lean4Lean.Verify.Inductive.Header.LoopInd

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
namespace VerifyInductive
namespace checkInductiveTypes.loopType

/-- The executable per-header statistics update leaves the cached common
parameters untouched, so the semantic cache can be transported without any
new evidence. -/
def ParameterCachePrefix.reindexUpdatedStats
    (H : ParameterCachePrefix
      env Us scope stats done depth)
    (lctx : LocalContext) (resultLevel : Level) (first : Bool)
    (nindices : Nat) (indName : Name) :
    ParameterCachePrefix env Us scope
      (checkInductiveTypes.loopInd.updatedStats stats lctx resultLevel first
        nindices indName)
      done depth :=
  H.reindex (by
    cases first <;> simp [checkInductiveTypes.loopInd.updatedStats])

/-- Exact cached-context suffixes survive the same per-header statistics
update. -/
def ParameterContextSuffix.reindexUpdatedStats
    (H : ParameterContextSuffix Hc stats depth)
    (lctx : LocalContext) (resultLevel : Level) (first : Bool)
    (nindices : Nat) (indName : Name) :
    ParameterContextSuffix Hc
      (checkInductiveTypes.loopInd.updatedStats stats lctx resultLevel first
        nindices indName) depth :=
  H.reindex (by
    cases first <;> simp [checkInductiveTypes.loopInd.updatedStats])

end checkInductiveTypes.loopType

end VerifyInductive
end Lean4Lean
