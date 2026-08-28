import Lean4Lean.Verify.Inductive.Header.SemanticFold
import Lean4Lean.Verify.Inductive.Header.SemanticResult

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive
namespace checkInductiveTypes.loopInd

/-- Public skeleton-free completion theorem for mutual headers.  A successful
production traversal existentially determines the abstract header-only
declaration, its exact source translations and normalized telescopes, and the
standard materialized-header interface consumed by constructor checking. -/
theorem checkInductiveTypes.materializesSemanticHeaders
    {c : AddInductive.Context} {indTypes : Array InductiveType}
    {nparams : Nat} {isUnsafe : Bool} {alpha : Type}
    (k : AddInductive.InductiveStats → AddInductive.M alpha)
    (Q : alpha → Prop)
    (Hc : ContextWF c)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < indTypes.size)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hc' : ContextWF c') →
      (Hsemantic :
        checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
          Hc'.venv c'.lparams nparams commonParams commonLevel
            indTypes.toList) →
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats
          (Hsemantic.headerDecl isUnsafe) depth →
      (k stats c').WF Q) :
    (AddInductive.checkInductiveTypes nparams indTypes k c).WF Q := by
  apply checkInductiveTypes.accumulatesSemanticHeaders k Q Hc hctx
    hnonempty hconsume
  intro c' stats depth commonParams commonLevel Hc' _henv _hsafety
    _hlparams Hsemantic
    hlevels hlevelParams _hindicesSize hindices
    _hconstsSize hconsts _hnonempty hparams hcommonParams
    Hcache Hsuffix Hambient hcommon
  exact Hfinish Hc' Hsemantic <|
    Hsemantic.materializedResult hlevels hlevelParams hindices hconsts
      hparams hcommonParams Hcache Hsuffix Hambient hcommon

end checkInductiveTypes.loopInd
end VerifyInductive
end Lean4Lean
