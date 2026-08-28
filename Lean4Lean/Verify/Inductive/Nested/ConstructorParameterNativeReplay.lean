import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterValidationRun
import Lean4Lean.Verify.Inductive.Nested.LoweringTrace

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- The concrete parameter context returned by an actual lowering run has a
semantic metacontext in the source environment.  Its free variables are also
fresh for the independent type-checker run used by restored-constructor
validation; both facts are consequences of the retained lowering trace. -/
theorem NestedLoweringRun.resultParameterMLCtx
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (henv : venv.WF)
    (Hfirst : ∀ first rest, types = first :: rest →
      ∃ target, TrExprS venv Us [] first.type target)
    (hprefix : initialState.ngen.namePrefix = `_nested_fresh) :
    ∃ mlctx : TypeChecker.MLCtx,
      mlctx.lctx = out.1.lctx ∧
      mlctx.WF venv Us ∧
      (∀ fv ∈ mlctx.vlctx.fvars,
        ({} : TypeChecker.State).ngen.Reserves fv) := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, htypes, Hopening,
      _hnewTypes, _hnestedAux, _hnextIdx, _hparamsPrefix, Hctx,
      _Hselection, Hqueue⟩
  rcases Hfirst first rest htypes with ⟨target, Htype⟩
  rcases Hopening.toMLCtx henv Hctx.wf .nil rfl trivial Htype with
    ⟨mlctx, _targetTail, hlctx, hmlctx, _Htail⟩
  refine ⟨mlctx, ?_, hmlctx, ?_⟩
  · exact hlctx.trans Hqueue.resultContext.1.symm
  · intro fv hfv
    apply H.resultContextKernelFresh hprefix fv
    rw [Hqueue.resultContext.1, ← hlctx, hmlctx.tr.fvars_eq]
    exact hfv

end VerifyInductive
end Lean4Lean
