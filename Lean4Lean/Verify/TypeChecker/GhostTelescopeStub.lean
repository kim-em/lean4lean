import Lean4Lean.Verify.TypeChecker.Basic
import Lean4Lean.Verify.TypeChecker.FrameDefs
import Lean4Lean.Verify.Typing.TelescopeTranslation

/-!
# Temporary stub for the ghost telescope theorem

Exactly the statement proved on `agent/verify-inductives-strengthening-ghost`
(`Lean4Lean/Verify/TypeChecker/GhostTelescope.lean`): a successful `checkType` run certifies the
telescope it checked. This file is replaced by that proof when the branches are merged.
-/

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception
open Kernel

theorem checkType.WF_telTr {c : VContext} {s : VState} {e : Expr}
    (henv : EnvGF (fun _ => True) c.env)
    (hunf : ∀ ⦃k r : Expr⦄, s.unfold[k]? = some r → FVarsIn (fun _ => True) r)
    (h1 : e.FVarsIn (· ∈ c.vlctx.fvars)) (hcache : s.inferTypeC[e]? = none) :
    M.WF c s (checkType e) fun _ _ => ∃ e', TelTr c.venv c.lparams c.vlctx e e' := by
  sorry

end Lean4Lean.TypeChecker
