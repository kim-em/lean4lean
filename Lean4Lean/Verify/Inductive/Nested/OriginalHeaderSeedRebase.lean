import Lean4Lean.Verify.Inductive.Recursor.Origins
import Lean4Lean.Verify.Inductive.Recursor.Telescope
import Lean4Lean.Verify.Typing.EnvironmentRestriction

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

theorem VEnv.addConstVals_projections_eq
    {base out : VEnv} {constants : List VConstVal}
    (H : base.addConstVals constants = some out) :
    out.projections = base.projections := by
  induction constants generalizing base with
  | nil =>
      simp [VEnv.addConstVals] at H
      subst out
      rfl
  | cons ci constants ih =>
      simp only [VEnv.addConstVals] at H
      cases hadd : base.addConst ci.name ci.toVConstant with
      | none => simp [hadd] at H
      | some next =>
          rw [hadd] at H
          rw [ih H]
          unfold VEnv.addConst at hadd
          split at hadd <;> cases hadd
          rfl

end VerifyInductive
end Lean4Lean
