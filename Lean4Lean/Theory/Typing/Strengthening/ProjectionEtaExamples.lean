import Lean4Lean.Theory.Typing.Strengthening.ProjectionEtaCancellation
import Lean4Lean.Theory.Typing.Strengthening.FullScope

/-! # Captured structure parameters disappear under projection

This tests the syntactic cancellation theorem at an actually registered structure
with a parameter and a field. No typing of the deliberately captured parameter is
asserted: the test identifies which scope condition cancellation can avoid.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A fresh variable can occur among expansion parameters and then disappear by
one computational projection. The endpoint is exactly the original lifted projection. -/
theorem captured_structure_projection (hinfo : env.projections s info)
    (hp : 0 < info.nparams) (hi : i < info.numFields) (e : VExpr) :
    ∃ out, RecordExpansion s info e.lift out ∧ ¬ out.Skips 1 0 ∧
      ProjectionCompute D (.proj s i out) (VExpr.proj s i e).lift := by
  let ps : List VExpr := .bvar 0 :: List.replicate (info.nparams - 1) (.sort .zero)
  have hps : ps.length = info.nparams := by simp only [ps, List.length_cons, List.length_replicate]; omega
  let out := structExpand s info [] ps e.lift
  have hR : RecordExpansion s info e.lift out := .expand .refl hps
  refine ⟨out, hR, ?_, hR.cancel_projection hinfo hi⟩
  intro hs
  have hbad := (skips_mkApps_iff.1 hs).2 (.bvar 0)
    (List.mem_append_left _ (by simp [ps]))
  simp [skips_iff, Skips'] at hbad

/-- Arbitrarily many parameter-capturing root expansions still cancel. Unlike a
fixed development bound, this theorem takes the actual finite expansion derivation. -/
theorem nested_structure_projection (R : RecordExpansion s info e.lift out)
    (hinfo : env.projections s info) (hi : i < info.numFields) (args : List VExpr) :
    ProjectionCompute D (mkApps (.proj s i out) (args.map VExpr.lift))
      (mkApps (.proj s i e) args).lift := by
  simpa only [VExpr.lift, VExpr.liftN_mkApps, VExpr.liftN] using
    (R.cancel_projection (D := D) hinfo hi).mkApps (args.map VExpr.lift)

end Lean4Lean.VEnv.Strengthening.PureObservation
