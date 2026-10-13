import Lean4Lean.Theory.Typing.Strengthening.FieldHeadExposure
import Lean4Lean.Theory.Typing.Strengthening.FullScope

/-! # Mixed function/structure eta with captured annotations

A registered structure with one parameter and one field permits a compact test:
eta-expand its constructor function and its resulting structure value, choosing a
fresh variable in both annotations, then compute through projection to a Pi.
The general theorem recovers a computational path below from this unscoped trace.
The arbitrary intermediate annotations are not asserted to be well typed.
-/
namespace Lean4Lean.VEnv.Strengthening.FieldObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions ProjectionCompute)
variable [Params]

def testPi : VExpr := .forallE (.sort .zero) (.sort .zero)
def testSource (s c : Name) : VExpr := .proj s 0 (mkApps (.const c []) [.sort .zero, testPi])
def testFunction (c : Name) : VExpr :=
  .lam (.bvar 0) (.app (VExpr.const c []).lift (.bvar 0))
def testIntermediate (s : Name) (info : VProjectionInfo) : VExpr :=
  .proj s 0 (structExpand s info [] [.bvar 0]
    (mkApps (testFunction info.ctorName) [.sort .zero, testPi]))

/-- Both kinds of eta occur before a computational head exposure, and both
expansion annotations deliberately mention the newly inserted variable. -/
theorem combined_eta_head_trace (hinfo : env.projections s info)
    (hp : info.nparams = 1) (hf : info.numFields = 1) :
    EtaCompute D (testSource s info.ctorName) (testIntermediate s info) ∧
      ProjectionCompute D (testIntermediate s info) testPi := by
  have he : EtaCompute D (testSource s info.ctorName)
      (.proj s 0 (mkApps (testFunction info.ctorName) [.sort .zero, testPi])) :=
    .proj (.app (.app .funEta (.compute (.base .refl))) (.compute (.base .refl)))
  refine ⟨he.trans (.proj (.structEta hinfo (by simpa using hp.symm))), ?_⟩
  have hcancel : ProjectionCompute D (testIntermediate s info)
      (.proj s 0 (mkApps (testFunction info.ctorName) [.sort .zero, testPi])) :=
    ProjectionCompute.cancel_struct hinfo (by simpa using hp.symm) (by omega)
  have hbeta : ProjectionCompute D (.app (testFunction info.ctorName) (.sort .zero))
      (.app (.const info.ctorName []) (.sort .zero)) := by
    apply ProjectionCompute.base
    simpa only [testFunction, inst, inst_lift, instVar_zero] using
      (PureObservation.Compute.beta (D := D) (A := .bvar 0)
        (b := .app (VExpr.const info.ctorName []).lift (.bvar 0)) (a := .sort .zero))
  have hfinal : ProjectionCompute D (testSource s info.ctorName) testPi :=
    .projIota (args := [.sort .zero, testPi]) (index := 0) hinfo
      (by simp [hp, hf]) (by simp [hp])
  exact hcancel.trans ((ProjectionCompute.proj (.app hbeta (.base .refl))).trans hfinal)

omit [Params] in
/-- The mixed intermediate is unscoped because its structure parameter is fresh. -/
theorem testIntermediate_not_scoped : ¬ (testIntermediate s info).Skips 1 0 := by
  intro H
  have Hm : (structExpand s info [] [.bvar 0]
      (mkApps (testFunction info.ctorName) [.sort .zero, testPi])).Skips 1 0 := by
    simpa only [testIntermediate, skips_iff, Skips'] using H
  have hbad := (skips_mkApps_iff.1 Hm).2 (.bvar 0) (by simp)
  simp [skips_iff, Skips'] at hbad

/-- The new mixed-path theorem reconstructs the head below despite both captured
annotations, using actual environment equations and their proved rigidity. -/
theorem combined_eta_exposure_below (hinfo : env.projections s info)
    (hp : info.nparams = 1) (hf : info.numFields = 1) :
    ∃ A B, ProjectionCompute (Definitions.ofEnv env univs henv)
      (testSource s info.ctorName) (.forallE A B) := by
  obtain ⟨R1, R2⟩ := combined_eta_head_trace (D := Definitions.ofEnv env univs henv) hinfo hp hf
  have R : EtaCompute (Definitions.ofEnv env univs henv)
      ((testSource s info.ctorName).lift' Lift.refl.skip) testPi := by
    simpa [testSource, testPi, mkApps, VExpr.lift'] using R1.trans (.compute R2)
  exact R.pi_exposure_below ConstructorRigid.ofEnv

/-- Even arbitrary untyped eta expansions cannot give a free variable a Pi head
through this computational fragment. -/
theorem variable_no_pi (hD : ConstructorRigid D) : ¬ EtaCompute D (.bvar i) (.forallE A B) := by
  intro R
  have H := R.obs_back hD (S := fun _ _ => False) .pi
  obtain ⟨_, h, _⟩ := H.var_inv
  exact h

end Lean4Lean.VEnv.Strengthening.FieldObservation
