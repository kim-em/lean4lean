import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiReplayData
import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedApplicationInput
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedParameterEquality
import Lean4Lean.Theory.Typing.AnchoredNativeSeededRegistered

/-! Start whole-Pi history replay with the actual application query. The
semantic premise is discharged by the retained Pi formation below the
original application, at the same original frame and resource table. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private lower_raised from Lean4Lean.Theory.Typing.AnchoredNativeSeededRegistered
set_option backward.isDefEq.respectTransparency false

theorem OriginalApplicationTypeRouteSide.piRequestReply
    (side : OriginalApplicationTypeRouteSide U common)
    {base : OriginalCaptureBase env U registry target}
    (frame : OriginalCaptureRealization side.graph env registry target locals commonLeft commonRight available)
    (capped : CappedCaptureGenerated base commonCaps commonLeft commonRight side.graph frame.frame.raw)
    (ordered : side.sourceEnv.Ordered)
    (frameBound : environmentCost (frame.frame.dependencyEnvironment ordered) ≤ capacity)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (request : GeneratedApplicationPiRequest side.domain side.body side.hu side.hv
      env registry target locals (side.raw.comp commonLeft) available side.a true (profile : Profile n))
    (piF : OriginalCodeInductionAt env registry ordered side.initial (.appPiFormation side.location)
      ((side.node.dependencyOrigin ordered).weight * (1 + capacity))) :
    Nonempty (BoundedParameterReply base commonCaps
      ((VExpr.forallE side.A side.B).subst (side.raw.comp commonLeft)) side.pi.display commonLeft commonRight
      (Profile.pi (side.A.subst (side.raw.comp commonLeft)) (side.B.subst (side.raw.comp commonLeft).lift)
        request.support [(request.key, raiseProfile request.rank request.bound profile)])
      capacity) := by
  have smaller : (Closure.close
      ((EndpointState.pi side.hu side.hv (.ref side.domain) side.body).dependencyOrigin ordered)
      (frame.frame.leftDiagonal.dependencyEnvironment ordered)).cost <
      (side.node.dependencyOrigin ordered).weight * (1 + capacity) := by
    rw [OriginalRichFrame.dependencyEnvironment_leftDiagonal]
    exact Nat.lt_of_lt_of_le
      (EndpointState.appPiFormation_dependency_cost_lt ordered side.hu side.hv (.ref side.domain)
        side.body side.function side.argument side.result _)
      (Nat.mul_le_mul_left _ (Nat.add_le_add_left frameBound 1))
  obtain ⟨meaning⟩ := piF target locals (side.raw.comp commonLeft) (side.raw.comp commonLeft) available
    frame.frame.leftDiagonal smaller closed formed frame.substitutions.left request.certificate request.resources
  refine ⟨{
    reply := {
      answer := {
        reply := {
          locals := locals, available := available, realization := frame
          generated := capped.generated
          query := {
            rank := request.rank + 1, bound := Nat.le_refl _, raw := _
            footprint := request.footprint, observation := .code request.certificate
            adapter := by rw [raiseProfile_self]; exact .refl _
            resources := request.resources
            live := Profile.HasType.sortable_live request.certificate.formed }
          closed := closed }
        capped := capped }
      bounded := fun _ => frameBound }
    related := ?_
    path := ?_ }⟩
  · simpa only [OriginalApplicationTypeRouteSide.pi, OriginalPiTypeRouteSide.display,
      OriginalNestedDisplay.ofOccurrence, subst_subst] using meaning.related
  · simp only [OriginalApplicationTypeRouteSide.pi, subst_subst]
    exact .refl


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
