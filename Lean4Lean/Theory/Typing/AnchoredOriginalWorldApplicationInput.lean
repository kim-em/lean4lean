import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryOperations
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPackingData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldUnaryDiagonal
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldParameterReply

/-! The original assembled application Pi supplies its semantic input through
one strictly smaller original formation call. The requested certificate and
selected source frame retain their existing world annotations. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private worldCode singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

structure GeneratedApplicationPackedRequest.Controlled
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length))
    (packed : GeneratedApplicationPackedRequest domain body argument hu hv env registry target locals σ available relevant profile) where
  request : ControlledStoredQuery controls frontier (.certificate packed.request.certificate)
  argument : ControlledStoredQuery controls frontier (.observation packed.argumentQuery.observation)
  domain : ControlledStoredQuery controls frontier (.certificate packed.domainCertificate)

 theorem OriginalApplicationTypeRouteSide.piRequestReplyWorld
    (side : OriginalApplicationTypeRouteSide U common)
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    (controls : OriginalWorldControls strata side.sourceEnv)
    (frame : OriginalCaptureRealization side.graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base commonCaps commonLeft commonRight side.graph frame.frame.raw controls)
    (replayable : generated.Replayable)
    (frontier : List (World strata.rules.length))
    (frameReady : generated.Controlled frontier)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : generated.Hereditary frontier)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (request : GeneratedApplicationPiRequest side.domain side.body side.hu side.hv
      env registry target locals (side.raw.comp commonLeft) available side.a relevant (profile : Profile n))
    (requestReady : ControlledStoredQuery controls frontier (.certificate request.certificate))
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental side.node baseline])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental side.node baseline])) :
    ∃ answer : AmbientBoundedParameterReply base commonCaps
      ((VExpr.forallE side.A side.B).subst (side.raw.comp commonLeft)) side.pi.display commonLeft commonRight
      (Profile.pi (side.A.subst (side.raw.comp commonLeft)) (side.B.subst (side.raw.comp commonLeft).lift)
        request.support [(request.key, raiseProfile request.rank request.bound profile)])
      (environmentCost baselineEnvironment),
      Nonempty (WorldParameterReplyData (P := P) controls baseline frontier answer) := by
  obtain ⟨frameData⟩ := WorldUnaryFrameData.ofGenerated frame.frame generated frameReady replayable compatible hereditary
  let diagonal := frame.frame.leftDiagonal
  let captured := frame.frame.diagonalWorld controls generated.environment
  have selectedCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      captured.worlds baseline.worlds := by
    simpa only [captured, OriginalRichFrame.diagonalWorld_worlds, WorldGenerated.worlds] using covered
  have smaller : (Closure.close
      ((EndpointState.pi side.hu side.hv (.ref side.domain) side.body).dependencyOrigin controls.ordered)
      (diagonal.dependencyEnvironment controls.ordered)).cost <
      (Closure.close (side.node.dependencyOrigin controls.ordered) baselineEnvironment).cost := by
    rw [show diagonal.dependencyEnvironment controls.ordered = frame.frame.dependencyEnvironment controls.ordered from
      frame.frame.dependencyEnvironment_leftDiagonal controls.ordered]
    exact Nat.lt_of_lt_of_le
      (EndpointState.appPiFormation_dependency_cost_lt controls.ordered side.hu side.hv (.ref side.domain)
        side.body side.function side.argument side.result _)
      (Nat.mul_le_mul_left _ (Nat.add_le_add_left capacity 1))
  have child : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental (.pi side.hu side.hv (.ref side.domain) side.body) captured)
      (originalCallWorld controls .fundamental side.node baseline) :=
    smaller_root (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans
      (EquationControlMeasure.scheduleDecrease (richSchedule_strict smaller _ _) _ _ _ _) selectedCovered
  have funded : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental (.pi side.hu side.hv (.ref side.domain) side.body) captured])
      (frontier ++ [originalCallWorld controls .fundamental side.node baseline]) := by
    have lower := split_call (calls := [originalCallWorld controls .fundamental
      (.pi side.hu side.hv (.ref side.domain) side.body) captured])
      (fun node member => by cases List.mem_singleton.mp member; exact child)
    clear bank frameReady requestReady sponsored frameData hereditary
    induction frontier with
    | nil => exact lower
    | cons world rest ih => exact ih.cons world
  obtain ⟨meaning, _⟩ := worldCode controls diagonal captured frontier _ bank funded
    (singletonSponsoredBelow sponsored child) (.ofLocation (.appPiFormation side.location) side.initial)
    frameData.leftDiagonal henv hscoped closed formed frame.substitutions.left
    request.certificate request.resources requestReady
  let answer : AmbientBoundedParameterReply base commonCaps
      ((VExpr.forallE side.A side.B).subst (side.raw.comp commonLeft)) side.pi.display commonLeft commonRight
      (Profile.pi (side.A.subst (side.raw.comp commonLeft)) (side.B.subst (side.raw.comp commonLeft).lift)
        request.support [(request.key, raiseProfile request.rank request.bound profile)])
      (environmentCost baselineEnvironment) := {
    reply := {
      answer := {
        reply := {
          locals := locals, available := available, realization := frame
          generated := generated.erase.capped.generated
          query := {
            rank := request.rank + 1, bound := Nat.le_refl _, raw := _
            footprint := request.footprint, observation := .code request.certificate
            adapter := by rw [raiseProfile_self]; exact .refl _
            resources := request.resources
            live := Profile.HasType.sortable_live request.certificate.formed }
          closed := closed }
        capped := generated.erase.capped }
      bounded := fun _ => capacity }
    related := by
      simpa only [OriginalApplicationTypeRouteSide.pi, OriginalPiTypeRouteSide.display,
        OriginalNestedDisplay.ofOccurrence, subst_subst] using meaning.related
    path := by
      simp only [OriginalApplicationTypeRouteSide.pi, subst_subst]
      exact .refl
    generation := generated.erase.ambientGenerated }
  exact ⟨answer, ⟨⟨generated, replayable, frameReady, compatible, requestReady.code, covered, hereditary⟩⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
