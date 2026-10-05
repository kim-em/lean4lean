import Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiDisplays
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrameFuture

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private empty_guard from Lean4Lean.Theory.Typing.AnchoredOriginalPiFrames
set_option backward.isDefEq.respectTransparency false

private def castCommon
    {display : EndpointDisplay sourceEnv U displayed expression assigned}
    (equal : common = other)
    (frame : OriginalRichDisplayFrame env registry target display common locals available) :
    OriginalRichDisplayFrame env registry target display other locals available := equal ▸ frame

private theorem castCommon_environment
    {display : EndpointDisplay sourceEnv U displayed expression assigned}
    (equal : common = other)
    (frame : OriginalRichDisplayFrame env registry target display common locals available)
    (ordered : sourceEnv.Ordered) :
    (castCommon equal frame).frame.dependencyEnvironment ordered = frame.frame.dependencyEnvironment ordered := by
  cases equal; rfl

noncomputable def OriginalRichDisplayFrame.piNeutral
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (location : Located root (.pi hu hv (.ref domain) body))
    (initial : ContextDerivation sourceEnv U rootSource)
    (insertion : Ctx.Lift' map source displayed)
    (annotationEq : annotation = A.lift' map)
    (bodyEq : displayedBody = B.lift' map.cons)
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (annotationType : env.IsType U target (annotation.subst common))
    (frame : OriginalRichDisplayFrame env registry target
      (location.piDisplayAs initial insertion annotationEq bodyEq) common locals available) :
    OriginalRichDisplayFrame env registry (annotation.subst common :: target)
      (location.piBodyDisplayAs initial insertion annotationEq bodyEq) common.lift
      (Locals.push locals) (Valuation.push [] (available.rename (.skip .refl))) := by
  let future : FutureInsertion env U target (annotation.subst common :: target) (.skip .refl) :=
    .skip (.refl formed) (Classical.choose_spec annotationType)
  have annotationRealized : A.subst (Subst.lift_l map common) = annotation.subst common := by
    rw [annotationEq, subst_lift']
  have domainEq : A.subst (Subst.lift_l map (common.lift_r (.skip .refl))) =
      (annotation.subst common).lift := by
    change A.subst ((Subst.lift_l map common).lift_r (.skip .refl)) = _
    rw [← lift'_subst, annotationRealized, ← lift_eq_lift']
  have typedNeutral : env.HasType U (annotation.subst common :: target) (.bvar 0)
      (A.subst (Subst.lift_l map (common.lift_r (.skip .refl)))) := by
    rw [domainEq]
    exact .bvar .zero
  let side : OriginalPiSide root initial env registry (annotation.subst common :: target)
      (location.contextDerivation initial) domain locals
      (Subst.lift_l map (common.lift_r (.skip .refl))) (available.rename (.skip .refl))
      (.empty : Profile 0) := {
    frame := frame.frame.future henv future
    location := .piDomain location
    lineage := rfl
    footprint := []
    code := .legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort true)))
    resources := fun _ _ member => nomatch member }
  have commonLift : common.lift = (common.lift_r (.skip .refl)).cons (.bvar 0) := by
    funext index; cases index <;> simp only [Subst.lift, Subst.cons, Subst.lift_r, lift_eq_lift']
  exact castCommon commonLift.symm (side.displayBodyFits henv below location initial rfl insertion annotationEq bodyEq
    (frame.substitutions.future henv future) (empty_guard typedNeutral) []
    (fun _ member => nomatch member) (fun _ member => nomatch member))

theorem OriginalRichDisplayFrame.piNeutral_environment
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (location : Located root (.pi hu hv (.ref domain) body))
    (initial : ContextDerivation sourceEnv U rootSource)
    (insertion : Ctx.Lift' map source displayed)
    (annotationEq : annotation = A.lift' map)
    (bodyEq : displayedBody = B.lift' map.cons)
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (annotationType : env.IsType U target (annotation.subst common))
    (frame : OriginalRichDisplayFrame env registry target
      (location.piDisplayAs initial insertion annotationEq bodyEq) common locals available) (ordered : sourceEnv.Ordered) :
    (frame.piNeutral location initial insertion annotationEq bodyEq henv below formed annotationType).frame.dependencyEnvironment ordered =
      Closure.close (domain.dependencyOrigin ordered) (frame.frame.dependencyEnvironment ordered) ::
        frame.frame.dependencyEnvironment ordered := by
  unfold OriginalRichDisplayFrame.piNeutral
  rw [castCommon_environment]
  dsimp only [OriginalPiSide.displayBodyFits]
  rw [OriginalPiSide.displayBodyFrame_environment]
  change Closure.close (domain.dependencyOrigin ordered)
    ((frame.frame.future henv _).dependencyEnvironment ordered) ::
    (frame.frame.future henv _).dependencyEnvironment ordered = _
  rw [OriginalRichFrame.dependencyEnvironment_future]

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
