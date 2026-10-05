import Lean4Lean.Theory.Typing.AnchoredOriginalNativeCanonicalSpine
import Lean4Lean.Theory.Typing.AnchoredOriginalNativeTerminalSponsorship

/-! The paired canonical native body runs under the actual finite replay's
proof insertion and right substitution. The original equation occurrence and
its exact domain ledger are retained across that target-only extension. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor
open private raised_lift_r from Lean4Lean.Theory.Typing.AnchoredNativeSupportedReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable def NativeCanonicalSpineResult.frame
    (result : NativeCanonicalSpineResult env U registry target declared plan captures newValues locals available)
    (context : ContextDerivation sourceEnv U declared) :
    OriginalRichFrame sourceEnv env U registry (plan.added (nativeCaptureSubst newValues) ++ target)
      context locals (raisedSubst captures plan.count) (plan.captures (nativeCaptureSubst newValues))
      (Valuation.rename (.skipN .refl plan.count) available) := by
  rw [result.locals_eq]
  exact result.spine.frame context

theorem NativeCanonicalSpineResult.frame_environment
    (result : NativeCanonicalSpineResult env U registry target declared plan captures newValues locals available)
    (context : ContextDerivation sourceEnv U declared) (ordered : sourceEnv.Ordered) :
    (result.frame context).dependencyEnvironment ordered = context.dependencyClosures ordered := by
  rcases result with ⟨insertion, raw, same, spine⟩
  cases same
  exact spine.frame_environment context ordered

theorem NativeCanonicalSpineResult.frame_ambient
    (result : NativeCanonicalSpineResult env U registry target declared plan captures newValues locals available)
    (context : ContextDerivation sourceEnv U declared) (below : sourceEnv ≤ env) :
    (result.frame context).Ambient := by
  rcases result with ⟨insertion, raw, same, spine⟩
  cases same
  exact spine.frame_ambient context below

noncomputable def NativeCanonicalSpineResult.occurrence
    (result : NativeCanonicalSpineResult env U registry target declared plan captures newValues locals available)
    {root : EndpointRef sourceEnv U [] rootExpression rootType}
    {node : EndpointState sourceEnv U declared expression assigned}
    (location : Located root node) (ordered : sourceEnv.Ordered) :
    OriginalRichOccurrenceFrame location .nil env registry
      (plan.added (nativeCaptureSubst newValues) ++ target) locals
      (raisedSubst captures plan.count) (plan.captures (nativeCaptureSubst newValues))
      (Valuation.rename (.skipN .refl plan.count) available) ordered [] := by
  refine ⟨result.frame (location.contextDerivation .nil), result.substitutions, ?_⟩
  rw [result.frame_environment, location.contextDerivation_dependencyClosures]
  exact Nat.le_refl _

noncomputable def NativeCanonicalSpineResult.bodyQuery
    (henv : env.Ordered)
    (result : NativeCanonicalSpineResult env U registry target declared plan captures newValues locals available)
    {node : EndpointState sourceEnv U declared expression assigned}
    (body : Obs env U registry target locals captures expression profile footprint) :
    RichObs sourceEnv env U registry (plan.added (nativeCaptureSubst newValues) ++ target)
      node locals (raisedSubst captures plan.count)
      (profile.rename (.skipN .refl plan.count)) (Footprint.rename (.skipN .refl plan.count) footprint) := by
  have observation := body.future henv result.insertion.toFuture
  rw [raised_lift_r] at observation
  exact .legacy (.legacy observation)

/-- Both raw substitution directions, the exact queried body, and the whole
finite renamed resource table agree at the retained original occurrence. -/
theorem NativeCanonicalSpineResult.bodyQuery_resources
    (henv : env.Ordered)
    (result : NativeCanonicalSpineResult env U registry target declared plan captures newValues locals available)
    (resources : footprint.Available available) :
    (Footprint.rename (.skipN .refl plan.count) footprint).Available
      (Valuation.rename (.skipN .refl plan.count) available) := resources.rename _

theorem NativeCanonicalSpineResult.occurrence_cost_le
    (result : NativeCanonicalSpineResult env U registry target declared plan captures newValues locals available)
    {root : EndpointRef sourceEnv U [] rootExpression rootType}
    {node : EndpointState sourceEnv U declared expression assigned}
    (location : Located root node) (ordered : sourceEnv.Ordered) :
    (Closure.close (node.dependencyOrigin ordered)
      ((result.occurrence location ordered).frame.dependencyEnvironment ordered)).cost ≤
      (Closure.close (root.dependencyOrigin ordered) []).cost :=
  (result.occurrence location ordered).cost_le

noncomputable def NativeCanonicalSpineResult.site
    {strata : EquationStratification env}
    (result : NativeCanonicalSpineResult env U registry target declared plan captures newValues locals available)
    {root : EndpointRef sourceEnv U [] rootExpression rootType}
    {node : EndpointState sourceEnv U declared expression assigned}
    (location : Located root node) (controls : OriginalWorldControls strata sourceEnv) :
    WorldQuerySite (registry := registry)
      (target := plan.added (nativeCaptureSubst newValues) ++ target)
      strata node locals (raisedSubst captures plan.count) := by
  have exactEnvironment : (result.occurrence location controls.ordered).frame.dependencyEnvironment
      controls.ordered = location.dependencyEnvironment controls.ordered [] := by
    rw [NativeCanonicalSpineResult.occurrence, result.frame_environment,
      location.contextDerivation_dependencyClosures]
    rfl
  exact (result.occurrence location controls.ordered).worldSite controls
    (exactEnvironment.symm ▸ WorldEnvironmentProvenance.located controls location .nil)

theorem NativeCanonicalSpineResult.site_ready
    {strata : EquationStratification env}
    (result : NativeCanonicalSpineResult env U registry target declared plan captures newValues locals available)
    {root : EndpointRef sourceEnv U [] rootExpression rootType}
    {node : EndpointState sourceEnv U declared expression assigned}
    (location : Located root node) (controls : OriginalWorldControls strata sourceEnv)
    (henv : env.Ordered) (below : sourceEnv ≤ env) (closed : available.AtomClosed)
    (body : Obs env U registry target locals captures expression profile footprint)
    (resources : footprint.Available available) :
    (result.site location controls).Ready (result.bodyQuery henv body) :=
  ⟨below, result.frame_ambient _ below, result.substitutions, closed.rename _, resources.rename _⟩

private theorem transported_worlds (equal : first = second)
    (environment : WorldEnvironmentProvenance strata U first) :
    (equal ▸ environment : WorldEnvironmentProvenance strata U second).worlds = environment.worlds := by
  cases equal
  rfl

theorem NativeCanonicalSpineResult.site_worlds
    {strata : EquationStratification env}
    (result : NativeCanonicalSpineResult env U registry target declared plan captures newValues locals available)
    {root : EndpointRef sourceEnv U [] rootExpression rootType}
    {node : EndpointState sourceEnv U declared expression assigned}
    (location : Located root node) (controls : OriginalWorldControls strata sourceEnv) :
    (result.site location controls).worlds =
      [originalCallWorld controls .fundamental node (WorldEnvironmentProvenance.located controls location .nil)] := by
  simp only [NativeCanonicalSpineResult.site, OriginalRichOccurrenceFrame.worldSite,
    WorldQuerySite.worlds, WorldClosureProvenance.worlds, transported_worlds,
    NativeCanonicalSpineResult.occurrence, NativeCanonicalSpineResult.frame_environment,
    location.contextDerivation_dependencyClosures, ContextDerivation.dependencyClosures,
    originalCallWorld]

/-- The private proof extension retains the original closed-equation sponsor.
The empty telescope uses coverage equality, not a fictitious strict body edge. -/
theorem NativeCanonicalSpineResult.site_sponsored
    {strata : EquationStratification env}
    (result : NativeCanonicalSpineResult env U registry target declared plan captures newValues locals available)
    {root : EndpointRef sourceEnv U [] rootExpression rootType}
    {node : EndpointState sourceEnv U declared expression assigned}
    (location : Located root node) (controls : OriginalWorldControls strata sourceEnv)
    {frontier : List (EquationWorldClosureOrder.World strata.rules.length)}
    (sponsored : EquationWorldClosureOrder.Sponsored frontier
      [originalCallWorld controls .fundamental (.ref root) .nil]) :
    EquationWorldClosureOrder.Sponsored frontier
      ((result.site location controls).worlds ++ (result.site location controls).annotation.environment.worlds) := by
  obtain ⟨sponsor, member, smaller⟩ := sponsored _ (List.mem_singleton_self _)
  apply EquationWorldClosureOrder.Sponsored.merge
  · rw [result.site_worlds]
    intro world belongs
    obtain ⟨old, oldMember, same | next⟩ :=
      WorldEnvironmentProvenance.located_call_covered controls location .nil world belongs
    · have oldEq := List.mem_singleton.mp oldMember
      subst old
      subst world
      exact ⟨sponsor, member, smaller⟩
    · have oldEq := List.mem_singleton.mp oldMember
      subst old
      exact ⟨sponsor, member, EquationWorldClosureOrder.trans
        (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans next smaller⟩
  · change EquationWorldClosureOrder.Sponsored frontier (_ : WorldEnvironmentProvenance strata U _).worlds
    simp only [NativeCanonicalSpineResult.site, OriginalRichOccurrenceFrame.worldSite, transported_worlds]
    intro world belongs
    exact ⟨sponsor, member, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans
      (WorldEnvironmentProvenance.located_captures_below controls location .nil world belongs) smaller⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
