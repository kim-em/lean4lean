import Lean4Lean.Theory.Typing.AnchoredOriginalLowerCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalEqualityGradedReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalRichReferenceExposure
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedBaseFreeze
import Lean4Lean.Theory.Typing.AnchoredOriginalDependencySchedules
import Lean4Lean.Theory.Typing.AnchoredTransitivity

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private lower_raised from Lean4Lean.Theory.Typing.AnchoredFamilyArgumentGrades
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
set_option Elab.async false

private theorem directionOrigin
    (ordered : sourceEnv.Ordered)
    (original : Derivation sourceEnv U source A B assigned) (forward : Bool) :
    (originalTypeRouteSide original forward).dependencyOrigin ordered = original.dependencyOrigin ordered := by
  cases forward <;> rfl

/-- Directional adaptation never constructs a symmetry derivation. The
requested support is retained from the original unary F answer. -/
noncomputable def OriginalDirectionalEqualityResult.adaptGraded
    {original : Derivation sourceEnv U source A B assigned}
    {forward : Bool}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {requested support : Profile n}
    (typed : requested.HasType support)
    (code : TypeRelated env U registry target (assigned.subst σ) (assigned.subst σ) support)
    (input : RichGradedResult sourceEnv env U registry target (.ref (originalTypeRouteSide original forward))
      locals σ available requested)
    (answer : OriginalDirectionalEqualityResult original forward env registry target locals σ τ available input.raw) :
    OriginalDirectionalEqualityResult original forward env registry target locals σ τ available requested where
  support := support
  related := by
    have adapted := input.adapter.termMap henv hscoped formed (Profile.HasType.raise input.bound typed)
      (code.raise henv input.bound) answer.related
    simpa only [lower_raised] using Related.lower henv input.bound formed adapted
  rightQuery := answer.rightQuery.adaptRequest henv hscoped formed input.bound input.adapter

/-- Two actual retained equality children compose through their original
middle occurrences. Source reconstruction uses precisely the reserved pair,
then freezes its chosen identity-frame reply back to the caller's resources. -/
private theorem composeDirections
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {A B C D assigned : VExpr}
    (first : Derivation sourceEnv U source A B assigned)
    (second : Derivation sourceEnv U source C D assigned)
    (forward backward : Bool)
    (same : (if !forward then A else B) = (if backward then C else D))
    (henv : env.Ordered) (hscoped : registry.Scoped) (ordered : sourceEnv.Ordered)
    (context : ContextDerivation sourceEnv U source)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (ambient : frame.Ambient) (closed : available.AtomClosed)
    (formed : OnCtx target (env.IsType U)) (substitutions : Ctx.SubstEq env U target σ σ source)
    (bank : OriginalLowerCallBank env U registry limit)
    (firstScheduled : richSchedule .fundamental
      (Closure.close (first.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost < limit)
    (secondScheduled : richSchedule .fundamental
      (Closure.close (second.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost < limit)
    (pairScheduled : richSchedule .expressionReindex
      ((Closure.close (first.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost +
       (Closure.close (second.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost) < limit)
    {n : Nat} {profile : Profile n} {footprint : Footprint}
    (query : RichObs sourceEnv env U registry target (.ref (originalTypeRouteSide first forward))
      locals σ profile footprint) (resources : footprint.Available available) :
    ∃ support, Related env U registry target ((if forward then A else B).subst σ)
      ((if !backward then C else D).subst σ) (assigned.subst σ) profile support ∧
      Nonempty (RichGradedResult sourceEnv env U registry target (.ref (originalTypeRouteSide second (!backward)))
        locals σ available profile) := by
  obtain ⟨support⟩ := bank.computational ordered ambient.below context
    (.here (root := originalTypeRouteSide first forward)) target locals σ σ available frame ambient
    (by simpa only [EndpointState.dependencyOrigin, directionOrigin] using firstScheduled)
    closed formed substitutions query resources
  obtain ⟨leftAnswer⟩ := bank.equality ordered ambient.below context first forward target locals σ available frame
    ambient firstScheduled closed formed substitutions query resources
  let base := frame.captureBase substitutions
  let leftDisplay := OriginalNestedDisplay.identity base (.ref (originalTypeRouteSide first (!forward)))
    (.ofLocation .here context)
  let rightDisplay := OriginalNestedDisplay.identity base (.ref (originalTypeRouteSide second backward))
    (.ofLocation .here context)
  let castLeft : OriginalNestedDisplay U source (if backward then C else D) assigned :=
    { leftDisplay with expression_eq := same.symm.trans leftDisplay.expression_eq }
  let leftRealization : OriginalCaptureRealization castLeft.graph env registry target locals σ σ available := base.identityRealization
  have leftGenerated : AmbientCaptureGenerated base base.initialCaps σ σ castLeft.graph leftRealization.frame.raw := .identity ambient
  have leftQuery : RichObs castLeft.sourceEnv env U registry target castLeft.node locals
      (castLeft.raw.comp σ) leftAnswer.rightQuery.raw leftAnswer.rightQuery.footprint := leftAnswer.rightQuery.observation
  have leftResources : leftAnswer.rightQuery.footprint.Available available := leftAnswer.rightQuery.resources
  have actualPair : richSchedule .expressionReindex
      ((Closure.close (castLeft.node.dependencyOrigin ordered)
          (leftRealization.frame.dependencyEnvironment ordered)).cost +
        (Closure.close (rightDisplay.node.dependencyOrigin ordered)
          (base.identityRealization.frame.dependencyEnvironment ordered)).cost) < limit := by
    simpa only [castLeft, leftDisplay, rightDisplay, OriginalNestedDisplay.identity,
      EndpointState.dependencyOrigin, directionOrigin, leftRealization, base, OriginalCaptureBase.identityRealization,
      OriginalRichFrame.captureBase] using pairScheduled
  obtain ⟨middle⟩ := bank.observation base base.initialCaps castLeft rightDisplay σ σ
    ordered ordered leftRealization leftGenerated closed
    base.identityRealization (.identity ambient) closed actualPair leftQuery leftResources
  let input := middle.answer.freezeBase
  obtain ⟨rightAnswer⟩ := bank.equality ordered ambient.below context second backward target locals σ available frame
    ambient secondScheduled closed formed substitutions input.observation input.resources
  let combined := input.adaptRequest henv hscoped formed leftAnswer.rightQuery.bound leftAnswer.rightQuery.adapter
  let adapted := rightAnswer.adaptGraded henv hscoped formed support.typed support.typeCode combined
  exact ⟨_, leftAnswer.related.trans henv hscoped (by simpa only [same] using adapted.related),
    ⟨adapted.rightQuery⟩⟩


def RichGradedResult.changeReference
    {first second : EndpointRef sourceEnv U source expression assigned}
    (same : first.expose = second.expose)
    (query : RichGradedResult sourceEnv env U registry target (.ref first) locals σ available profile) :
    RichGradedResult sourceEnv env U registry target (.ref second) locals σ available profile :=
  { query with observation := query.observation.changeReference same }

/-- Transitivity dispatch in either direction uses the two retained original
children and their strictly smaller middle R pair. All queries are frozen to
the same ambient caller frame; no symmetry derivation is manufactured. -/
theorem OriginalDirectionalEqualityResult.trans
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {A B C assigned : VExpr}
    (first : Derivation sourceEnv U source A B assigned)
    (second : Derivation sourceEnv U source B C assigned) (forward : Bool)
    (henv : env.Ordered) (hscoped : registry.Scoped) (ordered : sourceEnv.Ordered)
    (context : ContextDerivation sourceEnv U source)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (ambient : frame.Ambient) (closed : available.AtomClosed)
    (formed : OnCtx target (env.IsType U)) (substitutions : Ctx.SubstEq env U target σ σ source)
    (bank : OriginalLowerCallBank env U registry
      (richSchedule .fundamental (Closure.close ((Derivation.trans first second).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost))
    {n : Nat} {profile : Profile n} {footprint : Footprint}
    (query : RichObs sourceEnv env U registry target
      (.ref (originalTypeRouteSide (Derivation.trans first second) forward)) locals σ profile footprint)
    (resources : footprint.Available available) :
    Nonempty (OriginalDirectionalEqualityResult (Derivation.trans first second) forward
      env registry target locals σ σ available profile) := by
  have decrease :
      (Closure.close (first.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost +
        (Closure.close (second.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost <
      (Closure.close ((Derivation.trans first second).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost := by
    have scheduled := Derivation.trans_dependency_comparison_schedule ordered first second (frame.dependencyEnvironment ordered)
    simp only [schedule, Phase.code] at scheduled
    omega
  have firstBound := richSchedule_strict (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) decrease)
    RichPhase.fundamental RichPhase.fundamental
  have secondBound := richSchedule_strict (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) decrease)
    RichPhase.fundamental RichPhase.fundamental
  have pairBound := richSchedule_strict decrease RichPhase.expressionReindex RichPhase.fundamental
  cases forward with
  | true =>
    have source : RichObs sourceEnv env U registry target (.ref (.left first)) locals σ profile footprint :=
      query.changeReference (first := .left (.trans first second)) (second := .left first) rfl
    obtain ⟨support, related, ⟨result⟩⟩ := composeDirections first second true true rfl
      henv hscoped ordered context frame ambient closed formed substitutions bank
      firstBound secondBound pairBound source resources
    exact ⟨{ support := support, related := related, rightQuery := result.changeReference (first := .right second) (second := .right (.trans first second)) rfl }⟩
  | false =>
    have source : RichObs sourceEnv env U registry target (.ref (.right second)) locals σ profile footprint :=
      query.changeReference (first := .right (.trans first second)) (second := .right second) rfl
    obtain ⟨support, related, ⟨result⟩⟩ := composeDirections second first false false rfl
      henv hscoped ordered context frame ambient closed formed substitutions bank
      secondBound firstBound (by simpa only [Nat.add_comm] using pairBound) source resources
    exact ⟨{ support := support, related := related, rightQuery := result.changeReference (first := .left first) (second := .left (.trans first second)) rfl }⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
