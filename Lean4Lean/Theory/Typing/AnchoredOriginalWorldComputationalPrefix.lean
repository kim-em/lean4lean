import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidConstantStep
import Lean4Lean.Theory.Typing.AnchoredOriginalRichComputationalPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalLocatedDirect

/-! Restore the exact computational answer along a real original prefix.
Formation reindexing uses the caller's identity sandbox, and conversions use
only their retained equality children. Every returned certificate keeps its
actual annotation when it is frozen back to the original resource table. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private prefixCalls from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidConstantStep
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

private theorem prefixCertificateR
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    (left : EndpointState sourceEnv U source A (.sort u))
    (right : EndpointState sourceEnv U source A (.sort v))
    (leftProvenance : EndpointProvenance context left)
    (rightProvenance : EndpointProvenance context right)
    (caller : EndpointState sourceEnv U source expression assigned)
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds)
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (_formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (henv : env.Ordered) (_hscoped : registry.Scoped)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
    (leftLess : (Closure.close (left.dependencyOrigin controls.ordered) baselineEnvironment).cost <
      (Closure.close (caller.dependencyOrigin controls.ordered) baselineEnvironment).cost)
    (rightLess : (Closure.close (right.dependencyOrigin controls.ordered) baselineEnvironment).cost <
      (Closure.close (caller.dependencyOrigin controls.ordered) baselineEnvironment).cost)
    (certificate : RichCert sourceEnv env U registry target left locals σ relevant profile footprint)
    (resources : footprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ∃ outputFootprint, ∃ output : RichCert sourceEnv env U registry target right locals σ relevant profile outputFootprint,
      outputFootprint.Available available ∧
      Nonempty (ControlledStoredQuery controls frontier (.certificate output)) := by
  let diagonal := frame.leftDiagonal
  let diagonalData := data.leftDiagonal
  let sandbox := diagonal.captureBase substitutions.left
  let identity := diagonalData.generation substitutions.left
  obtain ⟨identityReady⟩ := diagonalData.controlled substitutions.left
  let leftDisplay := OriginalNestedDisplay.identity sandbox left leftProvenance
  let rightDisplay := OriginalNestedDisplay.identity sandbox right rightProvenance
  have capacity' : environmentCost (diagonal.dependencyEnvironment controls.ordered) ≤
      environmentCost baselineEnvironment := by
    simpa only [diagonal, OriginalRichFrame.dependencyEnvironment_leftDiagonal] using capacity
  have covered' : Covered (@EquationControlMeasure.Less strata.rules.length) identity.worlds baseline.worlds := by
    simpa only [WorldGenerated.worlds, WorldGenerated.environment, identity,
      WorldUnaryFrameData.generation, OriginalRichFrame.diagonalWorld_worlds] using covered
  let leftData : WorldCallFrameData (P := P) (base := sandbox) (caps := sandbox.initialCaps)
      (display := leftDisplay) controls baseline frontier sandbox.identityRealization := {
    generation := identity, replayable := trivial, controlled := identityReady,
    compatible := ⟨rfl,rfl⟩, closed := closed, capacity := capacity', covered := covered',
    hereditary := diagonalData.generation_hereditary substitutions.left }
  let rightData : WorldCallFrameData (P := P) (base := sandbox) (caps := sandbox.initialCaps)
      (display := rightDisplay) controls baseline frontier sandbox.identityRealization := {
    generation := identity, replayable := trivial, controlled := identityReady,
    compatible := ⟨rfl,rfl⟩, closed := closed, capacity := capacity', covered := covered',
    hereditary := diagonalData.generation_hereditary substitutions.left }
  have leftBelow : WorldBelow strata.rules.length (originalCallWorld controls .expressionReindex left baseline)
      (originalCallWorld controls .fundamental caller baseline) :=
    original_child (richSchedule_strict leftLess _ _) _ _ _ _ _
  have rightBelow : WorldBelow strata.rules.length (originalCallWorld controls .expressionReindex right baseline)
      (originalCallWorld controls .fundamental caller baseline) :=
    original_child (richSchedule_strict rightLess _ _) _ _ _ _ _
  have lower : ∀ child ∈ [originalCallWorld controls .expressionReindex left baseline,
      originalCallWorld controls .expressionReindex right baseline],
      WorldBelow strata.rules.length child (originalCallWorld controls .fundamental caller baseline) := by
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact leftBelow
    · cases List.mem_singleton.mp member; exact rightBelow
  obtain ⟨answer, ⟨answerReady⟩⟩ := (bank _ (prefixCalls frontier lower)).observation
    sandbox sandbox.initialCaps leftDisplay rightDisplay σ σ controls controls rfl rfl
    baseline baseline frontier rfl
    ((singletonSponsoredBelow paid leftBelow).merge (singletonSponsoredBelow paid rightBelow))
    sandbox.identityRealization leftData sandbox.identityRealization rightData
    (.code certificate) resources ready.code
  obtain ⟨frozenReady⟩ := answer.answer.freezeBase_controlled answerReady.query
  obtain ⟨fp, output, outputReady, outputResources, _⟩ :=
    answer.answer.freezeBase.code_controlled henv controls frozenReady certificate.formed
  exact ⟨fp, output, outputResources, ⟨outputReady⟩⟩

private theorem prefixCertificateEquality
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    (original : Derivation sourceEnv U source A B (.sort level)) (forward : Bool)
    (caller : EndpointState sourceEnv U source expression assigned)
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds)
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
    (less : (Closure.close (original.dependencyOrigin controls.ordered) baselineEnvironment).cost <
      (Closure.close (caller.dependencyOrigin controls.ordered) baselineEnvironment).cost)
    (certificate : RichCert sourceEnv env U registry target (.ref (originalTypeRouteSide original forward))
      locals σ relevant profile footprint)
    (resources : footprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ∃ answer : RichCodeTransferResult env U registry target (.ref (originalTypeRouteSide original forward))
        (.ref (originalTypeRouteSide original (!forward))) locals σ σ available relevant profile,
      Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)) := by
  let diagonal := frame.leftDiagonal
  let actual := frame.diagonalWorld controls captured
  have capacity' : environmentCost (diagonal.dependencyEnvironment controls.ordered) ≤
      environmentCost baselineEnvironment := by
    simpa only [diagonal, OriginalRichFrame.dependencyEnvironment_leftDiagonal] using capacity
  have covered' : Covered (@EquationControlMeasure.Less strata.rules.length) actual.worlds baseline.worlds := by
    simpa only [actual, OriginalRichFrame.diagonalWorld_worlds] using covered
  have lower : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental (.ref (originalTypeRouteSide original forward)) baseline)
      (originalCallWorld controls .fundamental caller baseline) := by
    cases forward <;> exact original_child (richSchedule_strict less _ _) _ _ _ _ _
  obtain ⟨answer, ⟨answerReady⟩⟩ := (bank _ (prefixCalls frontier
    (calls := [originalCallWorld controls .fundamental (.ref (originalTypeRouteSide original forward)) baseline])
    (by intro child member; cases List.mem_singleton.mp member; exact lower))).equality
      original forward (.ofLocation .here context) controls diagonal actual baseline frontier capacity' covered' rfl
      (singletonSponsoredBelow paid lower) data.leftDiagonal closed formed substitutions.left
      (.code certificate) resources ready.code
  obtain ⟨fp, output, outputReady, outputResources, _⟩ :=
    answer.rightQuery.code_controlled henv controls answerReady certificate.formed
  exact ⟨⟨fp, output, outputResources,
    answer.related.code_of_sortable henv hscoped formed certificate.formed⟩, ⟨outputReady⟩⟩

private noncomputable def prefixProvenance
    {context : ContextDerivation sourceEnv U source}
    {first : EndpointState sourceEnv U source expression A}
    {last : EndpointState sourceEnv U source expression B}
    (provenance : EndpointProvenance context first)
    (route : PrefixRoute sourceEnv U source expression first last) : EndpointProvenance context last :=
  { provenance with
    location := route.locate provenance.location,
    context_eq := provenance.context_eq.trans (route.locate_contextDerivation provenance.location provenance.initial).symm }

private noncomputable def formationProvenance
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source expression A}
    (provenance : EndpointProvenance context node) : EndpointProvenance context node.typeFormation.node :=
  { provenance with
    location := .assignedFormation provenance.location,
    context_eq := provenance.context_eq }

private noncomputable def formationCertificateCast
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {first last : TypeFormation sourceEnv U source assigned}
    (same : first = last)
    (certificate : RichCert sourceEnv env U registry target first.node locals σ relevant profile footprint)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ControlledStoredQuery controls frontier (.certificate
      (show RichCert sourceEnv env U registry target last.node locals σ relevant profile footprint
        from same ▸ certificate)) := by
  cases same
  exact ready

/-- Only original formation/equality children are interpreted. In particular,
a lazy reference with the same formation uses the exact existing certificate. -/
theorem _root_.Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.DirectPrefixRoute.restoreSupportedWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {first : EndpointState sourceEnv U source expression A}
    {last : EndpointState sourceEnv U source expression B}
    (route : DirectPrefixRoute sourceEnv U source expression first last)
    (caller : EndpointState sourceEnv U source callerExpression callerAssigned)
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds)
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
    (replay : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
    (provenance : EndpointProvenance context first)
    (bounded : (Closure.close (first.dependencyOrigin controls.ordered) baselineEnvironment).cost ≤
      (Closure.close (caller.dependencyOrigin controls.ordered) baselineEnvironment).cost)
    (answer : RichSupportedValue sourceEnv env U registry target last locals σ τ available profile)
    (ready : ControlledStoredQuery controls frontier (.certificate answer.certificate)) :
    ∃ output : RichSupportedValue sourceEnv env U registry target first locals σ τ available profile,
      Nonempty (ControlledStoredQuery controls frontier (.certificate output.certificate)) := by
  induction route with
  | done node => exact ⟨answer, ⟨ready⟩⟩
  | expose reference rest ih =>
    let step : PrefixRoute sourceEnv U source expression (.ref reference) reference.expose := .expose reference (.done _)
    let nextProvenance := prefixProvenance provenance step
    obtain ⟨tail, ⟨tailReady⟩⟩ := ih nextProvenance
      (Nat.le_trans (step.dependency_cost_le controls.ordered baselineEnvironment) bounded) answer ready
    rcases reference.exposure_formation_cost_reserve controls.ordered baselineEnvironment with same | smaller
    · let certificate : RichCert sourceEnv env U registry target reference.typeFormation.node locals σ true
          tail.support tail.footprint := same ▸ tail.certificate
      have certificateReady : ControlledStoredQuery controls frontier (.certificate certificate) := formationCertificateCast same tail.certificate tailReady
      exact ⟨{tail with certificate := certificate}, ⟨certificateReady⟩⟩
    · have leftLess := Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) smaller) bounded
      have rightLess := Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) smaller) bounded
      obtain ⟨fp, certificate, resources, ⟨certificateReady⟩⟩ := prefixCertificateR
        reference.expose.typeFormation.node reference.typeFormation.node
        (formationProvenance nextProvenance) (formationProvenance provenance)
        caller controls frame captured baseline frontier capacity covered data closed formed substitutions henv hscoped
        paid replay leftLess rightLess tail.certificate tail.resources tailReady
      exact ⟨{tail with footprint := fp, certificate := certificate, resources := resources}, ⟨certificateReady⟩⟩
  | forward wf original term rest ih =>
    let step : PrefixRoute sourceEnv U source expression (.convert (.forward wf original) term) term :=
      .convert (.forward wf original) term (.done _)
    let nextProvenance := prefixProvenance provenance step
    obtain ⟨tail, ⟨tailReady⟩⟩ := ih nextProvenance
      (Nat.le_trans (step.dependency_cost_le controls.ordered baselineEnvironment) bounded) answer ready
    have termLess : (Closure.close (term.dependencyOrigin controls.ordered) baselineEnvironment).cost <
        (Closure.close (caller.dependencyOrigin controls.ordered) baselineEnvironment).cost := by
      apply Nat.lt_of_lt_of_le _ bounded
      exact original_child_same_environment (Origin.rule_child (by simp [EndpointConversion.dependencyOrigin])) baselineEnvironment
    have equalityLess : (Closure.close (original.dependencyOrigin controls.ordered) baselineEnvironment).cost <
        (Closure.close (caller.dependencyOrigin controls.ordered) baselineEnvironment).cost := by
      apply Nat.lt_of_lt_of_le _ bounded
      exact original_child_same_environment (Origin.rule_child (by simp [EndpointConversion.dependencyOrigin])) baselineEnvironment
    obtain ⟨fp, certificate, resources, ⟨certificateReady⟩⟩ := prefixCertificateR
      term.typeFormation.node (.ref (.left original)) (formationProvenance nextProvenance) (.ofLocation .here context)
      caller controls frame captured baseline frontier capacity covered data closed formed substitutions henv hscoped
      paid replay (Nat.lt_of_le_of_lt (term.typeFormation_dependency_cost_le controls.ordered _) termLess)
      equalityLess tail.certificate tail.resources tailReady
    obtain ⟨changed, ⟨changedReady⟩⟩ := prefixCertificateEquality original true caller controls frame captured
      baseline frontier capacity covered data closed formed substitutions henv hscoped paid unary equalityLess
      certificate resources certificateReady
    exact ⟨{
      support := tail.support, footprint := changed.footprint, certificate := changed.certificate,
      resources := changed.resources, typed := tail.typed,
      related := Related.convert henv tail.typed changed.related tail.related,
      typeCode := (changed.related.symm henv tail.typed.wf_type).left_diagonal }, ⟨changedReady⟩⟩
  | backward wf original term rest ih =>
    let step : PrefixRoute sourceEnv U source expression (.convert (.backward wf original) term) term :=
      .convert (.backward wf original) term (.done _)
    let nextProvenance := prefixProvenance provenance step
    obtain ⟨tail, ⟨tailReady⟩⟩ := ih nextProvenance
      (Nat.le_trans (step.dependency_cost_le controls.ordered baselineEnvironment) bounded) answer ready
    have termLess : (Closure.close (term.dependencyOrigin controls.ordered) baselineEnvironment).cost <
        (Closure.close (caller.dependencyOrigin controls.ordered) baselineEnvironment).cost := by
      apply Nat.lt_of_lt_of_le _ bounded
      exact original_child_same_environment (Origin.rule_child (by simp [EndpointConversion.dependencyOrigin])) baselineEnvironment
    have equalityLess : (Closure.close (original.dependencyOrigin controls.ordered) baselineEnvironment).cost <
        (Closure.close (caller.dependencyOrigin controls.ordered) baselineEnvironment).cost := by
      apply Nat.lt_of_lt_of_le _ bounded
      exact original_child_same_environment (Origin.rule_child (by simp [EndpointConversion.dependencyOrigin])) baselineEnvironment
    obtain ⟨fp, certificate, resources, ⟨certificateReady⟩⟩ := prefixCertificateR
      term.typeFormation.node (.ref (.right original)) (formationProvenance nextProvenance) (.ofLocation .here context)
      caller controls frame captured baseline frontier capacity covered data closed formed substitutions henv hscoped
      paid replay (Nat.lt_of_le_of_lt (term.typeFormation_dependency_cost_le controls.ordered _) termLess)
      equalityLess tail.certificate tail.resources tailReady
    obtain ⟨changed, ⟨changedReady⟩⟩ := prefixCertificateEquality original false caller controls frame captured
      baseline frontier capacity covered data closed formed substitutions henv hscoped paid unary equalityLess
      certificate resources certificateReady
    exact ⟨{
      support := tail.support, footprint := changed.footprint, certificate := changed.certificate,
      resources := changed.resources, typed := tail.typed,
      related := Related.convert henv tail.typed changed.related tail.related,
      typeCode := (changed.related.symm henv tail.typed.wf_type).left_diagonal }, ⟨changedReady⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
