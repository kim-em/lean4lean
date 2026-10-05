import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFirstFormalParameterCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTemplateMajorBackwardInitialization

/-! The first formal capture starts at the actual selected major reply. Its
identity sandbox retains that reply's frame ancestry; no source history or
argument observation is an input. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

-- The suggestion index expands the dependent result telescope exponentially
-- during module export. Exclude this internal assembly theorem from automatic
-- premise suggestions; its statement and kernel checking are unchanged.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "captureFirstFormalWorld"

private theorem recontextFirstFrame
    {strata : EquationStratification env} {P : VEnv → Prop}
    {first second : ContextDerivation sourceEnv U source}
    (equal : first = second)
    (controls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length))
    (frame : OriginalRichFrame sourceEnv env U registry target first locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds) :
    ∃ next : OriginalRichFrame sourceEnv env U registry target second locals σ τ available,
      ∃ world : WorldEnvironmentProvenance strata U (next.dependencyEnvironment controls.ordered),
        HEq next frame ∧ HEq world captured ∧ Nonempty (WorldUnaryFrameData P controls frontier next world) ∧
        environmentCost (next.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment ∧
        Covered (@EquationControlMeasure.Less strata.rules.length) world.worlds baseline.worlds := by
  cases equal
  exact ⟨frame, captured, HEq.rfl, HEq.rfl, ⟨data⟩, capacity, covered⟩

section
variable
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {leftDisplay : OriginalNestedDisplay U common leftExpression leftAssigned}
    {rightNode : EndpointState rightEnv U rightSource (.proj name index rightValue) rightAssigned}
    (rightHead : ProjectionHead rightNode)
    {rightContext : ContextDerivation rightEnv U rightSource}
    (rightGraph : OriginalCaptureMap (common := common) rightContext rightRaw)
    (displayedEq : displayed = rightValue.subst rightRaw)
    (controls : OriginalWorldControls strata rightEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (answer : WorldTemplateAssignedReply (P := P) base caps leftDisplay
      (OriginalNestedDisplay.recordBridgeReference rightGraph (.right rightHead.major) displayedEq)
      commonLeft commonRight controls baseline frontier (profile : Profile n))
    (input : answer.FormationInput)
    (arguments : rightHead.parameters ++ rightHead.indices = [a, p])
    (bootstrap : WorldTemplateMajorBackwardInitialization input
      (congrArg (mkApps (.const name rightHead.levels)) arguments) rightHead.levelsWF)

/-- Actual original first-application location, including the selected prefix. -/
noncomputable def WorldTemplateMajorBackwardInitialization.firstLocation :=
  bootstrap.backward.route.locate (.appFunction bootstrap.location)

private theorem firstContext :
    ((bootstrap.backward.route.locate (.appFunction bootstrap.location))).contextDerivation input.provenance.initial =
      bootstrap.location.contextDerivation input.provenance.initial := by
  exact bootstrap.backward.route.locate_contextDerivation (.appFunction bootstrap.location) input.provenance.initial

/-- Everything after the initial frame witnesses is produced by the first
application history, header transplant, and empty-demand capture interpreter. -/
theorem WorldTemplateMajorBackwardInitialization.captureFirstFormalWorld
    (origin : ProjectionParameterOrigin rightEnv name rightHead.info)
    {signature : ConstantTelescope (origin.family.type.instL rightHead.levels)}
    {domains : signature.domains = [C,D]}
    (destination : FormalFamilyDestination (U := U) origin signature domains)
    (field : EndpointRef rightEnv U rightSource rightHead.fieldType (.sort rightHead.fieldLevel))
    (fieldEq : rightHead.field = .ref field)
    (paid : Sponsored frontier [originalCallWorld controls .assignedComparison rightNode baseline])
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceClosed : ∀ source, source ≤ env → P source)
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .assignedComparison rightNode baseline]))
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .assignedComparison rightNode baseline])) :
    ∃ frame : OriginalRichFrame rightEnv env U registry target
        ((bootstrap.backward.route.locate (.appFunction bootstrap.location)).contextDerivation input.provenance.initial)
        answer.reply.reply.answer.reply.locals (rightRaw.comp commonLeft) (rightRaw.comp commonLeft)
        answer.reply.reply.answer.reply.available,
      ∃ captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered),
        HEq frame bootstrap.frame ∧ HEq captured bootstrap.captured ∧
        ∃ frameData : WorldUnaryFrameData P controls frontier frame captured,
        let graph := OriginalCaptureMap.identity ((bootstrap.backward.route.locate (.appFunction bootstrap.location)).contextDerivation input.provenance.initial)
        let routeFrame : OriginalTypeRouteFrame env registry target graph (rightRaw.comp commonLeft) (rightRaw.comp commonLeft) :=
          ⟨_, _, ⟨frame, input.substitutions⟩, input.closed⟩
        let ownBase := frame.captureBase input.substitutions
        ∃ history : OriginalApplyPiHistory env registry target (rightRaw.comp commonLeft) (rightRaw.comp commonLeft)
            (originalApplicationTypeRouteSide input.provenance.initial bootstrap.backward.firstDomain
              bootstrap.backward.firstBody bootstrap.backward.firstFunction bootstrap.backward.firstArgument
              bootstrap.backward.firstResult bootstrap.backward.firstHu bootstrap.backward.firstHv
              (bootstrap.backward.route.locate (.appFunction bootstrap.location)) graph)
            (destination.nativeSide rightSource),
          ∃ sourceEq : history.sourceFrame = routeFrame,
            history.rightDomain = destination.firstDomain ∧
            history.headerFrame = closedTypeRouteFrame (ContextDerivation.nil (env := origin.types) (U := U))
              rightSource env registry target (rightRaw.comp commonLeft) (rightRaw.comp commonLeft) ∧
            ∃ headerWorld : WorldEnvironmentProvenance strata U history.final,
              headerWorld.worlds = [] ∧
              ∃ data : history.whole.ControlledWorldData P ownBase ownBase.initialCaps controls.cutoff controls.fuel frontier,
                ∃ boundary : history.whole.WorldBoundary data.inputs controls (controls.atHeader origin.constructorOrigin)
                    ((congrArg (fun f : OriginalTypeRouteFrame env registry target graph (rightRaw.comp commonLeft) (rightRaw.comp commonLeft) => f.realization.frame.dependencyEnvironment controls.ordered) sourceEq).symm ▸ captured)
                    headerWorld,
                  boundary.FrameOccurrenceCoherent data.controls data.frames ∧
                  Sponsored [originalCallWorld controls .assignedComparison rightNode captured]
                    (history.whole.worldReserve data.inputs).worlds ∧
                  Sponsored [originalCallWorld controls .assignedComparison rightNode baseline]
                    (history.whole.worldReserve data.inputs).worlds ∧
        ∃ reserveEnvironment, ∃ reserve : WorldEnvironmentProvenance strata U reserveEnvironment,
          Sponsored [originalCallWorld controls .assignedComparison rightNode captured] reserve.worlds ∧
          Sponsored [originalCallWorld controls .assignedComparison rightNode baseline] reserve.worlds ∧
          Nonempty (WorldVariableDemandReply P ownBase ownBase.initialCaps
            (.capture (destination.nativeSide rightSource).graph destination.firstDomain graph bootstrap.backward.firstArgument
              (.ofLocation (.appArgument (bootstrap.backward.route.locate (.appFunction bootstrap.location))) input.provenance.initial))
            (rightRaw.comp commonLeft) (rightRaw.comp commonLeft) (controls.atHeader origin.constructorOrigin)
            reserve frontier 0 (Profile.empty : Profile 0)) := by
  have framed : ∃ frame : OriginalRichFrame rightEnv env U registry target
      ((bootstrap.backward.route.locate (.appFunction bootstrap.location)).contextDerivation input.provenance.initial)
      answer.reply.reply.answer.reply.locals (rightRaw.comp commonLeft) (rightRaw.comp commonLeft)
      answer.reply.reply.answer.reply.available,
      ∃ captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered),
      HEq frame bootstrap.frame ∧ HEq captured bootstrap.captured ∧
      Nonempty (WorldUnaryFrameData P controls frontier frame captured) ∧
      environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment ∧
      Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds := by
    exact recontextFirstFrame
      (bootstrap.backward.route.locate_contextDerivation (.appFunction bootstrap.location) input.provenance.initial).symm
      controls frontier bootstrap.frame bootstrap.captured bootstrap.frameData baseline bootstrap.capacity bootstrap.covered
  obtain ⟨frame, captured, sameFrame, sameCaptured, ⟨frameData⟩, capacity, covered⟩ := framed
  refine ⟨frame, captured, sameFrame, sameCaptured, frameData, ?_⟩
  let graph := OriginalCaptureMap.identity ((bootstrap.backward.route.locate (.appFunction bootstrap.location)).contextDerivation input.provenance.initial)
  let routeFrame : OriginalTypeRouteFrame env registry target graph (rightRaw.comp commonLeft) (rightRaw.comp commonLeft) :=
    ⟨_, _, ⟨frame, input.substitutions⟩, input.closed⟩
  let generation := frameData.generation input.substitutions
  have readyPacket : Nonempty (generation.Controlled frontier) :=
    WorldUnaryFrameData.controlled (P := P) (controls := controls) (frontier := frontier)
      (frame := frame) (captured := captured) frameData input.substitutions
  let ready := Classical.choice readyPacket
  let hereditary := frameData.generation_hereditary input.substitutions
  let familyOrigin := origin.familyTypesOrigin.extend origin.typesBelow
  have shape : origin.family.type.instL rightHead.levels = .forallE C (.forallE D signature.result) := by
    exact signature.type_eq.trans (by rw [domains]; rfl)
  exact destination.captureFirstArgumentWorld input.provenance.initial bootstrap.backward.firstDomain
    bootstrap.backward.firstBody bootstrap.backward.firstFunction bootstrap.backward.firstArgument
    bootstrap.backward.firstResult bootstrap.backward.firstHu bootstrap.backward.firstHv (bootstrap.backward.route.locate (.appFunction bootstrap.location))
    graph routeFrame controls input.sourceBelow captured origin familyOrigin rightHead.levelsWF shape
    (frame.captureBase input.substitutions).initialCaps frontier generation ready ⟨rfl,rfl⟩ trivial hereditary
    (Covered.refl _) (sourceClosed _ (familyOrigin.sourceBelow.trans input.sourceBelow))
    (sourceClosed _ (origin.typesBelow.trans input.sourceBelow)) rightNode rightHead field fieldEq .here
    captured (fun _ => rfl) rfl baseline capacity covered paid henv hscoped formed bank unary

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
