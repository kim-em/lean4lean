import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeConstantOpening
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldEqualityReplay

/-! Universe alignment of an open retained operand is paid by its original
canonical opening. Reification may enlarge the proof, so neither R nor equality
is charged to the smaller operand schedule. The actual selected R frame and
its hereditary history are used for equality before freezing its resources. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

noncomputable def EndpointState.levelAlignment
    (ordered : sourceEnv.Ordered)
    (context : ContextDerivation sourceEnv U source)
    (node : EndpointState sourceEnv U source expression assigned)
    (equal : EqUpToLevels U expression next) :
    Derivation sourceEnv U source expression next assigned :=
  Classical.choice <| Derivation.reify <|
    EqUpToLevels.defeq ordered ordered.strong context.forget node.sound
      (EqUpToLevels.refl context.forget.levelWF node.sound).1 equal

/-- The returned query uses the original resource table and the actual right
endpoint of the constructed universe equality. No semantic answer, new source
bank, or bound on the synthesized proof's size is supplied. -/
theorem alignLevelsAtCanonicalOpening
    {strata : EquationStratification env} {P : VEnv → Prop}
    (owner : CanonicalCodeOwner env registry strata name)
    (fuel : Nat → Nat)
    {context : ContextDerivation owner.selected.origin.source U source}
    (node : EndpointState owner.selected.origin.source U source expression assigned)
    (provenance : EndpointProvenance context node)
    (equal : EqUpToLevels U expression next)
    (frame : OriginalRichFrame owner.selected.origin.source env U registry target
      context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U
      (frame.dependencyEnvironment owner.selected.origin.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P (canonicalQueryControls owner.selected fuel)
      frontier frame captured)
    (closed : available.AtomClosed)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (query : RichObs owner.selected.origin.source env U registry target node locals σ profile footprint)
    (resources : footprint.Available available)
    (ready : ControlledStoredQuery (canonicalQueryControls owner.selected fuel)
      frontier (.observation query))
    (caller : EndpointState callerEnv U callerSource callerExpression callerAssigned)
    (controls : OriginalWorldControls strata callerEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (nodeBelow : WorldBelow strata.rules.length
      (originalCallWorld (canonicalQueryControls owner.selected fuel) .fundamental node captured)
      (originalCallWorld controls .fundamental caller baseline))
    (masked : WithinAbove controls.cutoff controls.fuel (headDepth owner.selected.ordinal fuel))
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) :
    let original := EndpointState.levelAlignment owner.selected.origin.ordered context node equal
    ∃ answer : OriginalDirectionalEqualityResult original true env registry target
        locals σ τ available profile,
      Nonempty (ControlledStoredQuery (canonicalQueryControls owner.selected fuel)
        frontier (.observation answer.rightQuery.observation)) := by
  dsimp only
  let childControls := canonicalQueryControls owner.selected fuel
  let original := EndpointState.levelAlignment owner.selected.origin.ordered context node equal
  let base := frame.captureBase substitutions
  let left := OriginalNestedDisplay.identity base node provenance
  let first := OriginalNestedDisplay.identity base (.ref (.left original))
    (.ofLocation .here context)
  let donor := originalCallWorld controls .fundamental caller baseline
  have lower {e A} (child : EndpointState owner.selected.origin.source U source e A)
      (phase : RichPhase) :
      WorldBelow strata.rules.length (originalCallWorld childControls phase child captured) donor := by
    apply Below.root
      (openingDecrease owner.selected.ordinal_pos owner.selected.ordinal_le controls.cutoffBound
        masked controls.ordered.constantCount
        (richSchedule .fundamental (Closure.close (caller.dependencyOrigin controls.ordered) environment).cost)
        owner.selected.origin.ordered.constantCount
        (richSchedule phase (Closure.close (child.dependencyOrigin owner.selected.origin.ordered)
          (frame.dependencyEnvironment owner.selected.origin.ordered)).cost))
    intro world member
    exact EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans
      (Below.child member) nodeBelow
  have funded {calls : List (World strata.rules.length)}
      (smaller : ∀ child ∈ calls, WorldBelow strata.rules.length child donor) :
      CallBelow strata.rules.length (frontier ++ calls) (frontier ++ [donor]) := by
    have step := split_call smaller
    have appendLower : ∀ sponsors : List (World strata.rules.length),
        CallBelow strata.rules.length (sponsors ++ calls) (sponsors ++ [donor]) := by
      intro sponsors
      induction sponsors with
      | nil => exact step
      | cons world rest ih => exact ih.cons world
    exact appendLower frontier
  have sponsors {calls : List (World strata.rules.length)}
      (smaller : ∀ child ∈ calls, WorldBelow strata.rules.length child donor) :
      Sponsored frontier calls := by
    intro world member
    obtain ⟨sponsor, present, below⟩ := paid _ (List.mem_singleton_self _)
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans (smaller world member) below⟩
  have valueLower : ∀ child ∈ [originalCallWorld childControls .fundamental node captured],
      WorldBelow strata.rules.length child donor := by
    intro child member
    cases List.mem_singleton.mp member
    exact lower _ _
  obtain ⟨value, _, _⟩ := (unary _ (funded valueLower)).computational node provenance
    childControls frame captured captured frontier (Nat.le_refl _) (Covered.refl _) rfl
    (sponsors valueLower) data closed formed substitutions query resources ready
  let generated := data.generation substitutions
  obtain ⟨controlled⟩ := data.controlled substitutions
  let leftData : WorldCallFrameData (P := P) (base := base) (caps := base.initialCaps)
      (display := left) childControls captured frontier base.identityRealization := {
    generation := generated
    replayable := trivial
    controlled := controlled
    compatible := ⟨rfl, rfl⟩
    closed := closed
    capacity := Nat.le_refl _
    covered := Covered.refl _
    hereditary := data.generation_hereditary substitutions }
  let firstData : WorldCallFrameData (P := P) (base := base) (caps := base.initialCaps)
      (display := first) childControls captured frontier base.identityRealization := {
    generation := generated
    replayable := trivial
    controlled := controlled
    compatible := ⟨rfl, rfl⟩
    closed := closed
    capacity := Nat.le_refl _
    covered := Covered.refl _
    hereditary := data.generation_hereditary substitutions }
  have replayLower : ∀ child ∈
      [originalCallWorld childControls .expressionReindex left.node captured,
       originalCallWorld childControls .expressionReindex first.node captured],
      WorldBelow strata.rules.length child donor := by
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact lower _ _
    · cases List.mem_singleton.mp member; exact lower _ _
  obtain ⟨replayed, ⟨replayedData⟩⟩ := (bank _ (funded replayLower)).observation
    base base.initialCaps left first σ τ childControls childControls rfl rfl
    captured captured frontier rfl (sponsors replayLower)
    base.identityRealization leftData base.identityRealization firstData query resources ready
  let prior := replayed.answer.reply
  obtain ⟨selectedData⟩ := WorldUnaryFrameData.ofGenerated prior.realization.frame
    replayedData.generation replayedData.controlled replayedData.replayable
    replayedData.compatible replayedData.hereditary
  have equalityLower : ∀ child ∈
      [originalCallWorld childControls .fundamental (.ref (.left original)) captured],
      WorldBelow strata.rules.length child donor := by
    intro child member
    cases List.mem_singleton.mp member
    exact lower _ _
  obtain ⟨changed, ⟨changedReady⟩⟩ := (unary _ (funded equalityLower)).equality original true
    (.ofLocation .here context) childControls prior.realization.frame replayedData.generation.environment
    captured frontier (replayed.bounded childControls.ordered) replayedData.covered rfl
    (sponsors equalityLower) selectedData prior.closed formed prior.realization.substitutions
    prior.query.observation prior.query.resources replayedData.query
  let adapted : OriginalDirectionalEqualityResult original true env registry target
      prior.locals σ τ prior.available profile := {
    support := value.support
    related := by
      have mapped := prior.query.adapter.termMap henv hscoped formed
        (Profile.HasType.raise prior.query.bound value.typed)
        (value.typeCode.raise henv prior.query.bound) changed.related
      have lowered := Related.lower henv prior.query.bound formed mapped
      have leftId : first.raw.comp σ = σ := rfl
      have rightId : first.raw.comp τ = τ := rfl
      simpa only [OriginalFactorCut.lower_raised, leftId, rightId] using lowered
    rightQuery := changed.rightQuery.adaptRequest henv hscoped formed prior.query.bound prior.query.adapter }
  have included : ∀ index need, need ∈ prior.available index → need ∈ available index :=
    replayed.answer.capped.availableBound
  have same : prior.locals = locals := prior.locals_eq
  have move {firstLocals lastLocals : List Nat}
      (same : firstLocals = lastLocals)
      (answer : OriginalDirectionalEqualityResult original true env registry target
        firstLocals σ τ available profile)
      (controlled : ControlledStoredQuery childControls frontier (.observation answer.rightQuery.observation)) :
      ∃ result : OriginalDirectionalEqualityResult original true env registry target
          lastLocals σ τ available profile,
        Nonempty (ControlledStoredQuery childControls frontier (.observation result.rightQuery.observation)) := by
    cases same
    exact ⟨answer, ⟨controlled⟩⟩
  exact move same { adapted with rightQuery := adapted.rightQuery.availableMono included } changedReady

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
