import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCallerHeaderTransport
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldEqualityReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldParameterComparison

/-! The caller-selected declaration header is replayed at the retained universe
seed by actual R/equality/R calls in that same earlier source. The original
query, control prefix and selected frame histories are preserved. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

private theorem reindexEqualAtWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {left : OriginalNestedDisplay U common leftExpression leftType}
    {right : OriginalNestedDisplay U common rightExpression rightType}
    (equal : leftExpression = rightExpression)
    (henv : env.Ordered)
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (rightControls : OriginalWorldControls strata right.sourceEnv)
    (sameCutoff : leftControls.cutoff = rightControls.cutoff)
    (sameFuel : leftControls.fuel = rightControls.fuel)
    (leftWorld : WorldEnvironmentProvenance strata U initialEnvironment)
    (rightWorld : WorldEnvironmentProvenance strata U finalEnvironment)
    (frontier parent : List (World strata.rules.length))
    (answer : AmbientBoundedParameterReply base caps start left commonLeft commonRight
      (profile : Profile n) (environmentCost initialEnvironment))
    (answerData : WorldParameterReplyData (P := P) leftControls leftWorld frontier answer)
    (sorted : profile.HasType (.sort relevant))
    (rightFrame : OriginalCaptureRealization right.graph env registry target rightLocals
      commonLeft commonRight rightAvailable)
    (rightData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := right) rightControls rightWorld frontier rightFrame)
    (sponsored : Sponsored frontier
      [originalCallWorld leftControls .expressionReindex left.node leftWorld,
       originalCallWorld rightControls .expressionReindex right.node rightWorld])
    (smaller : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld leftControls .expressionReindex left.node leftWorld,
        originalCallWorld rightControls .expressionReindex right.node rightWorld]) parent)
    (bank : WorldBoundedCallBank env U registry strata P parent) :
    ∃ result : AmbientBoundedParameterReply base caps start right commonLeft commonRight
        profile (environmentCost finalEnvironment),
      Nonempty (WorldParameterReplyData (P := P) rightControls rightWorld frontier result) := by
  cases equal
  exact answer.reindexAtWorld henv leftControls rightControls sameCutoff sameFuel
    leftWorld rightWorld frontier parent answerData sorted rightFrame rightData sponsored smaller bank

/-- All three comparisons are strictly below the actual caller by declaration
count at the unchanged cutoff/fuel; no header replay answer is supplied. -/
theorem RetainedHeaderUniverse.replayCallerWorld
    {leftLevels rightLevels : List VLevel}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    (controls : OriginalWorldControls strata sourceEnv)
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (caller : EndpointState sourceEnv U source expression assigned)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (incoming : AmbientBoundedParameterReply base caps start
      (RetainedHeaderUniverse.display origin leftWF common) commonLeft commonRight
      (profile : Profile n) (environmentCost ([] : List Closure)))
    (incomingData : WorldParameterReplyData (P := P) (controls.atHeader origin) .nil frontier incoming)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (below : sourceEnv ≤ env) (sourceClosed : ∀ source, source ≤ env → P source)
    (sorted : profile.HasType (.sort relevant))
    (paid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline])) :
    ∃ result : AmbientBoundedParameterReply base caps start
      (RetainedHeaderUniverse.display origin rightWF common) commonLeft commonRight profile
      (environmentCost ([] : List Closure)),
      Nonempty (WorldParameterReplyData (P := P) (controls.atHeader origin) .nil frontier result) := by
  let original := RetainedHeaderUniverse.original origin leftWF rightWF equivalent
  let graph : OriginalCaptureMap (common := common)
      (ContextDerivation.nil (env := origin.source) (U := U)) Subst.id := .empty common
  let first := parameterEqualityDisplay graph original true
  let last := parameterEqualityDisplay graph original false
  let parent := originalCallWorld controls .fundamental caller baseline
  have lower {expression assigned} (node : EndpointState origin.source U [] expression assigned)
      (phase : RichPhase) :
      WorldBelow strata.rules.length
        (originalCallWorld (controls.atHeader origin) phase node .nil) parent :=
    originalClosedHeader_below controls origin node caller baseline phase .fundamental
  have funded {calls : List (World strata.rules.length)}
      (smaller : ∀ child ∈ calls, WorldBelow strata.rules.length child parent) :
      CallBelow strata.rules.length (frontier ++ calls) (frontier ++ [parent]) := by
    have step := split_call smaller
    have prefixed : ∀ sponsors : List (World strata.rules.length),
        CallBelow strata.rules.length (sponsors ++ calls) (sponsors ++ [parent]) := by
      intro sponsors
      induction sponsors with
      | nil => exact step
      | cons world rest ih => exact ih.cons world
    exact prefixed frontier
  have sponsors {calls : List (World strata.rules.length)}
      (smaller : ∀ child ∈ calls, WorldBelow strata.rules.length child parent) :
      Sponsored frontier calls := by
    intro world member
    exact singletonSponsoredBelow paid (smaller world member) world (List.mem_singleton_self world)
  let empty := closedTypeRouteFrame
    (ContextDerivation.nil (env := origin.source) (U := U)) common env registry target commonLeft commonRight
  let generated : WorldGenerated strata P base caps commonLeft commonRight graph
      empty.realization.frame.raw (controls.atHeader origin) :=
    .empty common commonLeft commonRight (origin.sourceBelow.trans below)
      (sourceClosed _ (origin.sourceBelow.trans below)) (controls.atHeader origin)
  have ready : generated.Controlled frontier :=
    ⟨.nil, by intro control active; exact Nat.zero_le _, by intro world member; cases member⟩
  let firstData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := first) (controls.atHeader origin) .nil frontier empty.realization := {
    generation := generated, replayable := trivial, controlled := ready,
    compatible := ⟨rfl, rfl⟩, closed := by intro index need member; cases member
    capacity := Nat.le_refl _, covered := Covered.refl [], hereditary := ⟨trivial, .nil, trivial⟩ }
  have firstLower : ∀ child ∈
      [originalCallWorld (controls.atHeader origin) .expressionReindex
        (RetainedHeaderUniverse.display origin leftWF common).node .nil,
       originalCallWorld (controls.atHeader origin) .expressionReindex first.node .nil],
      WorldBelow strata.rules.length child parent := by
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact lower _ _
    · cases List.mem_singleton.mp member; exact lower _ _
  obtain ⟨input, ⟨inputData⟩⟩ := reindexEqualAtWorld (right := first) subst_id.symm henv
    (controls.atHeader origin) (controls.atHeader origin) rfl rfl .nil .nil frontier _
    incoming incomingData sorted empty.realization firstData
    (sponsors firstLower) (funded firstLower) bank
  have equalityLower : ∀ child ∈
      [originalCallWorld (controls.atHeader origin) .fundamental (.ref (.left original)) .nil],
      WorldBelow strata.rules.length child parent := by
    intro child member
    cases List.mem_singleton.mp member
    exact lower _ _
  obtain ⟨changed, ⟨changedData⟩⟩ := input.equalityStepWorld graph original true henv hscoped formed
    (controls.atHeader origin) .nil frontier _ inputData sorted
    (sponsors equalityLower) (funded equalityLower) unary
  let finalData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := RetainedHeaderUniverse.display origin rightWF common)
      (controls.atHeader origin) .nil frontier empty.realization := {
    generation := generated, replayable := trivial, controlled := ready,
    compatible := ⟨rfl, rfl⟩, closed := by intro index need member; cases member
    capacity := Nat.le_refl _, covered := Covered.refl [], hereditary := ⟨trivial, .nil, trivial⟩ }
  have lastLower : ∀ child ∈
      [originalCallWorld (controls.atHeader origin) .expressionReindex last.node .nil,
       originalCallWorld (controls.atHeader origin) .expressionReindex
        (RetainedHeaderUniverse.display origin rightWF common).node .nil],
      WorldBelow strata.rules.length child parent := by
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact lower _ _
    · cases List.mem_singleton.mp member; exact lower _ _
  exact reindexEqualAtWorld (left := last)
    (right := RetainedHeaderUniverse.display origin rightWF common) subst_id henv
    (controls.atHeader origin) (controls.atHeader origin) rfl rfl .nil .nil frontier _
    changed changedData sorted empty.realization finalData
    (sponsors lastLower) (funded lastLower) bank

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  (initial : ContextDerivation sourceEnv U rootSource)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source (.const name levels) (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located root (.app hu hv (.ref domain) body function argument result))
  (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)

local notation "side" => originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph

/-- Complete caller-formation to declared-header transport at the retained
seed. The declaration is identified by actual ambient lookup uniqueness,
while the new origin is selected from the caller's primitive original. -/
theorem callerConstantRetainedHeaderWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {queryLevels : List VLevel}
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (incoming : AmbientBoundedParameterReply base caps
      ((VExpr.forallE A B).subst (raw.comp commonLeft)) (side).functionFormationDisplay
      commonLeft commonRight (profile : Profile n) (environmentCost baselineEnvironment))
    (incomingData : WorldParameterReplyData (P := P) controls baseline frontier incoming)
    (lookup : env.constants name = some info)
    (queryWF : ∀ level ∈ queryLevels, level.WF U)
    (queryEquivalent : List.Forall₂ (· ≈ ·) queryLevels levels)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (below : sourceEnv ≤ env)
    (sorted : profile.HasType (.sort relevant))
    (sourceClosed : ∀ source, source ≤ env → P source)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental (side).node baseline])
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (side).node baseline]))
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (side).node baseline])) :
    ∃ origin : ConstantHeaderOrigin sourceEnv name info,
    ∃ answer : AmbientBoundedParameterReply base caps
      ((VExpr.forallE A B).subst (raw.comp commonLeft))
      (RetainedHeaderUniverse.display origin queryWF common) commonLeft commonRight
      profile (environmentCost ([] : List Closure)),
      Nonempty (WorldParameterReplyData (P := P) (controls.atHeader origin) .nil frontier answer) := by
  obtain ⟨selection, origin, header, ⟨headerData⟩⟩ := callerConstantHeaderWorld
    initial domain body function argument result hu hv location graph controls baseline frontier
    incoming incomingData henv hscoped formed below sorted sourceClosed paid bank
  have sameInfo : selection.info = info :=
    Option.some.inj ((below.constants selection.lookup).symm.trans lookup)
  cases sameInfo
  have equivalent : List.Forall₂ (· ≈ ·) selection.seed queryLevels :=
    Lean4Lean.List.Forall₂.trans (T := (· ≈ ·)) (fun _ _ _ first second => first.trans second)
      selection.equivalent (Lean4Lean.List.Forall₂.imp (fun _ _ equal => equal.symm)
        (Lean4Lean.List.Forall₂.flip queryEquivalent))
  obtain ⟨answer, answerData⟩ := RetainedHeaderUniverse.replayCallerWorld
    controls origin selection.seedWF queryWF equivalent (side).node baseline frontier header headerData
    henv hscoped formed below sourceClosed sorted paid bank unary
  exact ⟨origin, answer, answerData⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
