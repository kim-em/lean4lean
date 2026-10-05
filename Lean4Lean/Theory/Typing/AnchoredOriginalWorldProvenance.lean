import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrame
import Lean4Lean.Theory.Typing.AnchoredOriginalGroupBaselineBudget
import Lean4Lean.Theory.Typing.AnchoredOriginalRichSchedule
import Lean4Lean.Theory.Typing.EquationWorldClosureOrder
import Lean4Lean.Theory.Typing.EquationControls

/-! Typed provenance for the *existing* numerical capture ledger. Worlds
are computed from actual original endpoints, their actual source orders,
and the recursively retained captured ledger. Caller fuel is retained
explicitly; it is not inferred from an empty seed query. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

structure OriginalWorldControls (strata : EquationStratification env) (sourceEnv : VEnv) where
  ordered : sourceEnv.Ordered
  cutoff : Nat
  cutoffBound : cutoff ≤ strata.rules.length
  sourceCutoff : strata.SourceCutoff sourceEnv cutoff
  fuel : Nat → Nat

mutual
inductive WorldClosureProvenance (strata : EquationStratification env) (U : Nat) : Closure → Type where
  | original
      {sourceEnv : VEnv} {source : List VExpr} {expression assigned : VExpr}
      (node : EndpointState sourceEnv U source expression assigned)
      (controls : OriginalWorldControls strata sourceEnv)
      {captured : List Closure}
      (environment : WorldEnvironmentProvenance strata U captured) :
      WorldClosureProvenance strata U (.close (node.dependencyOrigin controls.ordered) captured)
  /-- A retained route reserves its actual call phase. Its endpoint and
  captured ledger are still the original ones; this is not a fresh sponsor. -/
  | scheduled
      {sourceEnv : VEnv} {source : List VExpr} {expression assigned : VExpr}
      (phase : RichPhase)
      (node : EndpointState sourceEnv U source expression assigned)
      (controls : OriginalWorldControls strata sourceEnv)
      {captured : List Closure}
      (environment : WorldEnvironmentProvenance strata U captured) :
      WorldClosureProvenance strata U (.close (node.dependencyOrigin controls.ordered) captured)
  /-- The immutable combined reservation of an ordinary capture. Its key
  charges the actual value/domain bundle, retaining the original tail worlds.
  The two component worlds remain available to existing exact lookups. -/
  | captureBundle
      {sourceEnv : VEnv} {source : List VExpr} {a A : VExpr} {level : VLevel}
      (controls : OriginalWorldControls strata sourceEnv)
      (domain : EndpointRef sourceEnv U source A (.sort level))
      (argument : EndpointState sourceEnv U source a A)
      {captured : List Closure}
      (environment : WorldEnvironmentProvenance strata U captured) :
      WorldClosureProvenance strata U
        (.bundle (.close (argument.dependencyOrigin controls.ordered) captured)
          (.close (domain.dependencyOrigin controls.ordered) captured))
  | bundle {left right : Closure}
      (first : WorldClosureProvenance strata U left)
      (second : WorldClosureProvenance strata U right) :
      WorldClosureProvenance strata U (.bundle left right)
inductive WorldEnvironmentProvenance (strata : EquationStratification env) (U : Nat) : List Closure → Type where
  | nil : WorldEnvironmentProvenance strata U []
  | cons {head : Closure} {tail : List Closure}
      (entry : WorldClosureProvenance strata U head)
      (previous : WorldEnvironmentProvenance strata U tail) :
      WorldEnvironmentProvenance strata U (head :: tail)
end

mutual
noncomputable def WorldClosureProvenance.worlds
    (provenance : WorldClosureProvenance strata U closure) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match provenance with
  | .original (captured := captured) node controls environment =>
      [EquationWorldClosureOrder.Closure.node
        (EquationControlMeasure.key strata.rules.length controls.cutoff controls.fuel
          controls.ordered.constantCount (richSchedule .fundamental
            (Closure.close (node.dependencyOrigin controls.ordered) captured).cost)) environment.worlds]
  | .scheduled (captured := captured) phase node controls environment =>
      [EquationWorldClosureOrder.Closure.node
        (EquationControlMeasure.key strata.rules.length controls.cutoff controls.fuel
          controls.ordered.constantCount (richSchedule phase
            (Closure.close (node.dependencyOrigin controls.ordered) captured).cost)) environment.worlds]
  | .captureBundle (captured := captured) controls domain argument environment =>
      [EquationWorldClosureOrder.Closure.node
        (EquationControlMeasure.key strata.rules.length controls.cutoff controls.fuel
          controls.ordered.constantCount (richSchedule .expressionReindex
            (Closure.bundle (.close (argument.dependencyOrigin controls.ordered) captured)
              (.close (domain.dependencyOrigin controls.ordered) captured)).cost)) environment.worlds] ++
      [EquationWorldClosureOrder.Closure.node
        (EquationControlMeasure.key strata.rules.length controls.cutoff controls.fuel
          controls.ordered.constantCount (richSchedule .expressionReindex
            (Closure.close (argument.dependencyOrigin controls.ordered) captured).cost)) environment.worlds] ++
      [EquationWorldClosureOrder.Closure.node
        (EquationControlMeasure.key strata.rules.length controls.cutoff controls.fuel
          controls.ordered.constantCount (richSchedule .fundamental
            (Closure.close (domain.dependencyOrigin controls.ordered) captured).cost)) environment.worlds]
  | .bundle first second => first.worlds ++ second.worlds

noncomputable def WorldEnvironmentProvenance.worlds
    (provenance : WorldEnvironmentProvenance strata U captured) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match provenance with
  | .nil => []
  | .cons entry previous => entry.worlds ++ previous.worlds
end

def WorldEnvironmentProvenance.closures
    (_provenance : WorldEnvironmentProvenance strata U captured) : List Closure := captured

def WorldEnvironmentProvenance.append
    (first : WorldEnvironmentProvenance strata U left)
    (second : WorldEnvironmentProvenance strata U right) :
    WorldEnvironmentProvenance strata U (left ++ right) :=
  match first with
  | .nil => second
  | .cons entry previous => .cons entry (previous.append second)

@[simp] theorem WorldEnvironmentProvenance.worlds_append
    (first : WorldEnvironmentProvenance strata U left)
    (second : WorldEnvironmentProvenance strata U right) :
    (first.append second).worlds = first.worlds ++ second.worlds := by
  cases first with
  | nil => rfl
  | cons entry previous =>
      simp only [append, worlds, worlds_append previous second, List.append_assoc]
termination_by sizeOf first

/-- A frame annotation names the exact numerical environment and computes
its world frontier. This does not infer provenance from numeric costs. -/
structure OriginalFrameWorldProvenance
    (strata : EquationStratification env)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available) where
  controls : OriginalWorldControls strata sourceEnv
  environment : WorldEnvironmentProvenance strata U
    (frame.dependencyEnvironment controls.ordered)

/-- The exact location-derived ledger retains actual enclosing binder
originals. In particular this does not identify it with a selected owner's
possibly smaller semantic frame. -/
noncomputable def WorldEnvironmentProvenance.located
    {root : EndpointRef sourceEnv U source expression assigned}
    {node : EndpointState sourceEnv U selectedSource selectedExpression selectedType}
    (controls : OriginalWorldControls strata sourceEnv)
    (location : Located root node)
    (initial : WorldEnvironmentProvenance strata U captured) :
    WorldEnvironmentProvenance strata U (location.dependencyEnvironment controls.ordered captured) :=
  match location with
  | .here => initial
  | .expose parent | .convertTerm parent | .appFunction parent | .appArgument parent |
      .appDomain parent | .appResult parent | .appPiFormation parent | .lamDomain parent | .piDomain parent |
      .projField parent | .projMajor parent | .assignedFormation parent =>
      WorldEnvironmentProvenance.located controls parent initial
  | .lamBody (domain := domain) parent | .lamCodomain (domain := domain) parent |
      .appCodomain (domain := domain) parent | .piBody (domain := domain) parent =>
      .cons (.original domain controls (WorldEnvironmentProvenance.located controls parent initial))
        (WorldEnvironmentProvenance.located controls parent initial)

/-- A retained owner may be reconstructed, so its actual reservation carries
the reconstruction phase. Unary interpretation spends this phase reserve. -/
noncomputable def WorldEnvironmentProvenance.owner
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (controls : OriginalWorldControls strata sourceEnv)
    (owner : HeaderOwner field major)
    (initial : WorldEnvironmentProvenance strata U captured) :
    WorldClosureProvenance strata U (owner.dependencyClosure controls.ordered captured) := by
  cases owner with
  | inl selected | inr selected =>
    exact .scheduled .expressionReindex selected.node controls (WorldEnvironmentProvenance.located controls selected.location initial)

/-- The retained group envelope is built from actual field, major, and
original domain endpoints, with independent typed owner and prior ledgers. -/
noncomputable def WorldEnvironmentProvenance.groupBaseline
    (field : EndpointRef sourceEnv U source fieldExpression fieldType)
    (major : EndpointRef sourceEnv U source majorExpression majorType)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (ownerControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata headerEnv)
    (initial : WorldEnvironmentProvenance strata U ownerInitial)
    (prior : WorldEnvironmentProvenance strata U previous) :
    WorldEnvironmentProvenance strata U
      (groupCaptureBaseline field major domain ownerControls.ordered headerControls.ordered ownerInitial previous) :=
  .cons (.scheduled .expressionReindex (.ref domain) headerControls prior)
    (.cons (.bundle (.scheduled .expressionReindex (.ref field) ownerControls initial)
      (.scheduled .expressionReindex (.ref domain) headerControls prior))
    (.cons (.bundle (.scheduled .expressionReindex (.ref major) ownerControls initial)
      (.scheduled .expressionReindex (.ref domain) headerControls prior)) prior))

noncomputable def WorldEnvironmentProvenance.groupEntries
    {env : VEnv} {strata : EquationStratification env}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (ownerControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata headerEnv)
    (initial : WorldEnvironmentProvenance strata U ownerInitial)
    (prior : WorldEnvironmentProvenance strata U previous)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available ownerInitial rawCapture leftValue rightValue) :
    WorldEnvironmentProvenance strata U
      ((entries.map (fun entry => Closure.bundle
        (entry.owner.dependencyClosure ownerControls.ordered ownerInitial)
        (.close (domain.dependencyOrigin headerControls.ordered) previous))) ++ previous) := by
  induction entries with
  | nil => exact prior
  | cons entry entries ih =>
    exact .cons (.bundle (WorldEnvironmentProvenance.owner ownerControls entry.owner initial)
      (.original (.ref domain) headerControls prior)) ih

noncomputable def WorldEnvironmentProvenance.group
    {env : VEnv} {strata : EquationStratification env}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (ownerControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata headerEnv)
    (initial : WorldEnvironmentProvenance strata U ownerInitial)
    (prior : WorldEnvironmentProvenance strata U previous)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available ownerInitial rawCapture leftValue rightValue) :
    WorldEnvironmentProvenance strata U
      (entries.environment ownerControls.ordered headerControls.ordered ownerInitial previous) :=
  .cons (.original (.ref domain) headerControls prior)
    (.cons (.bundle (.scheduled .expressionReindex (.ref field) ownerControls initial)
      (.original (.ref domain) headerControls prior))
    (.cons (.bundle (.scheduled .expressionReindex (.ref major) ownerControls initial)
      (.original (.ref domain) headerControls prior))
      (WorldEnvironmentProvenance.groupEntries ownerControls headerControls initial prior entries)))

/-- No world labels are recovered from an erased reserve. The original
history ledger and the exact typed prior are retained independently. -/
noncomputable def WorldEnvironmentProvenance.groupHistory
    (field : EndpointRef sourceEnv U source fieldExpression fieldType)
    (major : EndpointRef sourceEnv U source majorExpression majorType)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (ownerControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata headerEnv)
    (initial : WorldEnvironmentProvenance strata U ownerInitial)
    (prior : WorldEnvironmentProvenance strata U previous)
    (route : WorldEnvironmentProvenance strata U reserve) :
    WorldEnvironmentProvenance strata U
      (groupCaptureHistoryReserve field major domain ownerControls.ordered headerControls.ordered
        ownerInitial previous reserve) :=
  route.append (WorldEnvironmentProvenance.groupBaseline field major domain ownerControls headerControls initial prior)

/-- The original call world is shared by all interpreter phases. Its definition
uses only the retained original and frame provenance. -/
noncomputable def originalCallWorld
    (controls : OriginalWorldControls strata sourceEnv) (phase : RichPhase)
    (node : EndpointState sourceEnv U source expression assigned)
    (captured : WorldEnvironmentProvenance strata U environment) : EquationWorldClosureOrder.World strata.rules.length :=
  .node (EquationControlMeasure.key strata.rules.length controls.cutoff controls.fuel
    controls.ordered.constantCount (richSchedule phase
      (OriginalClosureMeasure.Closure.close (node.dependencyOrigin controls.ordered) environment).cost))
    captured.worlds

/-- The immutable original bundle surrounds the selected active capture.
Only the active tail is reconstructed; the reservation is retained verbatim. -/
noncomputable def reservedCaptureWorldEnvironment
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (argument : EndpointState sourceEnv U source a A)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (selected : WorldEnvironmentProvenance strata U selectedEnvironment) :
    WorldEnvironmentProvenance strata U
      ([Closure.bundle (.close (argument.dependencyOrigin controls.ordered) baselineEnvironment)
        (.close (domain.dependencyOrigin controls.ordered) baselineEnvironment)] ++
       (Closure.bundle (.close (argument.dependencyOrigin controls.ordered) selectedEnvironment)
        (.close (domain.dependencyOrigin controls.ordered) selectedEnvironment) :: selectedEnvironment)) :=
  .cons (.captureBundle controls domain argument baseline)
    (.cons (.bundle (.scheduled .expressionReindex argument controls selected)
      (.original (.ref domain) controls selected)) selected)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
