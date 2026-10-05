import Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionComputational
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProjectionSelection
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedApplicationExecution
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldMappedTwoVariableApplication

/-! Physical projection terminals execute the actual proper major child.
When that major is a variable, its retained record demand is rebuilt from the
traced caller resource programs. No equality of source and caller controls is
used, and no physical projection origin is asserted for a charged residual. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private projectionMajor_cost_lt from
  Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionReindex
open private singletonSponsoredBelow from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

structure RetainedProjectionMajorAnswer
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (origin : RetainedNativeProjectionOrigin root env registry target source locals σ name index value)
    (controls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length)) (τ : Subst) (available : Valuation) where
  value : RichComputationalValue sourceEnv env U registry target (.ref (.right origin.head.major))
    locals σ τ available (Profile.singleton (n := origin.rank + 1) (.record origin.record))
  certificate : ControlledStoredQuery controls frontier (.certificate value.certificate)
  query : ControlledStoredQuery controls frontier (.observation value.rightQuery.observation)

/-- This is the original projection's proper-major F call. The selected
field request and its domain/support remain those of the same literal origin. -/
theorem RetainedNativeProjectionOrigin.executeMajorWorld
    {assigned value : VExpr}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (origin : RetainedNativeProjectionOrigin root env registry target source locals σ name index value)
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    {context : ContextDerivation sourceEnv U source}
    (route : PrefixRoute sourceEnv U source (.proj name index value) node (projectionNatural origin.head))
    (provenance : EndpointProvenance context node)
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : origin.majorFootprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.observation origin.majorQuery))
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured])) :
    Nonempty (RetainedProjectionMajorAnswer origin controls frontier τ available) := by
  have majorCost : (Closure.close ((EndpointState.ref (.right origin.head.major)).dependencyOrigin controls.ordered)
      (frame.dependencyEnvironment controls.ordered)).cost <
      (Closure.close (node.dependencyOrigin controls.ordered)
        (frame.dependencyEnvironment controls.ordered)).cost := by
    have proper := projectionMajor_cost_lt (naturalProjectionHead origin.head)
      controls.ordered (frame.dependencyEnvironment controls.ordered)
    exact Nat.lt_of_lt_of_le proper (route.dependency_cost_le controls.ordered _)
  have lower : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental (.ref (.right origin.head.major)) captured)
      (originalCallWorld controls .fundamental node captured) :=
    original_child (richSchedule_strict majorCost _ _) _ _ _ _ captured.worlds
  have smaller : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental (.ref (.right origin.head.major)) captured])
      (frontier ++ [originalCallWorld controls .fundamental node captured]) := by
    have fund : ∀ inherited : List (World strata.rules.length),
        CallBelow strata.rules.length
          (inherited ++ [originalCallWorld controls .fundamental (.ref (.right origin.head.major)) captured])
          (inherited ++ [originalCallWorld controls .fundamental node captured]) := by
      intro inherited
      induction inherited with
      | nil => exact split_call (by intro world member; cases List.mem_singleton.mp member; exact lower)
      | cons world rest ih => exact ih.cons world
    exact fund frontier
  let majorProvenance : EndpointProvenance context (.ref (.right origin.head.major)) := {
    rootSource := provenance.rootSource, rootExpression := provenance.rootExpression, rootType := provenance.rootType
    root := provenance.root, initial := provenance.initial
    location := .projMajor (route.locate provenance.location)
    context_eq := by
      change context = (route.locate provenance.location).contextDerivation provenance.initial
      rw [PrefixRoute.locate_contextDerivation]
      exact provenance.context_eq }
  obtain ⟨answer, ⟨certificate⟩, ⟨query⟩⟩ :=
    (bank _ smaller).computational (.ref (.right origin.head.major)) majorProvenance controls
      frame captured captured frontier (Nat.le_refl _) (Covered.refl _) rfl
      (singletonSponsoredBelow paid lower) data closed formed substitutions origin.majorQuery resources ready
  exact ⟨⟨answer, certificate, query⟩⟩

/-- The actual returned major relation supplies the selected field demand;
this is not a caller-provided projection admission. -/
theorem RetainedProjectionMajorAnswer.fieldRelated
    {value : VExpr}
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {origin : RetainedNativeProjectionOrigin root env registry target source locals σ name index value}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    (answer : RetainedProjectionMajorAnswer origin controls frontier τ available)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    Related env U registry target (.proj name index (value.subst σ))
      (.proj name index (value.subst τ)) origin.request.domain origin.request.input origin.request.support := by
  simpa only [origin.nameEq] using answer.value.related.projectRecord henv hscoped formed origin.member

inductive RetainedProjectionStep
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (controls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length)) (τ : Subst) (available : Valuation) :
    RetainedProjectionOrigin root env registry target source locals σ name index value → Type where
  | executed {actual : RetainedNativeProjectionOrigin root env registry target source locals σ name index value}
      (answer : RetainedProjectionMajorAnswer actual controls frontier τ available) :
      RetainedProjectionStep controls frontier τ available (.original actual)
  | pending (actual : RetainedChargedProjectionOrigin root env registry target source locals σ name index value) :
      RetainedProjectionStep controls frontier τ available (.charged actual)

/-- The shared term driver can dispatch a projection terminal without
reselecting a branch or losing the literal charged annotation's size. -/
theorem ControlledStoredQuery.executeRetainedProjectionSized
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint}
    (ready : ControlledStoredQuery controls frontier (.certificate query))
    (provenance : EndpointProvenance context node)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : footprint.Available available)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (selected : atom ∈ profile.atoms) :
    ∃ origin : RetainedProjectionOrigin provenance.root env registry target source locals σ name index value,
    ∃ children : RetainedProjectionWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      origin.footprint.Available available ∧ children.worlds ⊆ ready.annotation.worlds ∧
      origin.RootedAt node ∧ children.retainedSize < sizeOf (show WorldCertProvenance strata query from ready.annotation) ∧
      (∀ policy, origin.headDepth policy ≤ query.headDepth policy) ∧
      Nonempty (RetainedProjectionStep controls frontier τ available origin) := by
  obtain ⟨origin, children, path, included, worlds, rooted, smaller, depth⟩ :=
    ready.annotation.retainedProjectionOriginSized provenance.location selected
      (budget := sizeOf (show WorldCertProvenance strata query from ready.annotation)) (Nat.le_refl _)
  have supplied : origin.footprint.Available available :=
    fun index need member => resources index need (included member)
  refine ⟨origin, children, path, supplied, worlds, rooted, smaller, depth, ?_⟩
  cases origin with
  | charged actual => exact ⟨.pending actual⟩
  | original actual =>
    cases children with
    | original annotation =>
      obtain ⟨route⟩ := rooted
      have majorReady : ControlledStoredQuery controls frontier (.observation actual.majorQuery) := {
        annotation := annotation.major
        within := fun control active => Nat.le_trans (Nat.le_max_left _ _)
          (Nat.le_trans (depth _) (ready.within control active))
        sponsored := fun world member => ready.sponsored world (worlds (by
          exact List.mem_append_left _ (List.mem_append_right _ member))) }
      obtain ⟨answer⟩ := actual.executeMajorWorld route provenance controls frame captured frontier data closed formed
        substitutions (fun i need member => supplied i need (List.mem_append_left _ member)) majorReady paid bank
      exact ⟨.executed answer⟩

/-- Replay an original variable observation directly. Liveness is derived
from the actual caller frame, so no source F result or masked depth bound is
needed for this reconstruction. -/
theorem CallerVariableProgramScope.rebuildVariableObservationWorld
    {index : Nat}
    {strata : EquationStratification env}
    (scope : CallerVariableProgramScope env U registry target
      (fun i need => need ∈ callerAvailable i) sourceAvailable)
    {sourceNode : EndpointState sourceEnv U source (.bvar sourceIndex) sourceAssigned}
    (query : RichObs sourceEnv env U registry target sourceNode sourceLocals sourceσ requested footprint)
    (resources : footprint.Available sourceAvailable)
    (closed : sourceAvailable.AtomClosed)
    (mapped : scope.index sourceIndex = some index)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : callerEnv.Ordered)
    {context : ContextDerivation callerEnv U callerSource}
    (frame : OriginalRichFrame callerEnv env U registry target context callerLocals callerσ callerτ callerAvailable)
    (node : EndpointState callerEnv U callerSource (.bvar index) assigned)
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length)) :
    ∃ result : RichGradedResult callerEnv env U registry target node callerLocals callerσ callerAvailable requested,
      Nonempty (ControlledStoredQuery controls frontier (.observation result.observation)) := by
  obtain ⟨used, ⟨trace⟩, supplied⟩ := query.variableDependency closed resources
  let leaves (i : Nat) (need : Need) (member : (i, need) ∈ used) :
      VariableDependencyProgram env U registry target (fun i need => need ∈ callerAvailable i) index need.profile := by
    have same := trace.indices member
    subst i
    exact scope.program sourceIndex need (supplied sourceIndex need member) index mapped
  let replay := SortableVariableTrace.replayPrograms henv hscoped formed trace leaves
  let dependency : WorldVariableDependency env U registry target callerAvailable index requested := {
    rank := replay.rank, bound := replay.bound, raw := replay.raw, footprint := replay.footprint
    trace := replay.trace, resources := replay.resources, adapter := replay.adapter }
  exact ⟨dependency.atNode henv hscoped formed ordered frame node,
    ⟨dependency.atNode_controlled controls frontier henv hscoped formed ordered frame node⟩⟩

/-- A literal physical projection on a renamed variable supplies exactly
its retained record demand at the caller's genuine variable endpoint. The
record's family metadata, field request and raw input profile are unchanged. -/
theorem RetainedNativeProjectionOrigin.rebuildVariableMajorWorld
    {assigned : VExpr}
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (origin : RetainedNativeProjectionOrigin root env registry target source sourceLocals sourceσ
      name fieldIndex (.bvar sourceIndex))
    (scope : CallerVariableProgramScope env U registry target
      (fun i need => need ∈ callerAvailable i) sourceAvailable)
    (resources : (origin.majorFootprint ++ origin.fieldFootprint).Available sourceAvailable)
    (closed : sourceAvailable.AtomClosed)
    (mapped : scope.index sourceIndex = some index)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : callerEnv.Ordered)
    {context : ContextDerivation callerEnv U callerSource}
    (frame : OriginalRichFrame callerEnv env U registry target context callerLocals callerσ callerτ callerAvailable)
    (node : EndpointState callerEnv U callerSource (.bvar index) assigned)
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length)) :
    ∃ result : RichGradedResult callerEnv env U registry target node callerLocals callerσ callerAvailable
        (Profile.singleton (n := origin.rank + 1) (.record origin.record)),
      Nonempty (ControlledStoredQuery controls frontier (.observation result.observation)) := by
  exact scope.rebuildVariableObservationWorld origin.majorQuery
    (fun i need member => resources i need (List.mem_append_left _ member)) closed mapped
    henv hscoped formed ordered frame node controls frontier

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
