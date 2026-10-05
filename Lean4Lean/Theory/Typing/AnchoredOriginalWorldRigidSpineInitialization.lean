import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationBackwardStep
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldAssignedSortQuery
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldParameterComparison
import Lean4Lean.Theory.Typing.AnchoredOriginalPrefixDisplay
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPrefix
import Lean4Lean.Theory.Typing.AnchoredRigidFamilySpinePreparation

/-! Actual backwards construction of a rigid-family observation. Each state
retains the selected frame, its finite ancestry, and the certificate on the
actual original assigned formation. Application conversion prefixes are paid
by a real assigned comparison before the actual packing step. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000

/-- A selected assigned observation, including its actual frame ancestry.
The immutable baseline is independent of all subsequent frame selections. -/
structure WorldAssignedQuery
    {registry : CanonicalHead.Registry} {target : List VExpr}
    {strata : EquationStratification env} (P : VEnv → Prop)
    {context : ContextDerivation sourceEnv U source}
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (node : EndpointState sourceEnv U source expression assigned)
    (σ τ : Subst) (relevant : Bool) (profile : Profile n) where
  locals : List Nat
  available : Valuation
  frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available
  substitutions : Ctx.SubstEq env U target σ τ source
  captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered)
  frameData : WorldUnaryFrameData P controls frontier frame captured
  closed : available.AtomClosed
  capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment
  covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds
  footprint : Footprint
  certificate : RichCert sourceEnv env U registry target node.typeFormation.node locals σ relevant profile footprint
  resources : footprint.Available available
  certificateReady : ControlledStoredQuery controls frontier (.certificate certificate)

/-- The same selected reply is opened, not reannotated or replaced by an
independent existential query. Its generation becomes the sandbox ancestry. -/
theorem WorldAssignedQuery.ofReply
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    (henv : env.Ordered) (controls : OriginalWorldControls strata display.sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (answer : AmbientBoundedParameterReply base caps start display.formationDisplay commonLeft commonRight
      (profile : Profile n) (environmentCost baselineEnvironment))
    (data : WorldParameterReplyData (P := P) (display := display.formationDisplay) controls baseline frontier answer)
    (sorted : profile.HasType (.sort relevant)) :
    ∃ output : WorldAssignedQuery (registry := registry) (target := target) (context := display.context)
      P controls baseline frontier display.node (display.raw.comp commonLeft)
        (display.raw.comp commonRight) relevant profile,
      output.locals = answer.reply.answer.reply.locals ∧
      output.available = answer.reply.answer.reply.available ∧
      HEq output.frame answer.reply.answer.reply.realization.frame := by
  let selected := answer.reply.answer.reply
  obtain ⟨footprint, certificate, certificateReady, resources, _⟩ :=
    selected.query.code_controlled henv controls data.query sorted
  obtain ⟨frameData⟩ := WorldUnaryFrameData.ofGenerated selected.realization.frame
    data.generation data.controlled data.replayable data.compatible data.hereditary
  exact ⟨⟨selected.locals, selected.available, selected.realization.frame,
    selected.realization.substitutions, data.generation.environment, frameData,
    selected.closed, answer.reply.bounded controls.ordered, data.covered,
    footprint, certificate, resources, certificateReady⟩, rfl, rfl, HEq.rfl⟩

/-- Conversion prefixes are crossed by actual C on the same selected frame.
Only the input's actual R sponsor is used; the natural endpoint has no larger
original cost and C has a strictly smaller phase. -/
theorem WorldAssignedQuery.prefix
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    {profile : Profile n}
    (initial : ContextDerivation sourceEnv U rootSource) (location : Located root first)
    (route : PrefixRoute sourceEnv U source expression first last)
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (input : WorldAssignedQuery (registry := registry) (target := target)
      (context := location.contextDerivation initial) P controls baseline frontier first σ τ relevant profile)
    (henv : env.Ordered) (sorted : profile.HasType (.sort relevant))
    (paid : Sponsored frontier [originalCallWorld controls .assignedComparison first baseline,
      originalCallWorld controls .assignedComparison last baseline])
    (banks : ∀ budget, WorldBoundedReplayAt env U registry strata P budget) :
    ∃ output : WorldAssignedQuery (registry := registry) (target := target)
      (context := (route.locate location).contextDerivation initial)
      P controls baseline frontier last σ τ relevant profile,
      output.locals = input.locals ∧
      ∀ index need, need ∈ output.available index → need ∈ input.available index := by
  let base := input.frame.captureBase input.substitutions
  let left := OriginalNestedDisplay.ofOccurrence initial location (.identity _)
  let right := originalPrefixDisplay initial location (.identity _) route
  let generated := input.frameData.generation input.substitutions
  obtain ⟨ready⟩ := input.frameData.controlled input.substitutions
  let leftData : WorldCallFrameData (P := P) (base := base) (caps := base.initialCaps)
      (display := left) controls baseline frontier base.identityRealization := {
    generation := generated, replayable := trivial, controlled := ready,
    compatible := ⟨rfl, rfl⟩, hereditary := input.frameData.generation_hereditary input.substitutions,
    closed := input.closed, capacity := input.capacity, covered := input.covered }
  let rightData : WorldCallFrameData (P := P) (base := base) (caps := base.initialCaps)
      (display := right) controls baseline frontier base.identityRealization := {
    generation := generated, replayable := trivial, controlled := ready,
    compatible := ⟨rfl, rfl⟩, hereditary := input.frameData.generation_hereditary input.substitutions,
    closed := input.closed, capacity := input.capacity, covered := input.covered }
  obtain ⟨answer, ⟨data⟩⟩ := (banks _).assigned base base.initialCaps left right σ τ
    controls controls rfl rfl baseline baseline frontier rfl paid
    base.identityRealization leftData base.identityRealization rightData
    input.certificate input.resources input.certificateReady
  obtain ⟨output, localsEq, availableEq, _frameEq⟩ :=
    WorldAssignedQuery.ofReply (display := right) henv controls baseline frontier answer data sorted
  have sameLocals : output.locals = input.locals := localsEq.trans answer.reply.answer.reply.locals_eq
  have included : ∀ index need, need ∈ output.available index → need ∈ input.available index := by
    rw [availableEq]
    exact answer.reply.answer.capped.availableBound
  rw [route.locate_contextDerivation location initial]
  exact ⟨output, sameLocals, included⟩


/-- Every actual query selected at a backwards application step is retained.
The next prepared plan uses this very request key and its exact rank bound. -/
structure WorldRigidPackedStep
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {profile : Profile n}
    (initial : ContextDerivation sourceEnv U rootSource)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (function : EndpointState sourceEnv U source f (.forallE A B))
    (argument : EndpointState sourceEnv U source a A)
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (location : Located root (.app hu hv (.ref domain) body function argument result))
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (input : WorldAssignedQuery (registry := registry) (target := target)
      (context := location.contextDerivation initial) P controls baseline frontier
      (.app hu hv (.ref domain) body function argument result) σ τ relevant profile)
    (prepared : RigidFamilySpine.Prepared env U registry target name levels profile) where
  packed : GeneratedApplicationPackedRequest domain body argument hu hv env registry target
    input.locals σ input.available relevant profile
  packedReady : packed.Controlled controls frontier
  value : RichSupportedValue sourceEnv env U registry target argument input.locals σ τ input.available packed.request.key.input
  value_support : value.support = packed.request.support
  valueReady : ControlledStoredQuery controls frontier (.certificate value.certificate)
  admitted : RankedData.RequestAdmission env U (relations env U registry packed.request.rank) target
    packed.parameterRequest (a.subst σ) (a.subst τ)
  nextPrepared : RigidFamilySpine.Prepared env U registry target name levels
    (Profile.pi (A.subst σ) (B.subst σ.lift) packed.request.support
      [(packed.request.key, raiseProfile packed.request.rank packed.request.bound profile)])
  plan_eq : nextPrepared.plan = .binder packed.request.key (prepared.plan.raise _ packed.request.bound)
  next : WorldAssignedQuery (registry := registry) (target := target)
    (context := (Located.appFunction location).contextDerivation initial)
    P controls baseline frontier function σ τ relevant
    (Profile.pi (A.subst σ) (B.subst σ.lift) packed.request.support
      [(packed.request.key, raiseProfile packed.request.rank packed.request.bound profile)])
  nextLocals : next.locals = input.locals
  nextAvailable : ∀ index need, need ∈ next.available index → need ∈ input.available index

/-- A natural application performs the actual backward pack and records its
literal key and exact raised body demand in the prepared finite spine. -/
theorem WorldAssignedQuery.application
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {profile : Profile n}
    (initial : ContextDerivation sourceEnv U rootSource)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (function : EndpointState sourceEnv U source f (.forallE A B))
    (argument : EndpointState sourceEnv U source a A)
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (location : Located root (.app hu hv (.ref domain) body function argument result))
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (input : WorldAssignedQuery (registry := registry) (target := target)
      (context := location.contextDerivation initial) P controls baseline frontier
      (.app hu hv (.ref domain) body function argument result) σ τ relevant profile)
    (prepared : RigidFamilySpine.Prepared env U registry target name levels profile)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (paid : Sponsored frontier [originalCallWorld controls .fundamental
      (.app hu hv (.ref domain) body function argument result) baseline])
    (unary : ∀ budget, WorldBoundedUnaryAt env U registry strata P budget)
    (replay : ∀ budget, WorldBoundedReplayAt env U registry strata P budget) :
    Nonempty (WorldRigidPackedStep initial domain body function argument result hu hv location
      controls baseline frontier input prepared) := by
  obtain ⟨packed, ⟨packedReady⟩, ⟨value, supportEq, ⟨valueReady⟩⟩, admitted, answer, ⟨data⟩⟩ :=
    applicationBackwardStepWorld initial domain body function argument result hu hv location
      input.frame input.substitutions controls input.captured frontier input.frameData
      baseline input.capacity input.covered henv hscoped formed input.closed paid
      (fun budget _ => unary budget) (fun budget _ => replay budget)
      input.certificate input.resources input.certificateReady
  have sorted := packed.request.certificate.formed
  have piWF := Profile.WF.pi_iff.mp sorted.wf_value
  let nextPrepared := prepared.prepend packed.request.bound packed.request.key
    packed.request.support (piWF.2 _ _ (List.mem_singleton_self _)).1 piWF.1
    packed.request.admitted (A.subst σ) (B.subst σ.lift)
  let display := OriginalNestedDisplay.ofOccurrence initial (.appFunction location) (.identity _)
  obtain ⟨next, localsEq, availableEq, _frameEq⟩ := WorldAssignedQuery.ofReply (display := display) henv controls baseline frontier
    answer data sorted
  refine ⟨⟨packed, packedReady, value, supportEq, valueReady, admitted, nextPrepared, rfl, next,
    localsEq.trans answer.reply.answer.reply.locals_eq, ?_⟩⟩
  rw [availableEq]
  exact answer.reply.answer.capped.availableBound


/-- A finite record of the actual backward computation. A step keeps the
selected conversion frame, packed argument observer and typed request, and
then the recursively selected function frame. The leaf is a genuine
primitive constant original, with its actual assigned-code certificate. -/
inductive WorldRigidBackwardTrace
    {registry : CanonicalHead.Registry} {target source : List VExpr}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (σ τ : Subst) (name : Name) (levels : List VLevel) :
    {expression assigned : VExpr} → (node : EndpointState sourceEnv U source expression assigned) →
    (location : Located root node) → {n : Nat} → {profile : Profile n} → {relevant : Bool} →
    (prepared : RigidFamilySpine.Prepared env U registry target name levels profile) →
    WorldAssignedQuery (registry := registry) (target := target)
      (context := location.contextDerivation initial) P controls baseline frontier node σ τ relevant profile → Type where
  | constant
      {node : EndpointState sourceEnv U source (.const name levels) assigned}
      {location : Located root node}
      {prepared : RigidFamilySpine.Prepared env U registry target name levels profile}
      {input : WorldAssignedQuery (registry := registry) (target := target)
        (context := location.contextDerivation initial) P controls baseline frontier node σ τ relevant profile}
      (head : ConstantPrefix node)
      (primitive : WorldAssignedQuery (registry := registry) (target := target)
        (context := (head.route.locate location).contextDerivation initial)
        P controls baseline frontier (.ref head.reference) σ τ relevant profile)
      (funded : Sponsored frontier [originalCallWorld controls .assignedComparison (.ref head.reference) baseline])
      (sameLocals : primitive.locals = input.locals)
      (included : ∀ index need, need ∈ primitive.available index → need ∈ input.available index) :
      WorldRigidBackwardTrace initial controls baseline frontier σ τ name levels node location prepared input
  | application
      {node : EndpointState sourceEnv U source (.app f a) assigned}
      {location : Located root node}
      {prepared : RigidFamilySpine.Prepared env U registry target name levels profile}
      {input : WorldAssignedQuery (registry := registry) (target := target)
        (context := location.contextDerivation initial) P controls baseline frontier node σ τ relevant profile}
      (domain : EndpointRef sourceEnv U source A (.sort u))
      (body : EndpointState sourceEnv U (A :: source) B (.sort v))
      (function : EndpointState sourceEnv U source f (.forallE A B))
      (argument : EndpointState sourceEnv U source a A)
      (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
      (hu : u.WF U) (hv : v.WF U)
      (route : PrefixRoute sourceEnv U source (.app f a) node
        (.app hu hv (.ref domain) body function argument result))
      (natural : WorldAssignedQuery (registry := registry) (target := target)
        (context := (route.locate location).contextDerivation initial) P controls baseline frontier
        (.app hu hv (.ref domain) body function argument result) σ τ relevant profile)
      (sameLocals : natural.locals = input.locals)
      (included : ∀ index need, need ∈ natural.available index → need ∈ input.available index)
      (step : WorldRigidPackedStep initial domain body function argument result hu hv (route.locate location)
        controls baseline frontier natural prepared)
      (tail : WorldRigidBackwardTrace initial controls baseline frontier σ τ name levels function
        (.appFunction (route.locate location)) step.nextPrepared step.next) :
      WorldRigidBackwardTrace initial controls baseline frontier σ τ name levels node location prepared input


/-- The finite application spine of the actual source expression. -/
inductive RigidApplicationSpine (name : Name) (levels : List VLevel) : VExpr → Prop where
  | constant : RigidApplicationSpine name levels (.const name levels)
  | app {function : VExpr} (before : RigidApplicationSpine name levels function) (argument : VExpr) :
      RigidApplicationSpine name levels (.app function argument)

theorem RigidApplicationSpine.mkApps
    (before : RigidApplicationSpine name levels expression) (arguments : List VExpr) :
    RigidApplicationSpine name levels (VExpr.mkApps expression arguments) := by
  induction arguments generalizing expression with
  | nil => exact before
  | cons argument rest ih => exact ih (before.app argument)

/-- This initializer consumes only all-budget banks and its actual incoming
assigned certificate. Every recursive step is on the strict function subtree
of the source application spine. Sponsorship stays at one immutable actual
original R world, and every selected frame keeps its inherited baseline. -/
theorem WorldAssignedQuery.initializeRigidSpine
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {sponsor : EndpointState sourceEnv U sponsorSource sponsorExpression sponsorAssigned}
    (initial : ContextDerivation sourceEnv U rootSource)
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (sponsorMember : originalCallWorld controls .expressionReindex sponsor baseline ∈ frontier)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (unary : ∀ budget, WorldBoundedUnaryAt env U registry strata P budget)
    (replay : ∀ budget, WorldBoundedReplayAt env U registry strata P budget)
    (spineSyntax : RigidApplicationSpine name levels expression)
    (node : EndpointState sourceEnv U source expression assigned) (location : Located root node)
    (prepared : RigidFamilySpine.Prepared env U registry target name levels (profile : Profile n))
    (input : WorldAssignedQuery (registry := registry) (target := target)
      (context := location.contextDerivation initial) P controls baseline frontier node σ τ relevant profile)
    (cost : (Closure.close (node.dependencyOrigin controls.ordered) baselineEnvironment).cost ≤
      (Closure.close (sponsor.dependencyOrigin controls.ordered) baselineEnvironment).cost) :
    Nonempty (WorldRigidBackwardTrace initial controls baseline frontier σ τ name levels
      node location prepared input) := by
  have lower {expression assigned}
      (child : EndpointState sourceEnv U source expression assigned)
      (bounded : (Closure.close (child.dependencyOrigin controls.ordered) baselineEnvironment).cost ≤
        (Closure.close (sponsor.dependencyOrigin controls.ordered) baselineEnvironment).cost)
      (phase : RichPhase) (phaseBound : phase.code < RichPhase.expressionReindex.code) :
      WorldBelow strata.rules.length (originalCallWorld controls phase child baseline)
        (originalCallWorld controls .expressionReindex sponsor baseline) := by
    apply original_child
    simp only [richSchedule]
    omega
  have pay {calls : List (World strata.rules.length)}
      (below : ∀ child ∈ calls, WorldBelow strata.rules.length child
        (originalCallWorld controls .expressionReindex sponsor baseline)) : Sponsored frontier calls := by
    intro child member
    exact ⟨_, sponsorMember, below child member⟩
  induction spineSyntax generalizing assigned n relevant with
  | constant =>
    let head := constantPrefix node
    have primitiveCost := Nat.le_trans (head.route.dependency_cost_le controls.ordered baselineEnvironment) cost
    have paid := pay (calls := [originalCallWorld controls .assignedComparison node baseline,
        originalCallWorld controls .assignedComparison (.ref head.reference) baseline]) (by
      intro child member
      rcases List.mem_cons.mp member with rfl | member
      · exact lower node cost _ (by decide)
      · cases List.mem_singleton.mp member
        exact lower (.ref head.reference) primitiveCost _ (by decide))
    obtain ⟨primitive, sameLocals, included⟩ := input.prefix initial location head.route controls baseline frontier
      henv input.certificate.formed paid replay
    exact ⟨.constant head primitive (fun world member => paid world (List.mem_cons_of_mem _ member)) sameLocals included⟩
  | @app f a before ih =>
    obtain ⟨⟨A, B, u, v, hu, hv, domain, body, function, argument, result, naturalLocation,
      prefixEq, _cost⟩, route, locationEq⟩ := applicationPrefix location
    obtain ⟨domain, rfl⟩ := naturalLocation.originalDomains.1
    let naturalNode := EndpointState.app hu hv (.ref domain) body function argument result
    have naturalCost := Nat.le_trans (route.dependency_cost_le controls.ordered baselineEnvironment) cost
    have paid := pay (calls := [originalCallWorld controls .assignedComparison node baseline,
        originalCallWorld controls .assignedComparison naturalNode baseline]) (by
      intro child member
      rcases List.mem_cons.mp member with rfl | member
      · exact lower node cost _ (by decide)
      · cases List.mem_singleton.mp member
        exact lower naturalNode naturalCost _ (by decide))
    obtain ⟨natural, sameLocals, included⟩ := input.prefix initial location route controls baseline frontier
      henv input.certificate.formed paid replay
    have appPaid := pay (calls := [originalCallWorld controls .fundamental naturalNode baseline]) (by
      intro child member
      cases List.mem_singleton.mp member
      exact lower naturalNode naturalCost _ (by decide))
    obtain ⟨step⟩ := natural.application initial domain body function argument result hu hv
      (route.locate location) controls baseline frontier prepared henv hscoped formed appPaid unary replay
    have functionCost : (Closure.close (function.dependencyOrigin controls.ordered) baselineEnvironment).cost ≤
        (Closure.close (sponsor.dependencyOrigin controls.ordered) baselineEnvironment).cost := by
      apply Nat.le_trans _ naturalCost
      apply Nat.le_trans _ (application_cost_le_captured _ _ _ _ _ _)
      exact Nat.le_of_lt (binder_other_cost (by simp) baselineEnvironment)
    obtain ⟨tail⟩ := ih function (.appFunction (route.locate location)) step.nextPrepared step.next functionCost
    exact ⟨.application domain body function argument result hu hv route natural sameLocals included step tail⟩


/-- The actual primitive constant reached by the finite trace. Displayed
levels remain the original caller levels; a genuine header may use its own
primitive seed, which is handled separately by the constant-header bridge. -/
structure WorldRigidPrimitiveSeed
    {registry : CanonicalHead.Registry} {target source : List VExpr}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (σ τ : Subst) (name : Name) (levels : List VLevel) where
  assigned : VExpr
  reference : EndpointRef sourceEnv U source (.const name levels) assigned
  location : Located root (.ref reference)
  primitive : reference.Primitive
  funded : Sponsored frontier [originalCallWorld controls .assignedComparison (.ref reference) baseline]
  rank : Nat
  support : Profile rank
  relevant : Bool
  prepared : RigidFamilySpine.Prepared env U registry target name levels support
  input : WorldAssignedQuery (registry := registry) (target := target)
    (context := location.contextDerivation initial) P controls baseline frontier (.ref reference)
    σ τ relevant support

/-- No new selection is made: projection follows the actual stored child at
each application, ending in the exact primitive state constructed by C. -/
noncomputable def WorldRigidBackwardTrace.primitiveSeed
    {registry : CanonicalHead.Registry} {target source : List VExpr}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {initial : ContextDerivation sourceEnv U rootSource}
    {controls : OriginalWorldControls strata sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
    {frontier : List (World strata.rules.length)}
    {node : EndpointState sourceEnv U source expression assigned} {location : Located root node}
    {prepared : RigidFamilySpine.Prepared env U registry target name levels (profile : Profile n)}
    {input : WorldAssignedQuery (registry := registry) (target := target)
      (context := location.contextDerivation initial) P controls baseline frontier node σ τ relevant profile}
    (trace : WorldRigidBackwardTrace (source := source) (P := P) initial controls baseline frontier
      σ τ name levels node location prepared input) :
    WorldRigidPrimitiveSeed (registry := registry) (target := target) (root := root) (source := source)
      (P := P) initial controls baseline frontier σ τ name levels := by
  induction trace with
  | constant head primitive funded sameLocals included =>
    rename_i assigned rank support flag node chosenLocation chosenPrepared chosenInput
    exact ⟨head.type, head.reference, head.route.locate chosenLocation, head.primitive, funded,
      _, _, _, chosenPrepared, primitive⟩
  | application domain body function argument result hu hv route natural sameLocals included step tail ih =>
    exact ih

@[simp] theorem WorldRigidBackwardTrace.primitiveSeed_relevant
    {registry : CanonicalHead.Registry} {target source : List VExpr}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {initial : ContextDerivation sourceEnv U rootSource}
    {controls : OriginalWorldControls strata sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
    {frontier : List (World strata.rules.length)}
    {node : EndpointState sourceEnv U source expression assigned} {location : Located root node}
    {prepared : RigidFamilySpine.Prepared env U registry target name levels (profile : Profile n)}
    {input : WorldAssignedQuery (registry := registry) (target := target)
      (context := location.contextDerivation initial) P controls baseline frontier node σ τ relevant profile}
    (trace : WorldRigidBackwardTrace (source := source) (P := P) initial controls baseline frontier
      σ τ name levels node location prepared input) :
    trace.primitiveSeed.relevant = relevant := by
  induction trace with
  | constant => rfl
  | application domain body function argument result hu hv route natural sameLocals included step tail ih =>
    exact ih

/-- Entry from an actual independent sort-typing original. The identity
frame, initial literal sort observation, assigned comparison, sponsorship,
and entire backwards computation are constructed internally. -/
theorem EndpointRef.rigidSpineOfWorldBanks
    (strata : EquationStratification env) (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx Γ (env.IsType U)) (context : ContextDerivation env U Γ)
    (original : EndpointRef env U Γ (VExpr.mkApps (.const name levels) arguments) (.sort level))
    (unary : ∀ budget, WorldBoundedUnaryAt env U registry strata (fun _ => True) budget)
    (replay : ∀ budget, WorldBoundedReplayAt env U registry strata (fun _ => True) budget) :
    let controls := worldAdequacyControls strata henv
    ∃ locals, ∃ frame : OriginalRichFrame env env U registry Γ context locals .id .id (fun _ => []),
    ∃ baseline : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered),
    let frontier := [originalCallWorld controls .expressionReindex (.ref original) baseline,
      originalCallWorld controls .expressionReindex (.ref original) baseline]
    ∃ flag, Relevant level flag ∧
    ∃ input : WorldAssignedQuery (registry := registry) (target := Γ) (context := context)
      (fun _ => True) controls baseline frontier (.ref original) .id .id true (Profile.sort (n := 1) flag),
      Nonempty (WorldRigidBackwardTrace context controls baseline frontier .id .id name levels
        (.ref original) .here (RigidFamilySpine.Prepared.terminal flag) input) := by
  dsimp only
  let controls := worldAdequacyControls strata henv
  let substitutions := Ctx.SubstEq.id henv formed
  obtain ⟨locals, frame, baseline, flag, relevant, answer, ⟨data⟩⟩ :=
    EndpointState.assignedSortQueryOfWorldBanks strata henv formed context original (.ref original)
      (.ofLocation .here context) replay 1
  let base := frame.captureBase substitutions
  let display := OriginalNestedDisplay.identity base (.ref original) (.ofLocation .here context)
  let frontier := [originalCallWorld controls .expressionReindex (.ref original) baseline,
    originalCallWorld controls .expressionReindex (.ref original) baseline]
  obtain ⟨input, _localsEq, _availableEq, _frameEq⟩ := WorldAssignedQuery.ofReply (display := display) henv controls baseline frontier
    answer data (Profile.HasType.sort flag)
  have trace := input.initializeRigidSpine (root := original) (sponsor := .ref original)
    context controls baseline frontier List.mem_cons_self henv hscoped formed unary replay
    (RigidApplicationSpine.mkApps .constant arguments) (.ref original) .here
    (RigidFamilySpine.Prepared.terminal flag) (Nat.le_refl _)
  exact ⟨locals, frame, baseline, flag, relevant, input, trace⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
