import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTemplateFormalDemand
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionFields
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionParameters

/-! Enrich the actual source family, execute its proper-major assigned
comparison, and extract the original extra parameter demand from that same
selected reply. The formal destination is built from the real declaration.
Literal two-domain header shapes remain explicit experiment conditions. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private projectionMajor_cost_lt from Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionReindex
open private from_left from Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

private theorem prependCalls (frontier : List (World count))
    (below : CallBelow count calls parents) : CallBelow count (frontier ++ calls) (frontier ++ parents) := by
  induction frontier with
  | nil => exact below
  | cons head tail ih => exact ih.cons head

private theorem constantLength
    (node : EndpointState sourceEnv U source (.const name levels) assigned)
    (context : ContextDerivation sourceEnv U source) (ordered : sourceEnv.Ordered)
    (lookup : sourceEnv.constants name = some info) : levels.length = info.uvars := by
  obtain ⟨ci, actual, _, count⟩ := HasType.const_inv ordered context.forget.defeq node.sound.defeq
  have same : ci = info := Option.some.inj (actual.symm.trans lookup)
  exact same ▸ count

private theorem familyLength
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead node) (context : ContextDerivation sourceEnv U source)
    (ordered : sourceEnv.Ordered) (origin : ProjectionParameterOrigin sourceEnv name head.info) :
    head.levels.length = origin.family.uvars := by
  have familyFormed : VExpr.WF sourceEnv U source
      (mkApps (.const name head.levels) (head.parameters ++ head.indices)) :=
    ⟨_, (EndpointRef.right head.major).typeFormation.node.sound.defeq⟩
  obtain ⟨_, constantTyped⟩ := VExpr.WF.of_mkApps ordered context.forget.defeq familyFormed
  obtain ⟨info, actual, _, count⟩ := HasType.const_inv ordered context.forget.defeq constantTyped
  have same : info = origin.family.toVConstant := Option.some.inj (actual.symm.trans origin.familyPresent)
  exact same ▸ count

private theorem fieldReference
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead node) (provenance : EndpointProvenance context node) :
    ∃ field : EndpointRef sourceEnv U source head.fieldType (.sort head.fieldLevel),
      head.field = .ref field := by
  set_option backward.isDefEq.respectTransparency false in
    exact (head.route.locate provenance.location).originalProjectionFields.1

section
variable
  {left : EndpointState leftEnv U leftSource (.proj name index leftValue) leftAssigned}
  {right : EndpointState rightEnv U rightSource (.proj name index rightValue) rightAssigned}
  (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
  {root : EndpointRef leftEnv U rootSource rootExpression rootType}
  {initial : ContextDerivation leftEnv U rootSource}
  {domain : EndpointRef leftEnv U leftSource E (.sort u)}
  {body : EndpointState leftEnv U (E :: leftSource) F (.sort v)}
  {function : EndpointState leftEnv U leftSource (.app (.const name leftHead.levels) a) (.forallE E F)}
  {argument : EndpointState leftEnv U leftSource p E}
  {result : EndpointState leftEnv U leftSource (F.inst p) (.sort v)}
  {hu : u.WF U} {hv : v.WF U}
  {location : Located root (.app hu hv (.ref domain) body function argument result)}
  {rightContext : ContextDerivation rightEnv U rightSource}
  (leftGraph : OriginalCaptureMap (common := common) (location.contextDerivation initial) leftRaw)
  (rightGraph : OriginalCaptureMap (common := common) rightContext rightRaw)
  (sameExpression : leftValue.subst leftRaw = rightValue.subst rightRaw)
  {strata : EquationStratification env} {P : VEnv → Prop}
  {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
  (leftControls : OriginalWorldControls strata leftEnv)
  (rightControls : OriginalWorldControls strata rightEnv)
  (leftWorld : WorldEnvironmentProvenance strata U leftEnvironment)
  (rightWorld : WorldEnvironmentProvenance strata U rightEnvironment)
  (frontier : List (World strata.rules.length))
  (leftFrame : OriginalCaptureRealization leftGraph env registry target leftLocals commonLeft commonRight leftAvailable)
  (rightFrame : OriginalCaptureRealization rightGraph env registry target rightLocals commonLeft commonRight rightAvailable)
  {substitutions : Ctx.SubstEq env U target (leftRaw.comp commonLeft) (leftRaw.comp commonRight) leftSource}
  {extraQuery : RichGradedResult leftEnv env U registry target argument leftLocals
    (leftRaw.comp commonLeft) leftAvailable (extra : Profile m)}
  {queryLevels : List VLevel} {queryWF : ∀ level ∈ queryLevels, level.WF U}
  (packet : WorldTwoParameterBackward initial domain body function argument result hu hv location
    leftFrame.frame substitutions P leftControls leftWorld frontier (profile : Profile n)
    relevant extraQuery info queryWF)

local notation "leftMajor" => OriginalNestedDisplay.recordBridgeReference leftGraph (EndpointRef.right leftHead.major) rfl
local notation "rightMajor" => OriginalNestedDisplay.recordBridgeReference rightGraph (EndpointRef.right rightHead.major) sameExpression


/-- The supplied packet contains the actual backward argument calls. Its
family descriptor, independent major reply, formal captures, and demanded
right observer are all constructed here from the lower banks. -/
theorem WorldTwoParameterBackward.compareAndExtractExtraWorld
    (signature : ConstantTelescope (info.type.instL queryLevels))
    (domains : signature.domains = [C,D])
    (resultSort : signature.result = .sort level) (relevance : Relevant level familyRelevant)
    (leftArguments : leftHead.parameters ++ leftHead.indices = [a,p])
    (route : PrefixRoute leftEnv U leftSource (.app (.app (.const name leftHead.levels) a) p)
      ((EndpointState.ref (EndpointRef.right leftHead.major)).typeFormation.node.cast
        (congrArg (mkApps (.const name leftHead.levels)) leftArguments) rfl)
      (.app hu hv (.ref domain) body function argument result))
    (queryEquivalent : List.Forall₂ (· ≈ ·) queryLevels leftHead.levels)
    (rightProvenance : EndpointProvenance rightContext right)
    (rightSignature : ConstantTelescope
      ((selectProjectionParameterOrigin rightControls.ordered rightHead.registered).family.type.instL rightHead.levels))
    (rightDomains : rightSignature.domains = [rightC,rightD])
    (sameCutoff : leftControls.cutoff = rightControls.cutoff)
    (sameFuel : leftControls.fuel = rightControls.fuel)
    (paid : Sponsored frontier [originalCallWorld leftControls .assignedComparison left leftWorld,
      originalCallWorld rightControls .assignedComparison right rightWorld])
    (leftData : WorldCallFrameData (P := P) (base := base) (caps := caps) (display := leftMajor)
      leftControls leftWorld frontier leftFrame)
    (rightData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := OriginalNestedDisplay.recordBridgeReference rightGraph (.right rightHead.major) rfl)
      rightControls rightWorld frontier rightFrame)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceClosed : ∀ source, source ≤ env → P source)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld leftControls .assignedComparison left leftWorld,
        originalCallWorld rightControls .assignedComparison right rightWorld]))
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld leftControls .assignedComparison left leftWorld,
        originalCallWorld rightControls .assignedComparison right rightWorld])) :
    ∃ answer : WorldTemplateAssignedReply (P := P) base caps leftMajor rightMajor commonLeft commonRight
        rightControls rightWorld frontier
        (.singleton (n := packet.first.request.rank+1)
          (.family ⟨name,queryLevels,familyRelevant,[packet.firstDeclared C,packet.secondDeclared D]⟩)),
    ∃ rightA rightP,
      rightHead.parameters ++ rightHead.indices = [rightA,rightP] ∧
      List.Forall₂ (· ≈ ·) leftHead.levels rightHead.levels ∧
    ∃ nominal : WorldRichFamilySourceRequest rightControls frontier (.right rightHead.major) registry target
        answer.reply.reply.answer.reply.locals (rightRaw.comp commonLeft)
        answer.reply.reply.answer.reply.available rightP (packet.secondDeclared D),
    ∃ query : RichFamilyArgumentQuery (.right rightHead.major) env registry target rightSource
        answer.reply.reply.answer.reply.locals (rightRaw.comp commonLeft)
        answer.reply.reply.answer.reply.available rightP extra,
    ∃ output : ControlledStoredQuery rightControls frontier (.observation query.query.observation),
      query.assigned = nominal.argument.assigned ∧
      HEq query.node nominal.argument.node ∧ HEq query.location nominal.argument.location ∧
      query.query.rank = nominal.argument.query.rank ∧
      query.query.footprint = nominal.argument.query.footprint ∧
      output.annotation.worlds = nominal.controlled.annotation.worlds ∧
      (∀ policy, query.query.observation.headDepth policy = nominal.argument.query.observation.headDepth policy) := by
  let application := EndpointState.app hu hv (.ref domain) body function argument result
  have appCost :
      (Closure.close (application.dependencyOrigin leftControls.ordered) leftEnvironment).cost ≤
      (Closure.close ((EndpointState.ref (.right leftHead.major)).typeFormation.node.dependencyOrigin
        leftControls.ordered) leftEnvironment).cost := by
    set_option backward.isDefEq.respectTransparency false in
      simpa only [EndpointState.dependencyOrigin_cast] using
        route.dependency_cost_le leftControls.ordered leftEnvironment
  have appBelow : WorldBelow strata.rules.length
      (originalCallWorld leftControls .fundamental application leftWorld)
      (originalCallWorld leftControls .assignedComparison left leftWorld) := by
    apply original_child (richSchedule_strict (Nat.lt_of_le_of_lt appCost
      (Nat.lt_of_le_of_lt ((EndpointState.ref (.right leftHead.major)).typeFormation_dependency_cost_le
        leftControls.ordered leftEnvironment) (projectionMajor_cost_lt leftHead leftControls.ordered leftEnvironment))) _ _) _ _ _ _ _
  have appPaid : Sponsored frontier [originalCallWorld leftControls .fundamental application leftWorld] := by
    intro child present
    cases List.mem_singleton.mp present
    obtain ⟨sponsor, member, below⟩ := paid
      (originalCallWorld leftControls .assignedComparison left leftWorld) (List.mem_cons_self ..)
    exact ⟨sponsor, member, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans appBelow below⟩
  have appCalls : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld leftControls .fundamental application leftWorld])
      (frontier ++ [originalCallWorld leftControls .assignedComparison left leftWorld,
        originalCallWorld rightControls .assignedComparison right rightWorld]) :=
    prependCalls frontier (from_left (by intro child member; cases List.mem_singleton.mp member; exact appBelow))
  have appBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld leftControls .fundamental application leftWorld]) :=
    fun calls below => unary calls (below.trans appCalls)
  have sourceBelow : leftEnv ≤ env := leftData.generation.erase.ambientGenerated.ambient.1.below
  have lookup : env.constants name = some info := sourceBelow.constants packet.origin.constant
  have actualLength := constantLength packet.firstFunction (location.contextDerivation initial)
    leftControls.ordered packet.origin.constant
  have queryLength : queryLevels.length = info.uvars :=
    (Lean4Lean.List.Forall₂.length_eq queryEquivalent).trans actualLength
  have typeClosed : info.type.Closed := leftControls.ordered.closedC packet.origin.constant
  have enrichedExists : Nonempty (WorldTwoParameterFamilyResult packet signature C D familyRelevant) :=
    packet.callerFamilyWorld signature domains resultSort relevance lookup notDefinition notNative notQuotient
      queryLength leftHead.levelsWF queryEquivalent typeClosed henv hscoped formed leftData.closed appPaid appBank
  obtain ⟨enriched⟩ := enrichedExists
  have comparison :
    ∃ answer : WorldTemplateAssignedReply (P := P) base caps leftMajor rightMajor commonLeft commonRight
        rightControls rightWorld frontier
        (.singleton (n := packet.first.request.rank+1)
          (.family ⟨name,queryLevels,familyRelevant,[packet.firstDeclared C,packet.secondDeclared D]⟩)),
    ∃ code : TemplateAssignedResult env U registry target (EndpointState.ref (EndpointRef.right leftHead.major))
        (EndpointState.ref (EndpointRef.right rightHead.major))
        answer.reply.reply.answer.reply.locals (leftRaw.comp commonLeft) (rightRaw.comp commonLeft)
        answer.reply.reply.answer.reply.available familyRelevant
        (.singleton (n := packet.first.request.rank+1)
          (.family ⟨name,queryLevels,familyRelevant,[packet.firstDeclared C,packet.secondDeclared D]⟩)),
    ∃ output : ControlledStoredQuery rightControls frontier (.certificate code.certificate),
      output.annotation.worlds ⊆ answer.data.query.annotation.worlds ∧
      (∀ policy, code.certificate.headDepth policy ≤ answer.reply.reply.answer.reply.query.observation.headDepth policy) ∧
      List.Forall₂ (· ≈ ·) leftHead.levels rightHead.levels ∧
      (∃ rightA rightP, rightHead.parameters ++ rightHead.indices = [rightA,rightP] ∧
        RankedData.RequestAdmission env U (relations env U registry packet.first.request.rank) target
          (packet.firstDeclared C) (a.subst (leftRaw.comp commonLeft)) (rightA.subst (rightRaw.comp commonLeft)) ∧
        RankedData.RequestAdmission env U (relations env U registry packet.first.request.rank) target
          (packet.secondDeclared D) (p.subst (leftRaw.comp commonLeft)) (rightP.subst (rightRaw.comp commonLeft))) ∧
      ∃ bound : extraQuery.rank ≤ packet.first.request.rank,
        ∀ atom ∈ (raiseProfile packet.first.request.rank bound extraQuery.raw).atoms,
          atom ∈ (packet.secondDeclared D).input.atoms :=
    WorldTwoParameterFamilyResult.compareIndependentMajorWorld
      (leftEnv := leftEnv) (U := U) (leftSource := leftSource) (name := name)
      (index := index) (leftValue := leftValue) (leftAssigned := leftAssigned) (rightEnv := rightEnv)
      (rightSource := rightSource) (rightValue := rightValue) (rightAssigned := rightAssigned) (rootSource := rootSource)
      (rootExpression := rootExpression) (rootType := rootType) (E := E) (u := u)
      (F := F) (v := v) (a := a) (p := p)
      (common := common) (leftRaw := leftRaw) (rightRaw := rightRaw) (env := env)
      (registry := registry) (target := target) (leftEnvironment := leftEnvironment) (rightEnvironment := rightEnvironment)
      (leftLocals := leftLocals) (commonLeft := commonLeft) (commonRight := commonRight) (leftAvailable := leftAvailable)
      (rightLocals := rightLocals) (rightAvailable := rightAvailable) (m := m) (extra := extra)
      (n := n) (profile := profile) (relevant := relevant) (info := info)
      (left := left) (right := right) (strata := strata) (P := P)
      (base := base) (caps := caps) (root := root) (initial := initial)
      (domain := domain) (body := body) (function := function) (argument := argument)
      (result := result) (hu := hu) (hv := hv) (location := location)
      (rightContext := rightContext) (substitutions := substitutions) (extraQuery := extraQuery) (queryLevels := queryLevels)
      (queryWF := queryWF) (C := C) (D := D) (familyRelevant := familyRelevant)
      leftHead rightHead leftGraph rightGraph sameExpression
      leftControls rightControls leftWorld rightWorld frontier leftFrame rightFrame packet signature enriched
      leftArguments route sameCutoff sameFuel paid leftData rightData henv hscoped formed bank
  obtain ⟨answer, code, ready, _, _, levels, ⟨rightA,rightP,rightArguments,_,_⟩, _⟩ := comparison
  let rightOrigin := selectProjectionParameterOrigin rightControls.ordered rightHead.registered
  have actualRightLength := familyLength rightHead rightContext rightControls.ordered rightOrigin
  let destination := rightOrigin.formalFamilyDestination rightHead.levelsWF actualRightLength rightSignature rightDomains
  have hasField : ∃ field : EndpointRef rightEnv U rightSource rightHead.fieldType (.sort rightHead.fieldLevel),
      rightHead.field = .ref field :=
    fieldReference (sourceEnv := rightEnv) (U := U) (source := rightSource)
      (name := name) (index := index) (major := rightValue) (assigned := rightAssigned)
      (node := right) (context := rightContext) rightHead rightProvenance
  obtain ⟨field, fieldEq⟩ := hasField
  refine ⟨answer,rightA,rightP,rightArguments,levels,?_⟩
  exact WorldTwoParameterBackward.rightExtraQueryFromMajorWorld
    (sourceEnv := leftEnv) (U := U) (source := leftSource) (env := env)
    (registry := registry) (target := target) (strata := strata) (P := P)
    (root := root) (initial := initial) (domain := domain) (body := body)
    (function := function) (argument := argument) (result := result) (hu := hu) (hv := hv)
    (location := location) (frame := leftFrame.frame) (substitutions := substitutions)
    (leftControls := leftControls) (leftWorld := leftWorld) (frontier := frontier)
    (extraQuery := extraQuery) (queryLevels := queryLevels) (queryWF := queryWF)
    (base := base) (caps := caps) (leftDisplay := leftMajor)
    (rightNode := right) (rightContext := rightContext)
    (commonLeft := commonLeft) (commonRight := commonRight)
    (familyRelevant := familyRelevant) (rightA := rightA) (rightP := rightP)
    (signature := rightSignature) (domains := rightDomains)
    packet C D left rightHead rightGraph sameExpression rightControls rightWorld answer code ready
    rightArguments rightOrigin destination field fieldEq paid henv hscoped formed sourceClosed
    notDefinition notNative bank unary


end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
