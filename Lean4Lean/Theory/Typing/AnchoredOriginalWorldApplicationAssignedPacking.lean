import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationAssignedDemand
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationPack
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldArgumentSupplyControl
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryOperations

/-! Assigned-code enrichment is assembled into the actual application Pi
request. The original body certificate and finite binder pack are retained,
while both the extra value observer and its independent assigned-code seed
are included. An empty value profile does not remove that seed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private raiseCertificateControlled transportControlledCertificate from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationPack
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

private theorem raiseRequestControlled
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (query : RichGradedResult sourceEnv env U registry target node locals σ available (input : Profile n))
    (ready : ControlledStoredQuery controls frontier (.observation query.observation)) (bound : n ≤ N) :
    Nonempty (ControlledStoredQuery controls frontier
      (.observation (query.raiseRequest henv hscoped formed bound).observation)) :=
  ready.raise (Nat.le_max_left _ _)

private theorem unionControlled
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (left : RichGradedResult sourceEnv env U registry target node locals σ available (p : Profile n))
    (right : RichGradedResult sourceEnv env U registry target node locals σ available (q : Profile n))
    (leftReady : ControlledStoredQuery controls frontier (.observation left.observation))
    (rightReady : ControlledStoredQuery controls frontier (.observation right.observation)) :
    Nonempty (ControlledStoredQuery controls frontier
      (.observation (left.union henv hscoped formed right).observation)) := by
  obtain ⟨a⟩ := leftReady.raise (Nat.le_max_left left.rank right.rank)
  obtain ⟨b⟩ := rightReady.raise (Nat.le_max_right left.rank right.rank)
  refine ⟨⟨.union a.annotation b.annotation, ?_, a.sponsored.merge b.sponsored⟩⟩
  intro control active
  simpa only [StoredOriginalQuery.headDepth, RichGradedResult.union,
    RichGradedResult.raiseTo, RichObs.headDepth] using
    (Nat.max_le.mpr ⟨a.within control active, b.within control active⟩)

/-- Pack the actual finite replacements while retaining controls on the very
observer returned by the recursion. No per-need semantic answer is supplied. -/
theorem binderPackArgumentQueryControlled
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (pack : BinderPack n input required outside)
    (supply : RichArgumentSupply sourceEnv env U registry target node locals σ available required.localNeeds)
    (ready : supply.Controlled controls frontier) :
    ∃ query : RichGradedResult sourceEnv env U registry target node locals σ available input,
      Nonempty (ControlledStoredQuery controls frontier (.observation query.observation)) := by
  have get := fun need (member : (0, need) ∈ required) =>
    supply.lookup_controlled ready (Footprint.mem_localNeeds.mpr member)
  clear supply ready
  induction pack with
  | nil =>
    refine ⟨.empty, ⟨⟨.empty, ?_, ?_⟩⟩⟩
    · intro control active
      simp only [StoredOriginalQuery.headDepth, RichGradedResult.empty,
        RichObs.headDepth, SortableObs.headDepth, Obs.headDepth]
      exact Nat.zero_le _
    · intro world member
      cases member
  | external index need rest ih =>
    exact ih (fun wanted member => get wanted (List.mem_cons_of_mem _ member))
  | «local» need bound rest ih =>
    rw [show need.atGrade n = raiseProfile n bound need.profile from dif_pos bound]
    obtain ⟨tail, ⟨tailReady⟩⟩ := ih (fun wanted member => get wanted (List.mem_cons_of_mem _ member))
    obtain ⟨query, ⟨queryReady⟩⟩ := get need List.mem_cons_self
    let head := query.raiseRequest henv hscoped formed bound
    obtain ⟨headReady⟩ := raiseRequestControlled henv hscoped formed query queryReady bound
    obtain ⟨outputReady⟩ := unionControlled henv hscoped formed head tail headReady tailReady
    exact
      (show ∃ output : RichGradedResult sourceEnv env U registry target node locals σ available
        ((raiseProfile n bound need.profile).union _),
        Nonempty (ControlledStoredQuery controls frontier (.observation output.observation)) from
        ⟨head.union henv hscoped formed tail, ⟨outputReady⟩⟩)

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  {initial : ContextDerivation sourceEnv U rootSource}
  {domain : EndpointRef sourceEnv U source A (.sort u)}
  {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
  {function : EndpointState sourceEnv U source f (.forallE A B)}
  {argument : EndpointState sourceEnv U source a A}
  {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
  {hu : u.WF U} {hv : v.WF U}
  {location : Located root (.app hu hv (.ref domain) body function argument result)}
  {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}

/-- The actual argument F call is a proper child of the application at the
selected frame. It computes both typing support and its original certificate. -/
private theorem applicationArgumentWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame.frame.raw controls)
    (frontier : List (World strata.rules.length))
    (frameReady : generated.Controlled frontier)
    (frameReplayable : generated.Replayable)
    (frameCompatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (frameHereditary : generated.Hereditary frontier)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (query : RichObs sourceEnv env U registry target argument locals (raw.comp commonLeft) input footprint)
    (resources : footprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.observation query))
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental
      (.app hu hv (.ref domain) body function argument result) baseline])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline])) :
    ∃ answer : RichComputationalValue sourceEnv env U registry target argument locals
        (raw.comp commonLeft) (raw.comp commonRight) available input,
      Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)) := by
  obtain ⟨data⟩ := WorldUnaryFrameData.ofGenerated frame.frame generated frameReady
    frameReplayable frameCompatible frameHereditary
  have reserve := application_cost_le_captured (domain.dependencyOrigin controls.ordered)
    (body.dependencyOrigin controls.ordered) (function.dependencyOrigin controls.ordered)
    (argument.dependencyOrigin controls.ordered) (result.dependencyOrigin controls.ordered)
    (frame.frame.dependencyEnvironment controls.ordered)
  have smaller : (Closure.close (argument.dependencyOrigin controls.ordered)
      (frame.frame.dependencyEnvironment controls.ordered)).cost <
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin controls.ordered)
        baselineEnvironment).cost :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (binder_other_cost (by simp) _) reserve)
      (Nat.mul_le_mul_left _ (Nat.add_le_add_left capacity 1))
  have child : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental argument generated.environment)
      (originalCallWorld controls .fundamental (.app hu hv (.ref domain) body function argument result) baseline) :=
    smaller_root (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans
      (EquationControlMeasure.scheduleDecrease (richSchedule_strict smaller _ _) _ _ _ _) covered
  have funded : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental argument generated.environment])
      (frontier ++ [originalCallWorld controls .fundamental (.app hu hv (.ref domain) body function argument result) baseline]) := by
    have lower := split_call (calls := [originalCallWorld controls .fundamental argument generated.environment])
      (fun node member => by cases List.mem_singleton.mp member; exact child)
    clear bank frameReady ready sponsored data frameHereditary
    induction frontier with
    | nil => exact lower
    | cons world rest ih => exact ih.cons world
  have argumentSponsored : Sponsored frontier [originalCallWorld controls .fundamental argument generated.environment] := by
    intro world member
    cases List.mem_singleton.mp member
    obtain ⟨sponsor, present, bound⟩ := sponsored _ (List.mem_singleton_self _)
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans child bound⟩
  obtain ⟨answer, answerReady, _⟩ := (bank _ funded).computational argument
    (.ofLocation (.appArgument location) initial) controls frame.frame generated.environment
    generated.environment frontier (Nat.le_refl _) (Covered.refl _) rfl argumentSponsored data
    closed formed frame.substitutions query resources ready
  exact ⟨answer, answerReady⟩

/-- Enrich the actual backward body packet with both an extra argument
observer and an independently retained assigned-code demand. The extra raw
input and original binder input are kept in one key. Its support comes from
actual argument F and formation F/R, including when the value profile is empty. -/
theorem ApplicationBackwardQueries.piRequestAssignedDemandWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame.frame.raw controls)
    (frontier : List (World strata.rules.length))
    (frameReady : generated.Controlled frontier)
    (frameReplayable : generated.Replayable)
    (frameCompatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (frameHereditary : generated.Hereditary frontier)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds)
    (packet : ApplicationBackwardQueries initial domain body function argument result hu hv location
      frame.frame frame.substitutions controls.ordered relevant (profile : Profile n))
    (headReady : ∀ query ∈ packet.reply.answer.reply.realization.frame.raw.storedQueries,
      Nonempty (ControlledStoredQuery controls frontier query))
    (bodyReady : ControlledStoredQuery controls frontier (.certificate packet.certificate))
    (supply : RichArgumentSupply sourceEnv env U registry target argument locals (raw.comp commonLeft)
      available packet.footprint.localNeeds)
    (supplyReady : supply.Controlled controls frontier)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (extraQuery : RichGradedResult sourceEnv env U registry target argument locals (raw.comp commonLeft)
      available (extra : Profile m))
    (extraReady : ControlledStoredQuery controls frontier (.observation extraQuery.observation))
    (seed : RichCert sourceEnv env U registry target argument.typeFormation.node
      locals (raw.comp commonLeft) true (seedSupport : Profile k) seedFootprint)
    (seedResources : seedFootprint.Available available)
    (seedReady : ControlledStoredQuery controls frontier (.certificate seed))
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental
      (.app hu hv (.ref domain) body function argument result) baseline])
    (unaryBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline]))
    (replayBank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline])) :
    ∃ output : GeneratedApplicationPackedRequest domain body argument hu hv env registry target
        locals (raw.comp commonLeft) available relevant profile,
      Nonempty (output.Controlled controls frontier) ∧
      ∃ seedBound : k ≤ output.request.rank,
        (∀ atom ∈ (raiseProfile output.request.rank seedBound seedSupport).atoms,
          atom ∈ output.request.support.atoms) ∧
      ∃ extraBound : extraQuery.rank ≤ output.request.rank,
        (∀ atom ∈ (raiseProfile output.request.rank extraBound extraQuery.raw).atoms,
          atom ∈ output.request.key.input.atoms) ∧
      ∃ originalPack : RichTypedBinderPack domain env registry target locals (raw.comp commonLeft) available
          (a.subst (raw.comp commonLeft)) (a.subst (raw.comp commonRight)) packet.footprint n,
      ∃ oldBound : originalPack.rank ≤ output.request.rank,
        HEq output.request.key.input
          ((raiseProfile output.request.rank oldBound originalPack.input).union
            (raiseProfile output.request.rank extraBound extraQuery.raw)) := by
  obtain ⟨frameData⟩ := WorldUnaryFrameData.ofGenerated frame.frame generated frameReady
    frameReplayable frameCompatible frameHereditary
  obtain ⟨packed, ⟨packedReady⟩⟩ := packet.typedPackWorld (n := n) controls generated.environment baseline
    capacity covered frameData headReady henv hscoped formed closed sponsored unaryBank
  obtain ⟨oldArgument, ⟨oldReady⟩⟩ :=
    binderPackArgumentQueryControlled henv hscoped formed packed.pack supply supplyReady
  obtain ⟨extraValue, ⟨extraValueReady⟩⟩ := applicationArgumentWorld (location := location)
    controls frame generated frontier frameReady frameReplayable frameCompatible frameHereditary baseline capacity covered formed closed
    extraQuery.observation extraQuery.resources extraReady sponsored unaryBank
  let N := max packed.rank (max extraQuery.rank k)
  have oldBound : packed.rank ≤ N := Nat.le_max_left _ _
  have extraBound : extraQuery.rank ≤ N := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have seedBound : k ≤ N := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have outputBound : n ≤ N := Nat.le_trans packed.bound oldBound
  obtain ⟨extraCertificate, ⟨extraCertificateReady⟩⟩ :=
    raiseCertificateControlled extraValueReady extraBound
  obtain ⟨raisedSeed, ⟨raisedSeedReady⟩⟩ := raiseCertificateControlled seedReady seedBound
  let supplemental := (raiseProfile N extraBound extraValue.support).union
    (raiseProfile N seedBound seedSupport)
  let supplementalCertificate := RichCert.union extraCertificate raisedSeed
  have supplementalResources : (extraValue.footprint ++ seedFootprint).Available available :=
    fun i need member => (List.mem_append.mp member).elim (extraValue.resources i need) (seedResources i need)
  obtain ⟨supplementalFootprint, supplementalDomain, supplementalAvailable, supplementalMeaning, ⟨supplementalReady⟩⟩ :=
    applicationAssignedDemandWorld (location := location) controls frame generated frontier frameReady frameReplayable frameCompatible frameHereditary baseline
      capacity covered henv hscoped formed closed supplementalCertificate supplementalResources
      (extraCertificateReady.certUnion raisedSeedReady) sponsored unaryBank replayBank
  obtain ⟨oldDomain, ⟨oldDomainReady⟩⟩ := raiseCertificateControlled packedReady oldBound
  let support := (raiseProfile N oldBound packed.support).union supplemental
  let input := (raiseProfile N oldBound packed.input).union (raiseProfile N extraBound extraQuery.raw)
  let domainCertificate := RichCert.union oldDomain supplementalDomain
  let domainReady := oldDomainReady.certUnion supplementalReady
  have domainResources : (packed.footprint ++ supplementalFootprint).Available available :=
    fun i need member => (List.mem_append.mp member).elim (packed.resources i need) (supplementalAvailable i need)
  have supportCode : TypeRelated env U registry target (A.subst (raw.comp commonLeft))
      (A.subst (raw.comp commonLeft)) support := by
    apply TypeRelated.of_singletons
    intro atom member
    exact (List.mem_append.mp member).elim
      (fun member => (packed.code.raise henv oldBound).singleton member)
      (fun member => supplementalMeaning.singleton member)
  have oldTyped := (Profile.HasType.raise oldBound packed.typed).enlarge
    (Profile.le_union_left _ _) domainCertificate.formed.wf_value
  have extraTyped := (Profile.HasType.raise extraBound extraValue.typed).enlarge
    (Profile.le_trans (Profile.le_union_left _ _) (Profile.le_union_right _ _)) domainCertificate.formed.wf_value
  have typed : input.HasType support := oldTyped.union extraTyped
  have oldRelated := (packed.related.raise henv oldBound).left_diagonal.retag henv oldTyped supportCode
  have extraRelated := (extraValue.related.raise henv extraBound).left_diagonal.retag henv extraTyped supportCode
  have argumentRelated := oldRelated.union extraRelated
  let rawExtra : RichGradedResult sourceEnv env U registry target argument locals (raw.comp commonLeft)
      available extraQuery.raw := {
    rank := extraQuery.rank, bound := Nat.le_refl _, raw := extraQuery.raw, footprint := extraQuery.footprint
    observation := extraQuery.observation
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := extraQuery.resources, live := extraValue.related.live henv hscoped formed }
  let first := oldArgument.raiseRequest henv hscoped formed oldBound
  let second := rawExtra.raiseRequest henv hscoped formed extraBound
  obtain ⟨firstReady⟩ := raiseRequestControlled henv hscoped formed oldArgument oldReady oldBound
  obtain ⟨secondReady⟩ := raiseRequestControlled henv hscoped formed rawExtra extraReady extraBound
  let argumentQuery := first.union henv hscoped formed second
  obtain ⟨argumentReady⟩ := unionControlled henv hscoped formed first second firstReady secondReady
  let key : Key N := ⟨A.subst (raw.comp commonLeft), a.subst (raw.comp commonLeft), input⟩
  have rawValue := (argument.sound.defeq.mono frameData.ambient.below).substDF henv
    frame.substitutions.wf formed frame.substitutions.left
  let guard : LambdaGuard env U registry target (raw.comp commonLeft) A key support :=
    ⟨typed, domainCertificate.formed, .refl, supportCode,
      ⟨rawValue, rawValue, support, typed, domainCertificate.formed, supportCode,
        argumentRelated, argumentRelated⟩⟩
  obtain ⟨raisedBody, ⟨raisedBodyReady⟩⟩ := raiseCertificateControlled bodyReady outputBound
  have positions : packet.reply.answer.reply.locals = Locals.push locals := by
    exact packet.reply.answer.reply.locals_eq
  have realization : (Subst.id.cons (a.subst .id)).comp (raw.comp commonLeft) =
      (raw.comp commonLeft).cons (a.subst (raw.comp commonLeft)) := by
    funext i
    cases i <;> simp only [Subst.comp, Subst.cons, subst_id] <;> rfl
  obtain ⟨bodyCode, ⟨bodyCodeReady⟩⟩ := transportControlledCertificate raisedBodyReady positions realization
  let rowPack := packed.pack.raise oldBound
  have rowCovered : ∀ atom ∈ (raiseProfile N oldBound packed.input).atoms, atom ∈ key.input.atoms :=
    fun _ member => List.mem_append_left _ member
  let rows : RichRows sourceEnv env U registry target (.ref domain) body locals (raw.comp commonLeft)
      relevant support [(key, raiseProfile N outputBound profile)] (packed.outside ++ []) :=
    .cons guard bodyCode rowPack rowCovered .nil
  let request : GeneratedApplicationPiRequest domain body hu hv env registry target locals
      (raw.comp commonLeft) available a relevant profile := {
    rank := N, bound := outputBound, key := key, support := support
    footprint := (packed.footprint ++ supplementalFootprint) ++ (packed.outside ++ [])
    certificate := .pi hu hv domainCertificate PiGuard.literal rows
    resources := fun i need member => (List.mem_append.mp member).elim
      (domainResources i need)
      (fun member => packed.external i need (by simpa only [List.append_nil] using member))
    admitted := guard.anchor, anchor_eq := rfl }
  let output : GeneratedApplicationPackedRequest domain body argument hu hv env registry target locals
      (raw.comp commonLeft) available relevant profile := {
    request := request, argumentQuery := argumentQuery
    domainFootprint := packed.footprint ++ supplementalFootprint
    domainCertificate := domainCertificate, domainResources := domainResources
    inputTyped := typed, domainRelated := supportCode }
  have requestReady : ControlledStoredQuery controls frontier (.certificate request.certificate) := by
    refine ⟨.pi hu hv domainCertificate PiGuard.literal rows domainReady.annotation
      (.cons guard bodyCode rowPack rowCovered .nil bodyCodeReady.annotation .nil), ?_, ?_⟩
    · intro control active
      simpa only [StoredOriginalQuery.headDepth, request, rows, domainCertificate,
        RichCert.headDepth, RichRows.headDepth, Nat.max_zero] using
        (Nat.max_le.mpr ⟨domainReady.within control active, bodyCodeReady.within control active⟩)
    · change Sponsored frontier (domainReady.annotation.worlds ++ (bodyCodeReady.annotation.worlds ++ []))
      simpa only [List.append_nil] using domainReady.sponsored.merge bodyCodeReady.sponsored
  exact ⟨output, ⟨⟨requestReady, argumentReady, domainReady⟩⟩,
    seedBound, (fun _ member => List.mem_append_right _ (List.mem_append_right _ member)),
    extraBound, (fun _ member => List.mem_append_right _ member), packed, oldBound, HEq.rfl⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
