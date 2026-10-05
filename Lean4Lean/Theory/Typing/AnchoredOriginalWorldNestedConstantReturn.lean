import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedChargedWitness
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRichConstantApplication

/-! Return a constant through the actual enclosing canonical opening. The
child can itself contain canonical openings. Its saved source controls are
used unchanged; the enclosing charge is restored rather than flattened. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private def RichObs.CanonicalChildAnnotation
    {strata : EquationStratification env}
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (worlds : List (World strata.rules.length)) : Prop :=
  match query with
  | .canonicalConst (name := name) (levels := levels) (node := node) _ _ child _ => ∃ annotation : WorldObsProvenance strata child, annotation.worlds ⊆ worlds
  | _ => True

private theorem canonicalChild_cast
    {strata : EquationStratification env}
    {profile next : Profile n} (equal : profile = next)
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    {worlds : List (World strata.rules.length)}
    (present : query.CanonicalChildAnnotation worlds) :
    ((congrArg (fun p => RichObs sourceEnv env U registry target node locals σ p footprint)
      equal).mp query).CanonicalChildAnnotation worlds := by
  cases equal
  exact present

private theorem canonicalChild_lowerRaised
    {strata : EquationStratification env}
    {n N : Nat} {profile : Profile n} {bound : n ≤ N}
    (query : RichObs sourceEnv env U registry target node locals σ (raiseProfile N bound profile) footprint)
    {worlds : List (World strata.rules.length)}
    (present : query.CanonicalChildAnnotation worlds) : query.lowerRaised.CanonicalChildAnnotation worlds := by
  induction N generalizing n with
  | zero =>
    have same : n = 0 := by omega
    subst n
    exact present
  | succ N ih =>
    by_cases same : n = N + 1
    · subst n
      simp only [RichObs.lowerRaised, dif_pos]
      exact canonicalChild_cast (by rw [raiseProfile_self]) _ present
    · have previous : n ≤ N := by omega
      simp only [RichObs.lowerRaised, dif_neg same]
      apply ih
      trivial

private theorem WorldObsProvenance.canonicalChildAnnotation
    {strata : EquationStratification env}
    {query : RichObs sourceEnv env U registry target node locals σ profile footprint}
    (annotation : WorldObsProvenance strata query) : query.CanonicalChildAnnotation annotation.worlds :=
  match annotation with
  | .canonicalConst (name := name) (levels := levels) (node := node) _ _ _ _ child _ _ => ⟨child, fun _ member => List.mem_append_right _ member⟩
  | .castProfile equal child => canonicalChild_cast equal _ child.canonicalChildAnnotation
  | .lowerRaised child => canonicalChild_lowerRaised _ child.canonicalChildAnnotation
  | .var | .empty | .sort _ | .canonicalDelta .. | .rigidFamily .. | .code ..
    | .projection .. | .projectionSortable .. | .app .. | .route .. | .union .. | .view .. | .action ..
    | .select .. | .pad .. | .unpad .. | .family .. | .constructor .. | .legacy .. | .lam .. => True.intro
termination_by structural annotation

/-- The enclosing constant site comes from an actual original constant in
that owner's source. No lookup in another source is transported. -/
noncomputable def constantOriginAt
    (owner : CanonicalCodeOwner env registry strata ownerName)
    (node : EndpointState owner.selected.origin.source U source (.const name levels) assigned) :
    CanonicalConstOrigin env U registry strata name levels := by
  let head := constantPrefix node
  let closed := Classical.choice (EndpointRef.closedPrimitiveConstant head.reference rfl head.primitive)
  exact {
    ownerName := ownerName, owner := owner, info := closed.info, lookup := closed.lookup
    assignedLevels := closed.assignedLevels, assignedWF := closed.assignedWF
    levelsWF := closed.levelsWF, equivalent := closed.equivalent
    typeClosed := owner.selected.origin.ordered.closedC closed.lookup, site := closed.site }

/-- Universe alignment constructs its actual original in the enclosing
source from that source's own constant; no foreign lookup is assumed. -/
noncomputable def constantAtLevels
    (owner : CanonicalCodeOwner env registry strata ownerName)
    (node : EndpointState owner.selected.origin.source U source (.const name levels) assigned)
    (equal : EqUpToLevels U (.const name levels) (.const name nextLevels)) :
    EndpointRef owner.selected.origin.source U [] (.const name nextLevels)
      ((constantOriginAt owner node).info.type.instL (constantOriginAt owner node).assignedLevels) := by
  let origin := constantOriginAt owner node
  have raw := (EndpointState.ref origin.site).sound.defeq
  have comparison := raw.eqUpToLevels owner.selected.origin.ordered (by trivial) equal
  let original := Classical.choice (Derivation.reify
    (comparison.strong owner.selected.origin.ordered (by trivial)))
  exact .right original

/-- Restore the enclosing mask on the SAME graded source result. The new
opening site keeps the old source fuel, and is funded from the actual outer
recipe bound. Nested query annotations and their sponsors are retained. -/
theorem RichRecipeContext.returnConstantWorld
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target callerSource callerLocals callerLeft
      callerExpression relevant profile footprint}
    (pending : RichRecipeContext input recipe)
    {caller : EndpointState callerEnv U callerSource callerExpression callerAssigned}
    (controls : OriginalWorldControls input.strata callerEnv)
    (baseline : WorldEnvironmentProvenance input.strata U environment)
    (frontier : List (World input.strata.rules.length))
    (callerReady : ControlledStoredQuery controls frontier
      (.certificate (RichCert.recipe (node := caller) recipe)))
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (constant : EndpointState input.owner.selected.origin.source U source (.const name levels) assigned)
    (result : RichGradedResult input.owner.selected.origin.source env U registry target
      (.ref (constantOriginAt input.owner constant).site) [] input.realization (fun _ => []) requested)
    (resultReady : ControlledStoredQuery
      (canonicalQueryControls input.owner.selected
        (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control))
      frontier (.observation result.observation))
    (destination : EndpointState destinationEnv U destinationSource (.const name levels) destinationAssigned)
    (locals : List Nat) (σ : Subst) (available : Valuation) :
    ∃ next : RichGradedResult destinationEnv env U registry target destination locals σ available requested,
    ∃ ready : ControlledStoredQuery controls frontier (.observation next.observation),
      next.rank = result.rank ∧ HEq next.raw result.raw ∧
      ready.annotation.worlds =
        (WorldQuerySite.empty (registry := registry) (target := target)
          (canonicalQueryControls input.owner.selected
            (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control))
          (EndpointProvenance.ofLocation .here .nil) input.realization
          (node := .ref (constantOriginAt input.owner constant).site)).worlds ++
        resultReady.annotation.worlds := by
  let origin := constantOriginAt input.owner constant
  let childControls := canonicalQueryControls input.owner.selected
    (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control)
  let packet := CanonicalConstSitePacket.ofOrigin origin input.realization
    result.observation result.resources
  let next : RichGradedResult destinationEnv env U registry target destination locals σ available requested := {
    rank := result.rank, bound := result.bound, raw := result.raw, footprint := []
    observation := packet.observation destination locals σ
    adapter := result.adapter
    resources := fun _ _ member => nomatch member
    live := result.live }
  let annotation : WorldObsProvenance input.strata next.observation :=
    .canonicalConst origin input.realization result.observation result.resources resultReady.annotation
      childControls (EndpointProvenance.ofLocation .here .nil)
  have bounded : WithinAbove controls.cutoff controls.fuel
      (headDepth input.owner.selected.ordinal
        (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control)) := by
    intro control active
    have original := callerReady.within control active
    simp only [StoredOriginalQuery.headDepth, RichCert.headDepth] at original
    have bound := Nat.le_trans (pending.rootDepth (stratifiedHeadPolicy (input.strata.headOrdinal registry) control)) original
    simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth, RichCert.stratifiedDepth,
      RichRecipeRootInput.recipe, RichCodeRecipe.headDepth, stratifiedHeadPolicy,
      input.owner.headOrdinal_eq, headDepth] using bound
  have sitePaid : Sponsored frontier
      (WorldQuerySite.empty (registry := registry) (target := target) childControls (EndpointProvenance.ofLocation .here .nil)
        input.realization (node := .ref origin.site)).worlds := by
    intro world member
    change world ∈ [originalCallWorld childControls .fundamental (.ref origin.site) .nil] at member
    cases List.mem_singleton.mp member
    have lower : WorldBelow input.strata.rules.length
        (originalCallWorld childControls .fundamental (.ref origin.site) .nil)
        (originalCallWorld controls .fundamental caller baseline) := by
      apply Below.root
        (EquationStratifiedFuel.openingDecrease input.owner.selected.ordinal_pos input.owner.selected.ordinal_le
          controls.cutoffBound bounded controls.ordered.constantCount
          (richSchedule .fundamental (Closure.close (caller.dependencyOrigin controls.ordered) environment).cost)
          input.owner.selected.origin.ordered.constantCount
          (richSchedule .fundamental
            (Closure.close ((EndpointState.ref origin.site).dependencyOrigin input.owner.selected.origin.ordered) []).cost))
      intro value member
      cases member
    obtain ⟨sponsor, present, paid⟩ := callerPaid _ (List.mem_singleton_self _)
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less input.strata.rules.length)
      EquationControlMeasure.less_trans lower paid⟩
  let ready : ControlledStoredQuery controls frontier (.observation next.observation) := {
    annotation := annotation
    within := by
      intro control active
      change (packet.observation destination locals σ).stratifiedDepth
        (input.strata.headOrdinal registry) control ≤ controls.fuel control
      simp only [RichObs.stratifiedDepth, CanonicalConstSitePacket.observation_headDepth,
        packet, CanonicalConstSitePacket.ofOrigin, origin, constantOriginAt,
        stratifiedHeadPolicy, input.owner.headOrdinal_eq]
      exact EquationStratifiedFuel.rebuild input.owner.selected.ordinal_pos bounded resultReady.within control active
    sponsored := sitePaid.merge resultReady.sponsored }
  exact ⟨next, ready, rfl, HEq.rfl, rfl⟩

/-- Two nested openings execute the inner equality in the saved outer source
bank and return its SAME query under the outer charge. The inner bound comes
from the actual retained canonical-constant input; the outer bound comes
from the actual recipe. No flattened-mask premise is accepted. -/
theorem RichRecipeContext.reindexNestedConstantFunctionWorld
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target callerSource callerLocals callerLeft
      callerExpression relevant profile footprint}
    (pending : RichRecipeContext input recipe)
    {caller : EndpointState callerEnv U callerSource callerExpression callerAssigned}
    (controls : OriginalWorldControls input.strata callerEnv)
    (baseline : WorldEnvironmentProvenance input.strata U environment)
    (frontier : List (World input.strata.rules.length))
    (callerReady : ControlledStoredQuery controls frontier
      (.certificate (RichCert.recipe (node := caller) recipe)))
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (sourceCaller : EndpointState input.owner.selected.origin.source U sourceCallerContext
      sourceCallerExpression sourceCallerAssigned)
    (sourceBaseline : WorldEnvironmentProvenance input.strata U sourceEnvironment)
    (inner : CanonicalConstSitePacket env U registry target input.strata name sourceLevels (Profile.fn key output))
    (innerConstant : EndpointState input.owner.selected.origin.source U innerContext
      (.const name sourceLevels) innerAssigned)
    (innerLocals : List Nat) (innerSubstitution : Subst)
    (innerReady : ControlledStoredQuery
      (canonicalQueryControls input.owner.selected
        (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control))
      frontier (.observation (inner.observation innerConstant innerLocals innerSubstitution)))
    (sourcePaid : Sponsored frontier [originalCallWorld
      (canonicalQueryControls input.owner.selected
        (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control))
      .fundamental sourceCaller sourceBaseline])
    (sourceAvailable : P inner.owner.selected.origin.source)
    (sourceBank : WorldBoundedUnaryCallBank env U registry input.strata P
      (frontier ++ [originalCallWorld
        (canonicalQueryControls input.owner.selected
          (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control))
        .fundamental sourceCaller sourceBaseline]))
    (formed : OnCtx target (env.IsType U))
    (equal : EqUpToLevels U (.const name sourceLevels) (.const name levels))
    (destination : EndpointState destinationEnv U destinationSource (.const name levels) destinationAssigned)
    (locals : List Nat) (σ : Subst) (available : Valuation) :
    ∃ next : RichGradedResult destinationEnv env U registry target destination locals σ available (Profile.fn key output),
      Nonempty (ControlledStoredQuery controls frontier (.observation next.observation)) := by
  let sourceControls := canonicalQueryControls input.owner.selected
    (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control)
  rcases innerReady with ⟨annotation, within, sponsored⟩
  have bounded : WithinAbove sourceControls.cutoff sourceControls.fuel inner.chargeDepth := by
    intro control active
    have bound := within control active
    simpa only [StoredOriginalQuery.headDepth, CanonicalConstSitePacket.observation_headDepth,
      stratifiedHeadPolicy, inner.owner.headOrdinal_eq, CanonicalConstSitePacket.chargeDepth,
      RichObs.stratifiedDepth, headDepth] using bound
  obtain ⟨child, included⟩ := annotation.canonicalChildAnnotation
  have childPaid : Sponsored frontier child.worlds := fun world member => sponsored world (included member)
  let constant := EndpointState.ref (constantAtLevels input.owner innerConstant equal)
  obtain ⟨returned, ⟨returnedReady⟩⟩ := inner.reindexFunctionLevelsWorld equal child formed
    sourceCaller sourceControls sourceBaseline frontier sourcePaid sourceAvailable childPaid bounded sourceBank
    (.ref (constantOriginAt input.owner constant).site) [] input.realization (fun _ => [])
  obtain ⟨next, ready, _, _, _⟩ := pending.returnConstantWorld controls baseline frontier callerReady callerPaid
    constant returned returnedReady destination locals σ available
  exact ⟨next, ⟨ready⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
