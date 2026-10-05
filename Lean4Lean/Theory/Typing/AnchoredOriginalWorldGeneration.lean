import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteProvenance
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBindReservation
import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureGeneration

/-! A minimal positive world-annotated producer. The indices retain the
SAME raw semantic frame; erasure is the existing source-generation proof.
Empty, bind, capture, merge, and annotated identity bases are covered.
History introduction retains a recursive prior, seed, route-frame and owner
annotation, together with route-indexed inputs. Reserve labels are computed from the
actual route endpoints. Bounds on query controls and sponsorship remain
separate obligations; this datatype asserts provenance, not semantic answers. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

private noncomputable def historyLedgerOfEntries
    {env : VEnv} {strata : EquationStratification env}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (_entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available ownerInitial rawCapture leftValue rightValue)
    (ownerControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata headerEnv)
    (initial : WorldEnvironmentProvenance strata U ownerInitial)
    (prior : WorldEnvironmentProvenance strata U previous)
    (route : WorldEnvironmentProvenance strata U reserve) :
    WorldEnvironmentProvenance strata U
      (groupCaptureHistoryReserve field major domain ownerControls.ordered headerControls.ordered
        ownerInitial previous reserve) :=
  WorldEnvironmentProvenance.groupHistory field major domain ownerControls headerControls initial prior route

private theorem rawOwners
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available ownerInitial rawCapture leftValue rightValue)
    (ordered : sourceEnv.Ordered) (declared : Closure) :
    (richGroupedEntriesRaw entries).ownerClosures ordered declared =
      entries.map (fun entry => Closure.bundle (entry.owner.dependencyClosure ordered ownerInitial) declared) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    simp only [richGroupedEntriesRaw, RawRichGroupEntries.ownerClosures,
      RichGroupedCaptureEntry.toRaw, RawRichGroupEntry.owner, List.map_cons, ih]

inductive WorldGenerated (strata : EquationStratification env) (P : VEnv → Prop)
    (base : OriginalCaptureBase env U registry target) :
    (commonCaps : CaptureCaps) →
    {common : List VExpr} → (commonLeft commonRight : Subst) →
    {sourceEnv : VEnv} → {source : List VExpr} →
    {context : ContextDerivation sourceEnv U source} → {raw : Subst} →
    {locals : List Nat} → {σ τ : Subst} → {available : Valuation} →
    OriginalCaptureMap (common := common) context raw →
    RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available → OriginalWorldControls strata sourceEnv → Type where
  | merge
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {left : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable}
      {right : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable}
      (first : WorldGenerated strata P base commonCaps commonLeft commonRight graph left controls)
      (second : WorldGenerated strata P base commonCaps commonLeft commonRight graph right controls) :
      WorldGenerated strata P base commonCaps commonLeft commonRight graph (.merge left right) controls
  | identity (ambient : base.frame.Ambient) (sources : base.frame.raw.AllSources P)
      (controls : OriginalWorldControls strata base.sourceEnv)
      (environment : WorldEnvironmentProvenance strata U (base.frame.dependencyEnvironment controls.ordered)) : WorldGenerated strata P base base.initialCaps base.left base.right
      (.identity base.context) base.frame.raw controls
  | empty (common : List VExpr) (commonLeft commonRight : Subst) (below : sourceEnv ≤ env) (source : P sourceEnv) (controls : OriginalWorldControls strata sourceEnv) :
      WorldGenerated strata P base commonCaps commonLeft commonRight
        (.empty common : OriginalCaptureMap (sourceEnv := sourceEnv) (U := U) .nil .id)
        (.nil (locals := []) (σ := commonLeft) (τ := commonRight) (available := fun _ => [])) controls
  | bind
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
      (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph tail controls)
      {baselineEnvironment : List Closure}
      (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
      (capacity : environmentCost (tail.dependencyEnvironment controls.ordered) ≤
        environmentCost baselineEnvironment)
      (domain : EndpointRef sourceEnv U source A (.sort level))
      (annotation : VExpr) (displayed : A.subst raw = annotation)
      (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
        (support : Profile n) footprint)
      (resources : footprint.Available available) (typed : input.HasType support)
      (arguments : Related env U registry target x y (A.subst σ) input support)
      (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
      (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
      WorldGenerated strata P base (commonCaps.push (Need.Fits input)) (commonLeft.cons x) (commonRight.cons y)
        (.bind graph domain annotation displayed)
        (.reserve (.bind tail domain certificate resources typed arguments needs bounded covered)
          [.close (domain.dependencyOrigin controls.ordered) baselineEnvironment]) controls
  | weaken
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
      (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph frame controls)
      {ρ : Lift} (insertion : Ctx.Lift' ρ common next)
      (leftTail : Subst.lift_l ρ nextLeft = commonLeft)
      (rightTail : Subst.lift_l ρ nextRight = commonRight)
      (capsTail : (fun index => nextCaps (ρ.liftVar index)) = commonCaps) :
      WorldGenerated strata P base nextCaps nextLeft nextRight (.weaken graph insertion) frame controls
  | capture
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
      (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph tail controls)
      {baselineEnvironment : List Closure}
      (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
      (capacity : environmentCost (tail.dependencyEnvironment controls.ordered) ≤
        environmentCost baselineEnvironment)
      (domain : EndpointRef sourceEnv U source A (.sort level))
      {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
      (initial : ContextDerivation sourceEnv U rootSource)
      (argument : EndpointState sourceEnv U source a A)
      (location : Located root argument)
      (lineage : location.contextDerivation initial = context)
      (query : RichObs sourceEnv env U registry target argument locals σ (rawInput : Profile k) argumentFootprint)
      (queryAvailable : argumentFootprint.Available available)
      (queryBound : n ≤ k)
      (queryAdapter : GeneralNormalProfileAdapter env U registry target rawInput (raiseProfile k queryBound (input : Profile n)))
      (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
        (support : Profile n) footprint)
      (resources : footprint.Available available) (typed : input.HasType support)
      (arguments : Related env U registry target (a.subst σ) (a.subst τ) (A.subst σ) input support)
      (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
      (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
      WorldGenerated strata P base commonCaps commonLeft commonRight
        (.capture graph domain graph argument ⟨_, _, _, root, initial, location, lineage.symm⟩)
        (.reserve (.capture tail domain initial argument location lineage query queryAvailable certificate resources typed
          arguments needs bounded covered)
          [.bundle (.close (argument.dependencyOrigin controls.ordered) baselineEnvironment)
            (.close (domain.dependencyOrigin controls.ordered) baselineEnvironment)]) controls
  | historyGroup
      {context : ContextDerivation headerEnv U headerSource}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame headerEnv env U registry target context locals
        (raw.comp commonLeft) (raw.comp commonRight) available}
      (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph tail controls)
      (domain : EndpointRef headerEnv U headerSource A (.sort level))
      {ownerContext : ContextDerivation ownerEnv U ownerSource}
      (ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw)
      {nominalContext : ContextDerivation nominalEnv U nominalSource}
      (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
      (nominal : EndpointState nominalEnv U nominalSource argument assigned)
      (provenance : EndpointProvenance nominalContext nominal)
      (displayed : rawCapture.subst ownerRaw = argument.subst nominalRaw)
      {field : EndpointRef ownerEnv U ownerSource fieldExpression fieldType}
      {major : EndpointRef ownerEnv U ownerSource majorExpression majorType}
      (ownerOrdered : ownerEnv.Ordered) (headerOrdered : headerEnv.Ordered)
      (ownerInitial : List Closure)
      (seed : PendingRichCapture (field := field) (major := major) domain env registry target
        seedLocals (raw.comp commonLeft) seedAvailable ownerInitial rawCapture leftValue rightValue)
      (seedScope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps seed.depth
        (seed.owner.context seed.initialContext))
      (seedControls : OriginalWorldControls strata ownerEnv)
      (seedGenerated : WorldGenerated strata P base seedScope.caps seedScope.left seedScope.right seedScope.graph seed.frame.raw seedControls)
      (domainProvenance : EndpointProvenance context (.ref domain))
      (prior : OriginalCaptureRealization graph env registry target priorLocals commonLeft commonRight priorAvailable)
      (history : OriginalSeedTypeHistory seed seedScope.toOriginalOwnerScope graph domainProvenance prior
        ownerOrdered headerOrdered)
      (priorGenerated : WorldGenerated strata P base commonCaps commonLeft commonRight graph prior.frame.raw controls)
      (initialProvenance : WorldEnvironmentProvenance strata U ownerInitial)
      (baselines : WorldEnvironmentProvenance strata U (seed.frame.dependencyEnvironment ownerOrdered) ×
        WorldEnvironmentProvenance strata U (prior.frame.dependencyEnvironment headerOrdered))
      (routeInputs : history.route.WorldInputs strata)
      (historyWellFormed : history.route.WellFormed)
      (historyControls : ∀ index : Fin history.route.frames.length,
        OriginalWorldControls strata (history.route.frames[index]).sourceEnv)
      (historyGenerated : ∀ index : Fin history.route.frames.length,
        WorldGenerated strata P base seedScope.caps seedScope.left seedScope.right
          (history.route.frames[index]).graph (history.route.frames[index]).frame.realization.frame.raw
          (historyControls index))
      (tailBound : environmentCost (tail.dependencyEnvironment headerOrdered) ≤
        environmentCost (prior.frame.dependencyEnvironment headerOrdered))
      (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        locals (raw.comp commonLeft) available ownerInitial rawCapture leftValue rightValue)
      (scopes : ∀ entry ∈ entries, CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps entry.depth
        (entry.owner.context entry.initialContext))
      (ownerControls : OriginalWorldControls strata ownerEnv)
      (owners : ∀ entry member, WorldGenerated strata P base (scopes entry member).caps (scopes entry member).left
        (scopes entry member).right (scopes entry member).graph entry.frame.raw ownerControls)
      (ownerAmbient : ownerGraph.Ambient env)
      (nominalAmbient : nominalGraph.Ambient env)
      (priorAmbient : prior.frame.Ambient)
      (routeAmbient : history.route.Ambient)
      (ownerSources : ownerGraph.AllSources P)
      (nominalSources : nominalGraph.AllSources P)
      (priorSources : prior.frame.raw.AllSources P)
      (routeSources : history.route.AllSources P) :
      WorldGenerated strata P base commonCaps commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance)
        (.reserve (.group tail domain ownerOrdered ownerInitial (richGroupedEntriesRaw entries))
          (groupCaptureHistoryReserve field major domain ownerOrdered headerOrdered ownerInitial
            (prior.frame.dependencyEnvironment headerOrdered) history.route.reserve)) controls

theorem WorldGenerated.erase
    {base : OriginalCaptureBase env U registry target}
    (generated : WorldGenerated strata P base caps left right graph frame controls) :
    SourceCaptureGenerated P base caps left right graph frame := by
  induction generated with
  | merge first second ih₁ ih₂ => exact .merge ih₁ ih₂
  | identity ambient sources controls environment => exact .identity ambient sources
  | empty common left right below source controls => exact .empty common left right below source
  | weaken _ insertion leftTail rightTail capsTail ih => exact .weaken ih insertion leftTail rightTail capsTail
  | bind generated baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    exact .reserveBind (.bind ih domain annotation displayed certificate resources typed arguments needs bounded covered) _
  | capture generated baseline capacity domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered ih =>
    exact .reserveCapture (.capture ih domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered) _

  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      tailIH seedIH priorIH historyIH ownerIH =>
    exact .historyGroup tailIH domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedIH domainProvenance prior history historyWellFormed
      (by
        intro boxed member
        obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
        subst boxed
        exact historyIH ⟨index, bound⟩)
      tailBound entries scopes ownerIH
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources

def WorldGenerated.callControls
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {controls : OriginalWorldControls strata sourceEnv}
    (_generated : WorldGenerated strata P base caps left right graph frame controls) :
    OriginalWorldControls strata sourceEnv := controls

noncomputable def WorldGenerated.environment
    {base : OriginalCaptureBase env U registry target}
    (generated : WorldGenerated strata P base caps left right graph frame controls) :
    WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered) := by
  induction generated with
  | merge first second ih₁ ih₂ => exact ih₁.append ih₂
  | identity ambient sources controls environment => exact environment
  | empty common left right below source controls => exact .nil
  | weaken _ _ _ _ _ ih => exact ih
  | bind generated baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    exact reservedBindWorldEnvironment generated.callControls domain baseline ih
  | capture generated baseline capacity domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered ih =>
    exact .cons (.captureBundle generated.callControls domain argument baseline)
      (.cons (.bundle (.scheduled .expressionReindex argument generated.callControls ih) (.original (.ref domain) generated.callControls ih)) ih)

  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      tailIH seedIH priorIH historyIH ownerIH =>
    let headerControls := generated.callControls
    let baseline := historyLedgerOfEntries entries ownerControls headerControls
      initialProvenance baselines.2 (history.route.worldReserve routeInputs)
    let actual := WorldEnvironmentProvenance.group ownerControls headerControls initialProvenance tailIH entries
    exact baseline.append (by
      simpa only [RawOriginalRichFrame.dependencyEnvironment, rawOwners, RichGroupedCapture.environment] using actual)

noncomputable def WorldGenerated.worlds
    {base : OriginalCaptureBase env U registry target}
    (generated : WorldGenerated strata P base caps left right graph frame controls) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  generated.environment.worlds

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
