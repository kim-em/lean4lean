import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientCaptureGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalSourcePredicatesTransport
import Lean4Lean.Theory.Typing.AnchoredOriginalTypeRouteSources

/-! Positive generation retaining a hereditary source predicate in addition to
ambient inclusion. Actual scoped owners and dormant histories retain the same
semantic frames; erasure returns the existing ambient-generation witness. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option Elab.async false

inductive SourceCaptureGenerated (P : VEnv → Prop)
    (base : OriginalCaptureBase env U registry target) :
    (commonCaps : CaptureCaps) →
    {common : List VExpr} → (commonLeft commonRight : Subst) →
    {sourceEnv : VEnv} → {source : List VExpr} →
    {context : ContextDerivation sourceEnv U source} → {raw : Subst} →
    {locals : List Nat} → {σ τ : Subst} → {available : Valuation} →
    OriginalCaptureMap (common := common) context raw →
    RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available → Prop where
  | tail
      {context : ContextDerivation sourceEnv U source}
      {domain : EndpointRef sourceEnv U source A (.sort level)}
      {graph : OriginalCaptureMap (common := common) (.cons context domain) raw}
      {frame : RawOriginalRichFrame sourceEnv env U registry target (.cons context domain) locals σ τ available}
      (generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight graph frame)
      (valid : frame.Valid) :
      SourceCaptureGenerated P base commonCaps commonLeft commonRight (.tail graph)
        (OriginalRichFrame.mk frame valid).fullTail.frame.raw
  | reserveCapture
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {domain : EndpointRef sourceEnv U source A (.sort level)}
      {nominalContext : ContextDerivation nominalEnv U nominalSource}
      {nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw}
      {nominal : EndpointState nominalEnv U nominalSource argument assigned}
      {provenance : EndpointProvenance nominalContext nominal}
      {frame : RawOriginalRichFrame sourceEnv env U registry target
        (.cons context domain) locals σ τ available}
      (generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance) frame)
      (closures : List Closure) :
      SourceCaptureGenerated P base commonCaps commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance) (.reserve frame closures)
  | reserveBind
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {domain : EndpointRef sourceEnv U source A (.sort level)}
      {annotation : VExpr} {displayed : A.subst raw = annotation}
      {frame : RawOriginalRichFrame sourceEnv env U registry target
        (.cons context domain) locals σ τ available}
      (generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight
        (.bind graph domain annotation displayed) frame)
      (closures : List Closure) :
      SourceCaptureGenerated P base commonCaps commonLeft commonRight
        (.bind graph domain annotation displayed) (.reserve frame closures)
  | merge
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {left : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable}
      {right : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable}
      (first : SourceCaptureGenerated P base commonCaps commonLeft commonRight graph left)
      (second : SourceCaptureGenerated P base commonCaps commonLeft commonRight graph right) :
      SourceCaptureGenerated P base commonCaps commonLeft commonRight graph (.merge left right)
  | identity (ambient : base.frame.Ambient) (sources : base.frame.raw.AllSources P) : SourceCaptureGenerated P base base.initialCaps base.left base.right
      (.identity base.context) base.frame.raw
  | empty (common : List VExpr) (commonLeft commonRight : Subst) (below : sourceEnv ≤ env) (source : P sourceEnv) :
      SourceCaptureGenerated P base commonCaps commonLeft commonRight
        (.empty common : OriginalCaptureMap (sourceEnv := sourceEnv) (U := U) .nil .id)
        (.nil (locals := []) (σ := commonLeft) (τ := commonRight) (available := fun _ => []))
  | bind
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
      (generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight graph tail)
      (domain : EndpointRef sourceEnv U source A (.sort level))
      (annotation : VExpr) (displayed : A.subst raw = annotation)
      (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
        (support : Profile n) footprint)
      (resources : footprint.Available available) (typed : input.HasType support)
      (arguments : Related env U registry target x y (A.subst σ) input support)
      (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
      (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
      SourceCaptureGenerated P base (commonCaps.push (Need.Fits input)) (commonLeft.cons x) (commonRight.cons y)
        (.bind graph domain annotation displayed)
        (.bind tail domain certificate resources typed arguments needs bounded covered)
  | weaken
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
      (generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight graph frame)
      {ρ : Lift} (insertion : Ctx.Lift' ρ common next)
      (leftTail : Subst.lift_l ρ nextLeft = commonLeft)
      (rightTail : Subst.lift_l ρ nextRight = commonRight)
      (capsTail : (fun index => nextCaps (ρ.liftVar index)) = commonCaps) :
      SourceCaptureGenerated P base nextCaps nextLeft nextRight (.weaken graph insertion) frame
  | capture
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
      (generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight graph tail)
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
      SourceCaptureGenerated P base commonCaps commonLeft commonRight
        (.capture graph domain graph argument ⟨_, _, _, root, initial, location, lineage.symm⟩)
        (.capture tail domain initial argument location lineage query queryAvailable certificate resources typed
          arguments needs bounded covered)
  /-- Retain the original seed and declaration baseline independently of the
  current queries. Both the finite history and the fixed rebuilt-group
  envelope are charged at the captured head. -/
  | historyGroup
      {context : ContextDerivation headerEnv U headerSource}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame headerEnv env U registry target context locals
        (raw.comp commonLeft) (raw.comp commonRight) available}
      (generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight graph tail)
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
      (seedGenerated : SourceCaptureGenerated P base seedScope.caps seedScope.left seedScope.right seedScope.graph seed.frame.raw)
      (domainProvenance : EndpointProvenance context (.ref domain))
      (prior : OriginalCaptureRealization graph env registry target priorLocals commonLeft commonRight priorAvailable)
      (history : OriginalSeedTypeHistory seed seedScope.toOriginalOwnerScope graph domainProvenance prior
        ownerOrdered headerOrdered)
      (historyWellFormed : history.route.WellFormed)
      (historyGenerated : ∀ boxed ∈ history.route.frames,
        SourceCaptureGenerated P base seedScope.caps seedScope.left seedScope.right
          boxed.graph boxed.frame.realization.frame.raw)
      (tailBound : environmentCost (tail.dependencyEnvironment headerOrdered) ≤
        environmentCost (prior.frame.dependencyEnvironment headerOrdered))
      (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        locals (raw.comp commonLeft) available ownerInitial rawCapture leftValue rightValue)
      (scopes : ∀ entry ∈ entries, CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps entry.depth
        (entry.owner.context entry.initialContext))
      (owners : ∀ entry member, SourceCaptureGenerated P base (scopes entry member).caps (scopes entry member).left
        (scopes entry member).right (scopes entry member).graph entry.frame.raw)
      (ownerAmbient : ownerGraph.Ambient env)
      (nominalAmbient : nominalGraph.Ambient env)
      (priorAmbient : prior.frame.Ambient)
      (routeAmbient : history.route.Ambient)
      (ownerSources : ownerGraph.AllSources P)
      (nominalSources : nominalGraph.AllSources P)
      (priorSources : prior.frame.raw.AllSources P)
      (routeSources : history.route.AllSources P) :
      SourceCaptureGenerated P base commonCaps commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance)
        (.reserve (.group tail domain ownerOrdered ownerInitial (richGroupedEntriesRaw entries))
          (groupCaptureHistoryReserve field major domain ownerOrdered headerOrdered ownerInitial
            (prior.frame.dependencyEnvironment headerOrdered) history.route.reserve))


theorem SourceCaptureGenerated.ambientGenerated
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight graph frame) :
    AmbientCaptureGenerated base commonCaps commonLeft commonRight graph frame := by
  induction generated with
  | tail _ valid ih => exact .tail ih valid
  | reserveCapture _ closures ih => exact .reserveCapture ih closures
  | reserveBind _ closures ih => exact .reserveBind ih closures
  | merge _ _ first second => exact .merge first second
  | identity ambient sources => exact .identity ambient
  | empty common left right below source => exact .empty common left right below
  | bind _ domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    exact .bind ih domain annotation displayed certificate resources typed arguments needs bounded covered
  | weaken _ insertion leftTail rightTail capsTail ih => exact .weaken ih insertion leftTail rightTail capsTail
  | capture _ domain initial argument location lineage query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered ih =>
    exact .capture ih domain initial argument location lineage query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered
  | historyGroup _ domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope _ domainProvenance prior history historyWellFormed historyGenerated tailBound entries scopes owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources ih seedIH historyIH ownerIH =>
    exact .historyGroup ih domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedIH domainProvenance prior history historyWellFormed historyIH tailBound entries scopes ownerIH
      ownerAmbient nominalAmbient priorAmbient routeAmbient

theorem SourceCaptureGenerated.capped
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight graph frame) :
    CappedCaptureGenerated base commonCaps commonLeft commonRight graph frame :=
  generated.ambientGenerated.capped

private theorem entriesSources
    {field : EndpointRef sourceEnv U source fe ft}
    {major : EndpointRef sourceEnv U source me majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (entries : List (RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue))
    (owners : ∀ entry ∈ entries, entry.frame.raw.AllSources P) :
    (richGroupedEntriesRaw entries).AllSources P := by
  induction entries with
  | nil => simp only [richGroupedEntriesRaw, RawRichGroupEntries.AllSources.eq_def]
  | cons entry rest ih =>
    rw [richGroupedEntriesRaw, RawRichGroupEntries.AllSources.eq_def]
    refine ⟨?_, ih (fun e member => owners e (List.mem_cons_of_mem _ member))⟩
    simpa only [RichGroupedCaptureEntry.toRaw, RawRichGroupEntry.AllSources.eq_def] using
      owners entry (List.mem_cons_self ..)

theorem SourceCaptureGenerated.sources
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight graph frame) :
    graph.AllSources P ∧ frame.AllSources P := by
  induction generated with
  | tail _ valid ih =>
    exact ⟨⟨ih.1.source, ih.1⟩, OriginalRichFrame.AllSources.fullTail ⟨_, valid⟩ ih.2⟩
  | reserveCapture _ _ ih =>
    refine ⟨ih.1, ?_⟩
    rw [RawOriginalRichFrame.AllSources.eq_def]
    exact ⟨ih.2.source, ih.2⟩
  | reserveBind _ _ ih =>
    refine ⟨ih.1, ?_⟩
    rw [RawOriginalRichFrame.AllSources.eq_def]
    exact ⟨ih.2.source, ih.2⟩
  | merge _ _ first second =>
    refine ⟨first.1, ?_⟩
    rw [RawOriginalRichFrame.AllSources.eq_def]
    exact ⟨first.2.source, first.2, second.2⟩
  | identity ambient sources => exact ⟨⟨sources.source, trivial⟩, sources⟩
  | empty common left right below source =>
    refine ⟨⟨source, trivial⟩, ?_⟩
    rw [RawOriginalRichFrame.AllSources.eq_def]
    exact ⟨source, trivial⟩
  | bind _ domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    refine ⟨⟨ih.1.source, ih.1⟩, ?_⟩
    rw [RawOriginalRichFrame.AllSources.eq_def]
    exact ⟨ih.2.source, ih.2⟩
  | weaken _ insertion leftTail rightTail capsTail ih => exact ⟨⟨ih.1.source, ih.1⟩, ih.2⟩
  | capture _ domain initial argument location lineage query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered ih =>
    refine ⟨⟨ih.1.source, ih.1, ih.1⟩, ?_⟩
    rw [RawOriginalRichFrame.AllSources.eq_def]
    exact ⟨ih.2.source, ih.2⟩
  | historyGroup _ domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope _ domainProvenance prior history historyWellFormed historyGenerated tailBound entries scopes owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      ih seedIH historyIH ownerIH =>
    refine ⟨⟨ih.1.source, ih.1, nominalSources⟩, ?_⟩
    rw [RawOriginalRichFrame.AllSources.eq_def]
    refine ⟨ih.2.source, ?_⟩
    dsimp only
    rw [RawOriginalRichFrame.AllSources.eq_def]
    exact ⟨ih.2.source, ih.2, ownerSources.source,
      entriesSources entries (fun entry member => (ownerIH entry member).2)⟩

theorem SourceCaptureGenerated.mono
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight graph frame)
    (implication : ∀ source, P source → Q source) :
    SourceCaptureGenerated Q base commonCaps commonLeft commonRight graph frame := by
  induction generated with
  | tail _ valid ih => exact .tail ih valid
  | reserveCapture _ closures ih => exact .reserveCapture ih closures
  | reserveBind _ closures ih => exact .reserveBind ih closures
  | merge _ _ first second => exact .merge first second
  | identity ambient sources => exact .identity ambient (sources.mono implication)
  | empty common left right below source => exact .empty common left right below (implication _ source)
  | bind _ domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    exact .bind ih domain annotation displayed certificate resources typed arguments needs bounded covered
  | weaken _ insertion leftTail rightTail capsTail ih => exact .weaken ih insertion leftTail rightTail capsTail
  | capture _ domain initial argument location lineage query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered ih =>
    exact .capture ih domain initial argument location lineage query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered
  | historyGroup _ domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope _ domainProvenance prior history historyWellFormed historyGenerated tailBound entries scopes owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      ih seedIH historyIH ownerIH =>
    exact .historyGroup ih domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedIH domainProvenance prior history historyWellFormed historyIH tailBound entries scopes ownerIH
      ownerAmbient nominalAmbient priorAmbient routeAmbient (ownerSources.mono implication)
      (nominalSources.mono implication) (priorSources.mono implication)
      (RawGeneratedTypeRoute.AllSources.mono _ routeSources implication)

/-- Initializing a hereditary source predicate from ambient inclusion leaves
all actual frames and retained histories unchanged. At the full target stage,
constant-count monotonicity supplies `included`. -/
theorem AmbientCaptureGenerated.liftSources
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight graph frame)
    (included : ∀ source, source ≤ env → P source) :
    SourceCaptureGenerated P base commonCaps commonLeft commonRight graph frame := by
  induction generated with
  | tail _ valid ih => exact .tail ih valid
  | reserveCapture _ closures ih => exact .reserveCapture ih closures
  | reserveBind _ closures ih => exact .reserveBind ih closures
  | merge _ _ first second => exact .merge first second
  | identity ambient =>
    exact .identity ambient ((base.frame.raw.allSources_ambient.mpr ambient).mono included)
  | empty common left right below => exact .empty common left right below (included _ below)
  | bind _ domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    exact .bind ih domain annotation displayed certificate resources typed arguments needs bounded covered
  | weaken _ insertion leftTail rightTail capsTail ih => exact .weaken ih insertion leftTail rightTail capsTail
  | capture _ domain initial argument location lineage query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered ih =>
    exact .capture ih domain initial argument location lineage query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered
  | historyGroup _ domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope _ domainProvenance prior history historyWellFormed historyGenerated tailBound entries scopes owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ih seedIH historyIH ownerIH =>
    exact .historyGroup ih domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedIH domainProvenance prior history historyWellFormed historyIH tailBound entries scopes ownerIH
      ownerAmbient nominalAmbient priorAmbient routeAmbient
      ((ownerGraph.allSources_ambient.mpr ownerAmbient).mono included)
      ((nominalGraph.allSources_ambient.mpr nominalAmbient).mono included)
      ((prior.frame.raw.allSources_ambient.mpr priorAmbient).mono included)
      (RawGeneratedTypeRoute.AllSources.ofAmbient history.route routeAmbient included)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
