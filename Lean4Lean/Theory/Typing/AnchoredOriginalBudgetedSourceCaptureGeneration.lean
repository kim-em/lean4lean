import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalRichGroupedCaptureDepth
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameTailDepth
import Lean4Lean.Theory.Typing.AnchoredStageBudgets

/-! Positive generation with finite declaration controls. In addition to the
actual visible frame, the bounds cover dormant seed queries, prior frames,
route frames, and every selected owner. This is structural evidence on the
same selected graph/frame, not an assumption supplying semantic answers. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option Elab.async false

inductive BudgetedSourceCaptureGenerated (P : VEnv → Prop) (budgets : Budgeted.Budgets)
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
      (generated : BudgetedSourceCaptureGenerated P budgets base commonCaps commonLeft commonRight graph frame)
      (valid : frame.Valid) :
      BudgetedSourceCaptureGenerated P budgets base commonCaps commonLeft commonRight (.tail graph)
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
      (generated : BudgetedSourceCaptureGenerated P budgets base commonCaps commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance) frame)
      (closures : List Closure) :
      BudgetedSourceCaptureGenerated P budgets base commonCaps commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance) (.reserve frame closures)
  | reserveBind
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {domain : EndpointRef sourceEnv U source A (.sort level)}
      {annotation : VExpr} {displayed : A.subst raw = annotation}
      {frame : RawOriginalRichFrame sourceEnv env U registry target
        (.cons context domain) locals σ τ available}
      (generated : BudgetedSourceCaptureGenerated P budgets base commonCaps commonLeft commonRight
        (.bind graph domain annotation displayed) frame)
      (closures : List Closure) :
      BudgetedSourceCaptureGenerated P budgets base commonCaps commonLeft commonRight
        (.bind graph domain annotation displayed) (.reserve frame closures)
  | merge
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {left : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable}
      {right : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable}
      (first : BudgetedSourceCaptureGenerated P budgets base commonCaps commonLeft commonRight graph left)
      (second : BudgetedSourceCaptureGenerated P budgets base commonCaps commonLeft commonRight graph right) :
      BudgetedSourceCaptureGenerated P budgets base commonCaps commonLeft commonRight graph (.merge left right)
  | identity (ambient : base.frame.Ambient) (sources : base.frame.raw.AllSources P)
      (frameBudget : Budgeted.Within budgets base.frame.raw.nativeDepth) : BudgetedSourceCaptureGenerated P budgets base base.initialCaps base.left base.right
      (.identity base.context) base.frame.raw
  | empty (common : List VExpr) (commonLeft commonRight : Subst) (below : sourceEnv ≤ env) (source : P sourceEnv) :
      BudgetedSourceCaptureGenerated P budgets base commonCaps commonLeft commonRight
        (.empty common : OriginalCaptureMap (sourceEnv := sourceEnv) (U := U) .nil .id)
        (.nil (locals := []) (σ := commonLeft) (τ := commonRight) (available := fun _ => []))
  | bind
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
      (generated : BudgetedSourceCaptureGenerated P budgets base commonCaps commonLeft commonRight graph tail)
      (domain : EndpointRef sourceEnv U source A (.sort level))
      (annotation : VExpr) (displayed : A.subst raw = annotation)
      (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
        (support : Profile n) footprint)
      (resources : footprint.Available available) (typed : input.HasType support)
      (arguments : Related env U registry target x y (A.subst σ) input support)
      (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
      (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms)
      (certificateBudget : Budgeted.Within budgets certificate.nativeDepth) :
      BudgetedSourceCaptureGenerated P budgets base (commonCaps.push (Need.Fits input)) (commonLeft.cons x) (commonRight.cons y)
        (.bind graph domain annotation displayed)
        (.bind tail domain certificate resources typed arguments needs bounded covered)
  | weaken
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
      (generated : BudgetedSourceCaptureGenerated P budgets base commonCaps commonLeft commonRight graph frame)
      {ρ : Lift} (insertion : Ctx.Lift' ρ common next)
      (leftTail : Subst.lift_l ρ nextLeft = commonLeft)
      (rightTail : Subst.lift_l ρ nextRight = commonRight)
      (capsTail : (fun index => nextCaps (ρ.liftVar index)) = commonCaps) :
      BudgetedSourceCaptureGenerated P budgets base nextCaps nextLeft nextRight (.weaken graph insertion) frame
  | capture
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
      (generated : BudgetedSourceCaptureGenerated P budgets base commonCaps commonLeft commonRight graph tail)
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
      (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms)
      (queryBudget : Budgeted.Within budgets query.nativeDepth)
      (certificateBudget : Budgeted.Within budgets certificate.nativeDepth) :
      BudgetedSourceCaptureGenerated P budgets base commonCaps commonLeft commonRight
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
      (generated : BudgetedSourceCaptureGenerated P budgets base commonCaps commonLeft commonRight graph tail)
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
      (seedGenerated : BudgetedSourceCaptureGenerated P budgets base seedScope.caps seedScope.left seedScope.right seedScope.graph seed.frame.raw)
      (domainProvenance : EndpointProvenance context (.ref domain))
      (prior : OriginalCaptureRealization graph env registry target priorLocals commonLeft commonRight priorAvailable)
      (history : OriginalSeedTypeHistory seed seedScope.toOriginalOwnerScope graph domainProvenance prior
        ownerOrdered headerOrdered)
      (historyWellFormed : history.route.WellFormed)
      (historyGenerated : ∀ boxed ∈ history.route.frames,
        BudgetedSourceCaptureGenerated P budgets base seedScope.caps seedScope.left seedScope.right
          boxed.graph boxed.frame.realization.frame.raw)
      (tailBound : environmentCost (tail.dependencyEnvironment headerOrdered) ≤
        environmentCost (prior.frame.dependencyEnvironment headerOrdered))
      (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        locals (raw.comp commonLeft) available ownerInitial rawCapture leftValue rightValue)
      (scopes : ∀ entry ∈ entries, CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps entry.depth
        (entry.owner.context entry.initialContext))
      (owners : ∀ entry member, BudgetedSourceCaptureGenerated P budgets base (scopes entry member).caps (scopes entry member).left
        (scopes entry member).right (scopes entry member).graph entry.frame.raw)
      (ownerAmbient : ownerGraph.Ambient env)
      (nominalAmbient : nominalGraph.Ambient env)
      (priorAmbient : prior.frame.Ambient)
      (routeAmbient : history.route.Ambient)
      (ownerSources : ownerGraph.AllSources P)
      (nominalSources : nominalGraph.AllSources P)
      (priorSources : prior.frame.raw.AllSources P)
      (routeSources : history.route.AllSources P)
      (seedBudget : Budgeted.Within budgets seed.query.nativeDepth)
      (priorBudget : Budgeted.Within budgets prior.frame.raw.nativeDepth)
      (entriesBudget : Budgeted.Within budgets entries.nativeDepth) :
      BudgetedSourceCaptureGenerated P budgets base commonCaps commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance)
        (.reserve (.group tail domain ownerOrdered ownerInitial (richGroupedEntriesRaw entries))
          (groupCaptureHistoryReserve field major domain ownerOrdered headerOrdered ownerInitial
            (prior.frame.dependencyEnvironment headerOrdered) history.route.reserve))


theorem BudgetedSourceCaptureGenerated.sourceGenerated
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : BudgetedSourceCaptureGenerated P budgets base commonCaps commonLeft commonRight graph frame) :
    SourceCaptureGenerated P base commonCaps commonLeft commonRight graph frame := by
  induction generated with
  | tail _ valid ih => exact .tail ih valid
  | reserveCapture _ closures ih => exact .reserveCapture ih closures
  | reserveBind _ closures ih => exact .reserveBind ih closures
  | merge _ _ first second => exact .merge first second
  | identity ambient sources budget => exact .identity ambient sources
  | empty common left right below source => exact .empty common left right below source
  | bind _ domain annotation displayed certificate resources typed arguments needs bounded covered budget ih =>
    exact .bind ih domain annotation displayed certificate resources typed arguments needs bounded covered
  | weaken _ insertion leftTail rightTail capsTail ih => exact .weaken ih insertion leftTail rightTail capsTail
  | capture _ domain initial argument location lineage query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered queryBudget certificateBudget ih =>
    exact .capture ih domain initial argument location lineage query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered
  | historyGroup _ domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope _ domainProvenance prior history historyWellFormed historyGenerated tailBound entries scopes owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      seedBudget priorBudget entriesBudget ih seedIH historyIH ownerIH =>
    exact .historyGroup ih domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedIH domainProvenance prior history historyWellFormed historyIH tailBound entries scopes ownerIH
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources

/-- The visible bound belongs to the very frame certified by generation. -/
theorem BudgetedSourceCaptureGenerated.frameBudget
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : BudgetedSourceCaptureGenerated P budgets base commonCaps commonLeft commonRight graph frame) :
    Budgeted.Within budgets frame.nativeDepth := by
  induction generated with
  | tail previous valid ih =>
    intro current fuel member
    exact Nat.le_trans (OriginalRichFrame.nativeDepth_fullTail ⟨_, valid⟩ current) (ih current fuel member)
  | reserveCapture _ _ ih =>
    simpa only [RawOriginalRichFrame.nativeDepth] using ih
  | reserveBind _ _ ih =>
    simpa only [RawOriginalRichFrame.nativeDepth] using ih
  | identity _ _ budget => exact budget
  | empty =>
    intro current fuel member
    simp only [RawOriginalRichFrame.nativeDepth]
    exact Nat.zero_le _
  | merge _ _ first second =>
    intro current fuel member
    simp only [RawOriginalRichFrame.nativeDepth]
    exact Nat.max_le.mpr ⟨first current fuel member, second current fuel member⟩
  | bind _ _ _ _ _ _ _ _ _ _ _ budget ih =>
    intro current fuel member
    simp only [RawOriginalRichFrame.nativeDepth]
    exact Nat.max_le.mpr ⟨budget current fuel member, ih current fuel member⟩
  | weaken _ _ _ _ _ ih => exact ih
  | capture _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ queryBudget certificateBudget ih =>
    intro current fuel member
    simp only [RawOriginalRichFrame.nativeDepth]
    exact Nat.max_le.mpr ⟨queryBudget current fuel member,
      Nat.max_le.mpr ⟨certificateBudget current fuel member, ih current fuel member⟩⟩
  | historyGroup _ domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope _ domainProvenance prior history historyWellFormed historyGenerated tailBound entries scopes owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      seedBudget priorBudget entriesBudget ih seedIH historyIH ownerIH =>
    intro current fuel member
    simp only [RawOriginalRichFrame.nativeDepth, richGroupedEntriesRaw_nativeDepth]
    exact Nat.max_le.mpr ⟨entriesBudget current fuel member, ih current fuel member⟩

/-- Relax all controls without changing any retained semantic witness. -/
theorem BudgetedSourceCaptureGenerated.monoBudgets
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : BudgetedSourceCaptureGenerated P budgets base commonCaps commonLeft commonRight graph frame)
    (implication : ∀ depth, Budgeted.Within budgets depth → Budgeted.Within nextBudgets depth) :
    BudgetedSourceCaptureGenerated P nextBudgets base commonCaps commonLeft commonRight graph frame := by
  induction generated with
  | tail _ valid ih => exact .tail ih valid
  | reserveCapture _ closures ih => exact .reserveCapture ih closures
  | reserveBind _ closures ih => exact .reserveBind ih closures
  | merge _ _ first second => exact .merge first second
  | identity ambient sources budget => exact .identity ambient sources (implication _ budget)
  | empty common left right below source => exact .empty common left right below source
  | bind _ domain annotation displayed certificate resources typed arguments needs bounded covered budget ih =>
    exact .bind ih domain annotation displayed certificate resources typed arguments needs bounded covered (implication _ budget)
  | weaken _ insertion leftTail rightTail capsTail ih => exact .weaken ih insertion leftTail rightTail capsTail
  | capture _ domain initial argument location lineage query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered queryBudget certificateBudget ih =>
    exact .capture ih domain initial argument location lineage query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered
      (implication _ queryBudget) (implication _ certificateBudget)
  | historyGroup _ domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope _ domainProvenance prior history historyWellFormed historyGenerated tailBound entries scopes owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      seedBudget priorBudget entriesBudget ih seedIH historyIH ownerIH =>
    exact .historyGroup ih domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedIH domainProvenance prior history historyWellFormed historyIH tailBound entries scopes ownerIH
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      (implication _ seedBudget) (implication _ priorBudget) (implication _ entriesBudget)

private theorem within_singleton {current : Name → Bool} {fuel : Nat}
    {depth : (Name → Bool) → Nat} (bound : depth current ≤ fuel) :
    Budgeted.Within [(current, fuel)] depth := by
  intro filter limit member
  cases List.mem_singleton.mp member
  exact bound

theorem BudgetedSourceCaptureGenerated.raiseFuel
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : BudgetedSourceCaptureGenerated P [(current, fuel)] base commonCaps commonLeft commonRight graph frame)
    (bound : fuel ≤ nextFuel) :
    BudgetedSourceCaptureGenerated P [(current, nextFuel)] base commonCaps commonLeft commonRight graph frame :=
  generated.monoBudgets fun _ previous => within_singleton
    (Nat.le_trans (previous current fuel List.mem_cons_self) bound)

private theorem finiteListFuel {α : Type} (items : List α)
    (property : ∀ item, item ∈ items → Nat → Prop)
    (relax : ∀ item member first next, first ≤ next → property item member first → property item member next)
    (witnesses : ∀ item member, ∃ fuel, property item member fuel) :
    ∃ fuel, ∀ item member, property item member fuel := by
  induction items with
  | nil => exact ⟨0, fun _ member => nomatch member⟩
  | cons head tail ih =>
    obtain ⟨first, firstBound⟩ := witnesses head List.mem_cons_self
    obtain ⟨rest, restBound⟩ := ih
      (fun item member fuel => property item (List.mem_cons_of_mem head member) fuel)
      (fun item member a b bound => relax item (List.mem_cons_of_mem head member) a b bound)
      (fun item member => witnesses item (List.mem_cons_of_mem head member))
    refine ⟨max first rest, ?_⟩
    intro item member
    rcases List.mem_cons.mp member with rfl | present
    · exact relax item member first _ (Nat.le_max_left _ _) firstBound
    · exact relax item member rest _ (Nat.le_max_right _ _) (restBound item present)

/-- Every finite positively generated capture has some finite active fuel,
including dormant histories. This does not manufacture quiet caller bounds
or prove preservation by a semantic recursive call. -/
theorem SourceCaptureGenerated.finiteFuel
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight graph frame)
    (current : Name → Bool) :
    ∃ fuel, BudgetedSourceCaptureGenerated P [(current, fuel)] base commonCaps commonLeft commonRight graph frame := by
  induction generated with
  | tail previous valid ih =>
    obtain ⟨fuel, bounded⟩ := ih
    exact ⟨fuel, .tail bounded valid⟩
  | reserveCapture _ closures ih =>
    obtain ⟨fuel, bounded⟩ := ih
    exact ⟨fuel, .reserveCapture bounded closures⟩
  | reserveBind _ closures ih =>
    obtain ⟨fuel, bounded⟩ := ih
    exact ⟨fuel, .reserveBind bounded closures⟩
  | merge _ _ ihl ihr =>
    obtain ⟨left, leftBound⟩ := ihl
    obtain ⟨right, rightBound⟩ := ihr
    exact ⟨max left right, .merge (leftBound.raiseFuel (Nat.le_max_left _ _))
      (rightBound.raiseFuel (Nat.le_max_right _ _))⟩
  | identity ambient sources =>
    exact ⟨_, .identity ambient sources (within_singleton (Nat.le_refl _))⟩
  | empty common left right below sources => exact ⟨0, .empty common left right below sources⟩
  | bind _ domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    obtain ⟨fuel, previous⟩ := ih
    exact ⟨max fuel (certificate.nativeDepth current),
      .bind (previous.raiseFuel (Nat.le_max_left _ _)) domain annotation displayed certificate
        resources typed arguments needs bounded covered (within_singleton (Nat.le_max_right _ _))⟩
  | weaken _ insertion leftTail rightTail capsTail ih =>
    obtain ⟨fuel, previous⟩ := ih
    exact ⟨fuel, .weaken previous insertion leftTail rightTail capsTail⟩
  | capture _ domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered ih =>
    obtain ⟨fuel, previous⟩ := ih
    let next := max fuel (max (query.nativeDepth current) (certificate.nativeDepth current))
    refine ⟨next, .capture (previous.raiseFuel (by omega)) domain initial argument location lineage query
      queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered
      (within_singleton ?_) (within_singleton ?_)⟩ <;> dsimp only [next] <;> omega
  | historyGroup _ domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope _ domainProvenance prior history historyWellFormed historyGenerated tailBound entries scopes owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      ih seedIH historyIH ownerIH =>
    obtain ⟨tailFuel, tailBounded⟩ := ih
    obtain ⟨seedFuel, seedBounded⟩ := seedIH
    obtain ⟨routeFuel, routeBounded⟩ := finiteListFuel history.route.frames
      (fun boxed _ fuel => BudgetedSourceCaptureGenerated P [(current, fuel)] _ _ _ _
        boxed.graph boxed.frame.realization.frame.raw)
      (fun _ _ _ _ bound generated => generated.raiseFuel bound) historyIH
    obtain ⟨ownerFuel, ownerBounded⟩ := finiteListFuel entries
      (fun entry member fuel => BudgetedSourceCaptureGenerated P [(current, fuel)] base
        (scopes entry member).caps (scopes entry member).left (scopes entry member).right
        (scopes entry member).graph entry.frame.raw)
      (fun _ _ _ _ bound generated => generated.raiseFuel bound) ownerIH
    let next := max tailFuel (max seedFuel (max routeFuel (max ownerFuel
      (max (seed.query.nativeDepth current)
        (max (prior.frame.raw.nativeDepth current) (entries.nativeDepth current))))))
    refine ⟨next, .historyGroup (tailBounded.raiseFuel (by omega))
      domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope (seedBounded.raiseFuel (by omega)) domainProvenance prior history historyWellFormed
      (fun boxed member => (routeBounded boxed member).raiseFuel (by omega)) tailBound entries scopes
      (fun entry member => (ownerBounded entry member).raiseFuel (by omega))
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      (within_singleton ?_) (within_singleton ?_) (within_singleton ?_)⟩ <;> dsimp only [next] <;> omega

private theorem within_cons {current : Name → Bool} {fuel : Nat}
    {depth : (Name → Bool) → Nat} (bound : depth current ≤ fuel)
    (previous : Budgeted.Within budgets depth) :
    Budgeted.Within ((current, fuel) :: budgets) depth := by
  intro filter limit member
  rcases List.mem_cons.mp member with equal | member
  · cases equal; exact bound
  · exact previous filter limit member

/-- Increase only the newly active fuel, preserving every caller control. -/
theorem BudgetedSourceCaptureGenerated.raiseActiveFuel
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : BudgetedSourceCaptureGenerated P ((current, fuel) :: budgets)
      base commonCaps commonLeft commonRight graph frame)
    (bound : fuel ≤ nextFuel) :
    BudgetedSourceCaptureGenerated P ((current, nextFuel) :: budgets)
      base commonCaps commonLeft commonRight graph frame :=
  generated.monoBudgets fun _ previous => within_cons
    (Nat.le_trans (previous current fuel List.mem_cons_self) bound)
    (fun filter limit member => previous filter limit (List.mem_cons_of_mem _ member))

/-- Start a new active control on the SAME finite retained generation while
preserving all existing caller budgets, including dormant history bounds. -/
theorem BudgetedSourceCaptureGenerated.addFiniteFuel
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : BudgetedSourceCaptureGenerated P budgets base commonCaps commonLeft commonRight graph frame)
    (current : Name → Bool) :
    ∃ fuel, BudgetedSourceCaptureGenerated P ((current, fuel) :: budgets) base commonCaps commonLeft commonRight graph frame := by
  induction generated with
  | tail previous valid ih =>
    obtain ⟨fuel, bounded⟩ := ih
    exact ⟨fuel, .tail bounded valid⟩
  | reserveCapture _ closures ih =>
    obtain ⟨fuel, bounded⟩ := ih
    exact ⟨fuel, .reserveCapture bounded closures⟩
  | reserveBind _ closures ih =>
    obtain ⟨fuel, bounded⟩ := ih
    exact ⟨fuel, .reserveBind bounded closures⟩
  | merge _ _ ihl ihr =>
    obtain ⟨left, leftBound⟩ := ihl
    obtain ⟨right, rightBound⟩ := ihr
    exact ⟨max left right, .merge (leftBound.raiseActiveFuel (Nat.le_max_left _ _))
      (rightBound.raiseActiveFuel (Nat.le_max_right _ _))⟩
  | identity ambient sources frameBudget =>
    exact ⟨_, .identity ambient sources (within_cons (Nat.le_refl _) frameBudget)⟩
  | empty common left right below sources => exact ⟨0, .empty common left right below sources⟩
  | bind _ domain annotation displayed certificate resources typed arguments needs bounded covered certificateBudget ih =>
    obtain ⟨fuel, previous⟩ := ih
    exact ⟨max fuel (certificate.nativeDepth current),
      .bind (previous.raiseActiveFuel (Nat.le_max_left _ _)) domain annotation displayed certificate
        resources typed arguments needs bounded covered (within_cons (Nat.le_max_right _ _) certificateBudget)⟩
  | weaken _ insertion leftTail rightTail capsTail ih =>
    obtain ⟨fuel, previous⟩ := ih
    exact ⟨fuel, .weaken previous insertion leftTail rightTail capsTail⟩
  | capture _ domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered queryBudget certificateBudget ih =>
    obtain ⟨fuel, previous⟩ := ih
    let next := max fuel (max (query.nativeDepth current) (certificate.nativeDepth current))
    refine ⟨next, .capture (previous.raiseActiveFuel (by omega)) domain initial argument location lineage query
      queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered
      (within_cons ?_ queryBudget) (within_cons ?_ certificateBudget)⟩ <;> dsimp only [next] <;> omega
  | historyGroup _ domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope _ domainProvenance prior history historyWellFormed historyGenerated tailBound entries scopes owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      seedBudget priorBudget entriesBudget ih seedIH historyIH ownerIH =>
    obtain ⟨tailFuel, tailBounded⟩ := ih
    obtain ⟨seedFuel, seedBounded⟩ := seedIH
    obtain ⟨routeFuel, routeBounded⟩ := finiteListFuel history.route.frames
      (fun boxed _ fuel => BudgetedSourceCaptureGenerated P ((current, fuel) :: budgets) _ _ _ _
        boxed.graph boxed.frame.realization.frame.raw)
      (fun _ _ _ _ bound generated => generated.raiseActiveFuel bound) historyIH
    obtain ⟨ownerFuel, ownerBounded⟩ := finiteListFuel entries
      (fun entry member fuel => BudgetedSourceCaptureGenerated P ((current, fuel) :: budgets) base
        (scopes entry member).caps (scopes entry member).left (scopes entry member).right
        (scopes entry member).graph entry.frame.raw)
      (fun _ _ _ _ bound generated => generated.raiseActiveFuel bound) ownerIH
    let next := max tailFuel (max seedFuel (max routeFuel (max ownerFuel
      (max (seed.query.nativeDepth current)
        (max (prior.frame.raw.nativeDepth current) (entries.nativeDepth current))))))
    refine ⟨next, .historyGroup (tailBounded.raiseActiveFuel (by omega))
      domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope (seedBounded.raiseActiveFuel (by omega)) domainProvenance prior history historyWellFormed
      (fun boxed member => (routeBounded boxed member).raiseActiveFuel (by omega)) tailBound entries scopes
      (fun entry member => (ownerBounded entry member).raiseActiveFuel (by omega))
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      (within_cons ?_ seedBudget) (within_cons ?_ priorBudget) (within_cons ?_ entriesBudget)⟩ <;> dsimp only [next] <;> omega

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
