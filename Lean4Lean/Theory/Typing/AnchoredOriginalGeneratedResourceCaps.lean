import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedReplyMerge
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPendingCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalSeedTypeHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalGroupBaselineBudget

/-! Fresh common binders retain a fixed finite profile cap. Capture slots
may collect additional original queries, while every hidden owner baseline
is generated under the same common caps. Every group retains a paid actual
owner seed independently of its current resource queries, including when
that list is empty. The seed carries no declared-domain alignment answer. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev CaptureCaps := Nat → Need → Prop

def CaptureCaps.push (head : Need → Prop) (tail : CaptureCaps) : CaptureCaps
  | 0 => head
  | index + 1 => tail index

def Need.Fits (input : Profile n) (need : Need) : Prop :=
  need.rank ≤ n ∧ ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms

def CaptureCaps.Holds (caps : CaptureCaps) (available : Valuation) : Prop :=
  ∀ index need, need ∈ available index → caps index need

def OriginalCaptureBase.initialCaps (base : OriginalCaptureBase env U registry target) : CaptureCaps :=
  fun index need => need ∈ base.available index

/-- A captured head is extensible. A fresh common binder inherits the common
head cap, and source weakening pulls the caps back along its actual lift. -/
def OriginalCaptureMap.resourceCaps
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw) (commonCaps : CaptureCaps) : CaptureCaps :=
  match graph with
  | .empty _ => fun _ _ => False
  | .identity _ => commonCaps
  | .tail previous => fun index => previous.resourceCaps commonCaps (index + 1)
  | .capture previous .. => (previous.resourceCaps commonCaps).push (fun _ => True)
  | .bind previous .. => (previous.resourceCaps (fun index => commonCaps (index + 1))).push (commonCaps 0)
  | .weaken (ρ := ρ) previous _ => previous.resourceCaps (fun index => commonCaps (ρ.liftVar index))

theorem OriginalCaptureGenerated.resourceCaps
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := base.source) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : OriginalCaptureGenerated base graph frame) :
    (graph.resourceCaps base.initialCaps).Holds available := by
  induction generated with
  | identity => intro index need member; exact member
  | empty => intro index need member; exact False.elim (List.not_mem_nil member)
  | capture _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    intro index need member
    cases index with
    | zero => trivial
    | succ index => exact ih index need member
  | group _ _ _ _ _ _ _ _ _ ih =>
    intro index need member
    cases index with
    | zero => trivial
    | succ index => exact ih index need member

/-- A retained owner's common scope and inherited immutable binder caps.
The actual generated frame is supplied separately, so this data also covers
query-selected merges beneath the original source binders. -/
structure CappedOwnerScope
    (common : List VExpr) (ownerRaw commonLeft commonRight : Subst)
    (commonCaps : CaptureCaps) (depth : Nat)
    (context : ContextDerivation sourceEnv U source)
    extends OriginalOwnerScope common ownerRaw commonLeft commonRight depth context where
  caps : CaptureCaps
  capsTail : (fun index => caps ((Lift.skipN .refl depth).liftVar index)) = commonCaps

inductive CappedCaptureGenerated
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
      (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph frame)
      (valid : frame.Valid) :
      CappedCaptureGenerated base commonCaps commonLeft commonRight (.tail graph)
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
      (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance) frame)
      (closures : List Closure) :
      CappedCaptureGenerated base commonCaps commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance) (.reserve frame closures)
  | reserveBind
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {domain : EndpointRef sourceEnv U source A (.sort level)}
      {annotation : VExpr} {displayed : A.subst raw = annotation}
      {frame : RawOriginalRichFrame sourceEnv env U registry target
        (.cons context domain) locals σ τ available}
      (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight
        (.bind graph domain annotation displayed) frame)
      (closures : List Closure) :
      CappedCaptureGenerated base commonCaps commonLeft commonRight
        (.bind graph domain annotation displayed) (.reserve frame closures)
  | merge
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {left : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable}
      {right : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable}
      (first : CappedCaptureGenerated base commonCaps commonLeft commonRight graph left)
      (second : CappedCaptureGenerated base commonCaps commonLeft commonRight graph right) :
      CappedCaptureGenerated base commonCaps commonLeft commonRight graph (.merge left right)
  | identity : CappedCaptureGenerated base base.initialCaps base.left base.right
      (.identity base.context) base.frame.raw
  | empty (common : List VExpr) (commonLeft commonRight : Subst) :
      CappedCaptureGenerated base commonCaps commonLeft commonRight
        (.empty common : OriginalCaptureMap (sourceEnv := sourceEnv) (U := U) .nil .id)
        (.nil (locals := []) (σ := commonLeft) (τ := commonRight) (available := fun _ => []))
  | bind
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
      (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph tail)
      (domain : EndpointRef sourceEnv U source A (.sort level))
      (annotation : VExpr) (displayed : A.subst raw = annotation)
      (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
        (support : Profile n) footprint)
      (resources : footprint.Available available) (typed : input.HasType support)
      (arguments : Related env U registry target x y (A.subst σ) input support)
      (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
      (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
      CappedCaptureGenerated base (commonCaps.push (Need.Fits input)) (commonLeft.cons x) (commonRight.cons y)
        (.bind graph domain annotation displayed)
        (.bind tail domain certificate resources typed arguments needs bounded covered)
  | weaken
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
      (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph frame)
      {ρ : Lift} (insertion : Ctx.Lift' ρ common next)
      (leftTail : Subst.lift_l ρ nextLeft = commonLeft)
      (rightTail : Subst.lift_l ρ nextRight = commonRight)
      (capsTail : (fun index => nextCaps (ρ.liftVar index)) = commonCaps) :
      CappedCaptureGenerated base nextCaps nextLeft nextRight (.weaken graph insertion) frame
  | capture
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
      (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph tail)
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
      CappedCaptureGenerated base commonCaps commonLeft commonRight
        (.capture graph domain graph argument ⟨_, _, _, root, initial, location, lineage.symm⟩)
        (.capture tail domain initial argument location lineage query queryAvailable certificate resources typed
          arguments needs bounded covered)
  | group
      {context : ContextDerivation headerEnv U headerSource}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame headerEnv env U registry target context locals σ τ available}
      (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph tail)
      (domain : EndpointRef headerEnv U headerSource A (.sort level))
      {ownerContext : ContextDerivation ownerEnv U ownerSource}
      {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
      {ownerFrame : RawOriginalRichFrame ownerEnv env U registry target ownerContext ownerLocals ownerLeft ownerRight ownerAvailable}
      (ownerGenerated : CappedCaptureGenerated base commonCaps commonLeft commonRight ownerGraph ownerFrame)
      {nominalContext : ContextDerivation nominalEnv U nominalSource}
      (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
      (nominal : EndpointState nominalEnv U nominalSource argument assigned)
      (provenance : EndpointProvenance nominalContext nominal)
      (displayed : rawCapture.subst ownerRaw = argument.subst nominalRaw)
      {field : EndpointRef ownerEnv U ownerSource fieldExpression fieldType}
      {major : EndpointRef ownerEnv U ownerSource majorExpression majorType}
      (ownerOrdered : ownerEnv.Ordered) (ownerInitial : List Closure)
      (seed : PendingRichCapture (field := field) (major := major) domain env registry target
        locals σ available ownerInitial rawCapture (rawCapture.subst ownerLeft) (rawCapture.subst ownerRight))
      (seedExtension : OriginalFrameExtension ownerFrame seed.frame.raw)
      (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        locals σ available ownerInitial rawCapture (rawCapture.subst ownerLeft) (rawCapture.subst ownerRight))
      (owners : ∀ entry ∈ entries, Nonempty (OriginalFrameExtension ownerFrame entry.frame.raw)) :
      CappedCaptureGenerated base commonCaps commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance)
        (.group tail domain ownerOrdered ownerInitial (richGroupedEntriesRaw entries))

  | scopedGroup
      {context : ContextDerivation headerEnv U headerSource}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame headerEnv env U registry target context locals σ τ available}
      (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph tail)
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
      (ownerOrdered : ownerEnv.Ordered) (ownerInitial : List Closure)
      (seed : PendingRichCapture (field := field) (major := major) domain env registry target
        locals σ available ownerInitial rawCapture leftValue rightValue)
      (seedScope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps seed.depth
        (seed.owner.context seed.initialContext))
      (seedGenerated : CappedCaptureGenerated base seedScope.caps seedScope.left seedScope.right seedScope.graph seed.frame.raw)
      (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        locals σ available ownerInitial rawCapture leftValue rightValue)
      (scopes : ∀ entry ∈ entries, CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps entry.depth
        (entry.owner.context entry.initialContext))
      (owners : ∀ entry member, CappedCaptureGenerated base (scopes entry member).caps (scopes entry member).left
        (scopes entry member).right (scopes entry member).graph entry.frame.raw) :
      CappedCaptureGenerated base commonCaps commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance)
        (.group tail domain ownerOrdered ownerInitial (richGroupedEntriesRaw entries))


  /-- Retain the original seed and declaration baseline independently of the
  current queries. Both the finite history and the fixed rebuilt-group
  envelope are charged at the captured head. -/
  | historyGroup
      {context : ContextDerivation headerEnv U headerSource}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame headerEnv env U registry target context locals
        (raw.comp commonLeft) (raw.comp commonRight) available}
      (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph tail)
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
      (seedGenerated : CappedCaptureGenerated base seedScope.caps seedScope.left seedScope.right seedScope.graph seed.frame.raw)
      (domainProvenance : EndpointProvenance context (.ref domain))
      (prior : OriginalCaptureRealization graph env registry target priorLocals commonLeft commonRight priorAvailable)
      (history : OriginalSeedTypeHistory seed seedScope.toOriginalOwnerScope graph domainProvenance prior
        ownerOrdered headerOrdered)
      (historyWellFormed : history.route.WellFormed)
      (historyGenerated : ∀ boxed ∈ history.route.frames,
        CappedCaptureGenerated base seedScope.caps seedScope.left seedScope.right
          boxed.graph boxed.frame.realization.frame.raw)
      (tailBound : environmentCost (tail.dependencyEnvironment headerOrdered) ≤
        environmentCost (prior.frame.dependencyEnvironment headerOrdered))
      (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        locals (raw.comp commonLeft) available ownerInitial rawCapture leftValue rightValue)
      (scopes : ∀ entry ∈ entries, CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps entry.depth
        (entry.owner.context entry.initialContext))
      (owners : ∀ entry member, CappedCaptureGenerated base (scopes entry member).caps (scopes entry member).left
        (scopes entry member).right (scopes entry member).graph entry.frame.raw) :
      CappedCaptureGenerated base commonCaps commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance)
        (.reserve (.group tail domain ownerOrdered ownerInitial (richGroupedEntriesRaw entries))
          (groupCaptureHistoryReserve field major domain ownerOrdered headerOrdered ownerInitial
            (prior.frame.dependencyEnvironment headerOrdered) history.route.reserve))


theorem CappedCaptureGenerated.generated
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (capped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph frame) :
    ScopedCaptureGenerated base commonLeft commonRight graph frame := by
  induction capped with
  | tail generated valid ih => exact .tail ih valid
  | reserveCapture _ closures ih => exact .reserveCapture ih closures
  | reserveBind _ closures ih => exact .reserveBind ih closures
  | identity => exact .original .identity
  | merge _ _ first second => exact .merge first second
  | empty => exact .empty _ _ _
  | bind _ domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    exact .bind ih domain annotation displayed certificate resources typed arguments needs bounded covered
  | weaken _ insertion leftTail rightTail capsTail ih => exact .weaken ih insertion leftTail rightTail
  | capture _ domain initial argument location lineage query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered ih =>
    exact .capture ih domain initial argument location lineage query queryAvailable certificate resources typed arguments needs bounded covered
  | group _ domain _ nominalGraph nominal provenance displayed ownerOrdered ownerInitial seed seedExtension entries owners ih ownerIH =>
    exact .group ih domain ownerIH nominalGraph nominal provenance displayed ownerOrdered ownerInitial entries owners
  | scopedGroup _ domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered ownerInitial
      seed seedScope _ entries scopes owners ih seedIH ownerIH =>
    exact .scopedGroup ih domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered ownerInitial
      seed seedScope.toOriginalOwnerScope seedIH entries
      (fun entry member => (scopes entry member).toOriginalOwnerScope) ownerIH

  | historyGroup _ domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope _ domainProvenance prior history historyWellFormed historyGenerated tailBound entries scopes owners
      ih seedIH historyIH ownerIH =>
    exact .reserveCapture
      (.scopedGroup ih domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered ownerInitial
        (seed.reheader _ _ _) seedScope.toOriginalOwnerScope seedIH entries
        (fun entry member => (scopes entry member).toOriginalOwnerScope) ownerIH) _

theorem CappedCaptureGenerated.availableBound
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (capped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph frame) :
    (graph.resourceCaps commonCaps).Holds available := by
  induction capped with
  | tail generated valid ih => exact fun index need member => ih (index + 1) need member
  | reserveCapture _ _ ih => exact ih
  | reserveBind _ _ ih => exact ih
  | identity => intro index need member; exact member
  | merge _ _ first second =>
    intro index need member
    exact (List.mem_append.mp member).elim (first index need) (second index need)
  | empty => intro index need member; exact False.elim (List.not_mem_nil member)
  | bind _ domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    intro index need member
    cases index with
    | zero => exact ⟨bounded need member, covered need member⟩
    | succ index => exact ih index need member
  | weaken _ insertion leftTail rightTail capsTail ih =>
    simpa only [OriginalCaptureMap.resourceCaps, capsTail] using ih
  | capture _ domain initial argument location lineage query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered ih =>
    intro index need member
    cases index with
    | zero => trivial
    | succ index => exact ih index need member
  | group _ domain _ nominalGraph nominal provenance displayed ownerOrdered ownerInitial seed seedExtension entries owners ih ownerIH =>
    intro index need member
    cases index with
    | zero => trivial
    | succ index => exact ih index need member
  | scopedGroup _ domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered ownerInitial
      seed seedScope _ entries scopes owners ih seedIH ownerIH =>
    intro index need member
    cases index with
    | zero => trivial
    | succ index => exact ih index need member

  | historyGroup _ domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope _ domainProvenance prior history historyWellFormed historyGenerated tailBound entries scopes owners
      ih seedIH historyIH ownerIH =>
    intro index need member
    cases index with
    | zero => trivial
    | succ index => exact ih index need member

/-- Every hidden owner extension inherits all outer common caps. Its new
original binders get exactly the finite inputs of their retained guards. -/
theorem OriginalFrameExtension.generateCappedScope
    {base : OriginalCaptureBase env U registry target}
    {startContext : ContextDerivation sourceEnv U startSource}
    {graph : OriginalCaptureMap (common := common) startContext raw}
    {start : RawOriginalRichFrame sourceEnv env U registry target startContext startLocals startLeft startRight startAvailable}
    {context : ContextDerivation sourceEnv U source}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (extension : OriginalFrameExtension start frame)
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph start) :
    ∃ nextCommon nextRaw nextLeft nextRight nextCaps,
      ∃ nextGraph : OriginalCaptureMap (common := nextCommon) context nextRaw,
      CappedCaptureGenerated base nextCaps nextLeft nextRight nextGraph frame ∧
      nextRaw = raw.liftN extension.length ∧
      Ctx.Lift' (.skipN .refl extension.length) common nextCommon ∧
      Subst.lift_l (.skipN .refl extension.length) nextLeft = commonLeft ∧
      Subst.lift_l (.skipN .refl extension.length) nextRight = commonRight ∧
      (fun index => nextCaps ((Lift.skipN .refl extension.length).liftVar index)) = commonCaps := by
  induction extension with
  | refl => exact ⟨_, _, _, _, _, graph, generated, rfl, .refl, rfl, rfl, rfl⟩
  | bind previous domain certificate resources typed arguments needs bounded covered ih =>
    obtain ⟨nextCommon, nextRaw, nextLeft, nextRight, nextCaps, nextGraph, nextGenerated,
      rawEq, insertion, leftTail, rightTail, capsTail⟩ := ih
    refine ⟨_, nextRaw.lift, _, _, _, .bind nextGraph domain _ rfl,
      .bind nextGenerated domain _ rfl certificate resources typed arguments needs bounded covered,
      ?_, .skip insertion, ?_, ?_, ?_⟩
    · rw [rawEq]; rfl
    · exact OriginalFactorCut.capture_tail_cons _ _ _ _ leftTail
    · exact OriginalFactorCut.capture_tail_cons _ _ _ _ rightTail
    · exact capsTail

/-- The reply records a generated cap derivation, not a promise that an
arbitrary semantically available new binder demand should be accepted. -/
structure CappedGeneratedQueryReply
    (base : OriginalCaptureBase env U registry target)
    (commonCaps : CaptureCaps)
    (display : OriginalNestedDisplay U common expression assigned)
    (commonLeft commonRight : Subst) (requested : Profile n) where
  reply : GeneratedQueryReply base display commonLeft commonRight requested
  capped : CappedCaptureGenerated base commonCaps commonLeft commonRight display.graph reply.realization.frame.raw

theorem GeneratedQueryReply.merge_capped
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {p q : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (left : GeneratedQueryReply base display commonLeft commonRight p)
    (right : GeneratedQueryReply base display commonLeft commonRight q)
    (leftCap : CappedCaptureGenerated base commonCaps commonLeft commonRight display.graph left.realization.frame.raw)
    (rightCap : CappedCaptureGenerated base commonCaps commonLeft commonRight display.graph right.realization.frame.raw) :
    CappedCaptureGenerated base commonCaps commonLeft commonRight display.graph
      (left.merge henv hscoped formed right).reply.realization.frame.raw := by
  rcases left with ⟨leftLocals, leftAvailable, leftFrame, leftGenerated, leftQuery, leftClosed⟩
  rcases right with ⟨rightLocals, rightAvailable, rightFrame, rightGenerated, rightQuery, rightClosed⟩
  have localsEq : leftLocals = rightLocals :=
    leftGenerated.locals_eq.trans rightGenerated.locals_eq.symm
  cases localsEq
  exact .merge leftCap rightCap

noncomputable def CappedGeneratedQueryReply.union
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {p q : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (left : CappedGeneratedQueryReply base commonCaps display commonLeft commonRight p)
    (right : CappedGeneratedQueryReply base commonCaps display commonLeft commonRight q) :
    CappedGeneratedQueryReply base commonCaps display commonLeft commonRight (p.union q) :=
  ⟨left.reply.union henv hscoped formed right.reply,
    left.reply.merge_capped henv hscoped formed right.reply left.capped right.capped⟩

/-- The returned body's exact finite footprint can be packed under the
unchanged row input even when captured slots acquired new resources. -/
theorem CappedCaptureGenerated.packBody
    {base : OriginalCaptureBase env U registry target}
    {commonCaps : CaptureCaps} {input : Profile n}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    {displayed : A.subst raw = annotation}
    {frame : RawOriginalRichFrame sourceEnv env U registry target (.cons context domain)
      locals σ τ available}
    (capped : CappedCaptureGenerated base (commonCaps.push (Need.Fits (input : Profile n)))
      commonLeft commonRight (.bind graph domain annotation displayed) frame)
    (resources : required.Available available) :
    ∃ packed outside, BinderPack n packed required outside ∧
      (∀ atom ∈ packed.atoms, atom ∈ input.atoms) ∧
      outside.Available (fun index => available (index + 1)) := by
  have bounded := capped.availableBound
  have resource : required.Available (Valuation.push (available 0) (fun index => available (index + 1))) := by
    intro index need member
    cases index <;> exact resources _ need member
  exact Footprint.pack_available resource
    (fun need member => (bounded 0 need member).1)
    (fun need member => (bounded 0 need member).2)


private def unweakenCapped
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    (commonLeft commonRight : Subst)
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) : Prop :=
  match graph, frame with
  | .weaken (ρ := ρ) previous _, frame =>
    CappedCaptureGenerated base (fun index => commonCaps (ρ.liftVar index))
      (Subst.lift_l ρ commonLeft) (Subst.lift_l ρ commonRight) previous frame
  | _, _ => True

private theorem unweakenCapped_merge
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {left : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable}
    {right : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable}
    (first : unweakenCapped base commonCaps commonLeft commonRight graph left)
    (second : unweakenCapped base commonCaps commonLeft commonRight graph right) :
    unweakenCapped base commonCaps commonLeft commonRight graph (.merge left right) := by
  cases graph <;> try trivial
  exact .merge first second

private theorem CappedCaptureGenerated.unweakenInvariant
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (capped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph frame) :
    unweakenCapped base commonCaps commonLeft commonRight graph frame := by
  induction capped with
  | merge _ _ first second => exact unweakenCapped_merge first second
  | identity => trivial
  | empty => trivial
  | tail => trivial
  | bind => trivial
  | reserveCapture => trivial
  | reserveBind => trivial
  | capture => trivial
  | group => trivial
  | scopedGroup => trivial
  | historyGroup => trivial
  | weaken generated insertion leftTail rightTail capsTail _ =>
    simpa only [unweakenCapped, leftTail, rightTail, capsTail] using generated

theorem CappedCaptureGenerated.unweaken
    {base : OriginalCaptureBase env U registry target} {nextCaps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {ρ : Lift} {insertion : Ctx.Lift' ρ common next}
    (generated : CappedCaptureGenerated base nextCaps nextLeft nextRight (.weaken graph insertion) frame) :
    CappedCaptureGenerated base (fun index => nextCaps (ρ.liftVar index))
      (Subst.lift_l ρ nextLeft) (Subst.lift_l ρ nextRight) graph frame :=
  generated.unweakenInvariant

theorem CappedGeneratedQueryReply.ofFrame
    {locals : List Nat} {available : Valuation}
    {base : OriginalCaptureBase env U registry target}
    (display : OriginalNestedDisplay U common expression assigned)
    (frame : OriginalRichFrame display.sourceEnv env U registry target display.context locals σ τ available)
    (capped : CappedCaptureGenerated base commonCaps commonLeft commonRight display.graph frame.raw)
    (substitutions : Ctx.SubstEq env U target σ τ display.source)
    (closed : available.AtomClosed)
    (query : RichGradedResult display.sourceEnv env U registry target display.node locals σ available requested) :
    Nonempty (CappedGeneratedQueryReply base commonCaps display commonLeft commonRight requested) := by
  obtain ⟨left, right⟩ := capped.generated.realizations
  subst σ
  subst τ
  exact ⟨⟨⟨locals, available, ⟨frame, substitutions⟩, capped.generated, query, closed⟩, capped⟩⟩

noncomputable def CappedGeneratedQueryReply.restrict
    (answer : CappedGeneratedQueryReply base commonCaps display commonLeft commonRight (input : Profile n))
    (need : Need) (bounded : need.rank ≤ n)
    (covered : ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    CappedGeneratedQueryReply base commonCaps display commonLeft commonRight need.profile :=
  ⟨answer.reply.restrict need bounded covered, answer.capped⟩

theorem CappedGeneratedQueryReply.unweaken
    {base : OriginalCaptureBase env U registry target}
    {commonCaps nextCaps : CaptureCaps}
    {display : OriginalNestedDisplay U common expression assigned}
    {ρ : Lift} (insertion : Ctx.Lift' ρ common next)
    (leftTail : Subst.lift_l ρ nextLeft = commonLeft)
    (rightTail : Subst.lift_l ρ nextRight = commonRight)
    (capsTail : (fun index => nextCaps (ρ.liftVar index)) = commonCaps)
    (answer : CappedGeneratedQueryReply base nextCaps (display.weaken insertion) nextLeft nextRight requested) :
    Nonempty (CappedGeneratedQueryReply base commonCaps display commonLeft commonRight requested) := by
  have capped := answer.capped.unweaken
  rw [leftTail, rightTail, capsTail] at capped
  exact CappedGeneratedQueryReply.ofFrame display answer.reply.realization.frame capped
    answer.reply.realization.substitutions answer.reply.closed answer.reply.query

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
