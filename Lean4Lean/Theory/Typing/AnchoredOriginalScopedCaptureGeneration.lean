import Lean4Lean.Theory.Typing.AnchoredOriginalRichFramePeelMeasure
import Lean4Lean.Theory.Typing.AnchoredOriginalOwnerScope
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPendingCapture

/-! A generated common display context is raw syntax. Its fresh annotation
may itself contain captured heterogeneous arguments, so it is not assigned
an invented original context derivation. Each side instead extends its own
actual original domain and frame, and the whole source action is retained. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

inductive ScopedCaptureGenerated
    (base : OriginalCaptureBase env U registry target) :
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
      (generated : ScopedCaptureGenerated base commonLeft commonRight graph frame)
      (valid : frame.Valid) :
      ScopedCaptureGenerated base commonLeft commonRight (.tail graph)
        (OriginalRichFrame.mk frame valid).fullTail.frame.raw
  | merge
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {left : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable}
      {right : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable}
      (first : ScopedCaptureGenerated base commonLeft commonRight graph left)
      (second : ScopedCaptureGenerated base commonLeft commonRight graph right) :
      ScopedCaptureGenerated base commonLeft commonRight graph (.merge left right)
  /-- Erasure may retain a finite history reserve only at a captured head.
  The stronger capped generator controls which history supplies the reserve. -/
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
      (generated : ScopedCaptureGenerated base commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance) frame)
      (closures : List Closure) :
      ScopedCaptureGenerated base commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance) (.reserve frame closures)
  | reserveBind
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {domain : EndpointRef sourceEnv U source A (.sort level)}
      {annotation : VExpr} {displayed : A.subst raw = annotation}
      {frame : RawOriginalRichFrame sourceEnv env U registry target
        (.cons context domain) locals σ τ available}
      (generated : ScopedCaptureGenerated base commonLeft commonRight
        (.bind graph domain annotation displayed) frame)
      (closures : List Closure) :
      ScopedCaptureGenerated base commonLeft commonRight
        (.bind graph domain annotation displayed) (.reserve frame closures)
  | original (generated : OriginalCaptureGenerated base graph frame) :
      ScopedCaptureGenerated base base.left base.right graph frame
  | empty (common : List VExpr) (commonLeft commonRight : Subst) :
      ScopedCaptureGenerated base commonLeft commonRight
        (.empty common : OriginalCaptureMap (sourceEnv := sourceEnv) (U := U) .nil .id)
        (.nil (locals := []) (σ := commonLeft) (τ := commonRight) (available := fun _ => []))
  | bind
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
      (generated : ScopedCaptureGenerated base commonLeft commonRight graph tail)
      (domain : EndpointRef sourceEnv U source A (.sort level))
      (annotation : VExpr) (displayed : A.subst raw = annotation)
      (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
        (support : Profile n) footprint)
      (resources : footprint.Available available) (typed : input.HasType support)
      (arguments : Related env U registry target x y (A.subst σ) input support)
      (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
      (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
      ScopedCaptureGenerated base (commonLeft.cons x) (commonRight.cons y)
        (.bind graph domain annotation displayed)
        (.bind tail domain certificate resources typed arguments needs bounded covered)
  | weaken
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
      (generated : ScopedCaptureGenerated base commonLeft commonRight graph frame)
      {ρ : Lift} (insertion : Ctx.Lift' ρ common next)
      (leftTail : Subst.lift_l ρ nextLeft = commonLeft)
      (rightTail : Subst.lift_l ρ nextRight = commonRight) :
      ScopedCaptureGenerated base nextLeft nextRight (.weaken graph insertion) frame
  | capture
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
      (generated : ScopedCaptureGenerated base commonLeft commonRight graph tail)
      (domain : EndpointRef sourceEnv U source A (.sort level))
      {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
      (initial : ContextDerivation sourceEnv U rootSource)
      (argument : EndpointState sourceEnv U source a A)
      (location : Located root argument)
      (lineage : location.contextDerivation initial = context)
      (query : RichObs sourceEnv env U registry target argument locals σ (rawInput : Profile k) argumentFootprint)
      (queryAvailable : argumentFootprint.Available available)
      (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
        (support : Profile n) footprint)
      (resources : footprint.Available available) (typed : input.HasType support)
      (arguments : Related env U registry target (a.subst σ) (a.subst τ) (A.subst σ) input support)
      (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
      (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
      ScopedCaptureGenerated base commonLeft commonRight
        (.capture graph domain graph argument ⟨_, _, _, root, initial, location, lineage.symm⟩)
        (.capture tail domain initial argument location lineage query queryAvailable certificate resources typed
          arguments needs bounded covered)
  | group
      {context : ContextDerivation headerEnv U headerSource}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame headerEnv env U registry target context locals σ τ available}
      (generated : ScopedCaptureGenerated base commonLeft commonRight graph tail)
      (domain : EndpointRef headerEnv U headerSource A (.sort level))
      {ownerContext : ContextDerivation ownerEnv U ownerSource}
      {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
      {ownerFrame : RawOriginalRichFrame ownerEnv env U registry target ownerContext ownerLocals ownerLeft ownerRight ownerAvailable}
      (ownerGenerated : ScopedCaptureGenerated base commonLeft commonRight ownerGraph ownerFrame)
      {nominalContext : ContextDerivation nominalEnv U nominalSource}
      (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
      (nominal : EndpointState nominalEnv U nominalSource argument assigned)
      (provenance : EndpointProvenance nominalContext nominal)
      (displayed : rawCapture.subst ownerRaw = argument.subst nominalRaw)
      {field : EndpointRef ownerEnv U ownerSource fieldExpression fieldType}
      {major : EndpointRef ownerEnv U ownerSource majorExpression majorType}
      (ownerOrdered : ownerEnv.Ordered) (ownerInitial : List Closure)
      (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        locals σ available ownerInitial rawCapture (rawCapture.subst ownerLeft) (rawCapture.subst ownerRight))
      (owners : ∀ entry ∈ entries, Nonempty (OriginalFrameExtension ownerFrame entry.frame.raw)) :
      ScopedCaptureGenerated base commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance)
        (.group tail domain ownerOrdered ownerInitial (richGroupedEntriesRaw entries))

  | scopedGroup
      {context : ContextDerivation headerEnv U headerSource}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame headerEnv env U registry target context locals σ τ available}
      (generated : ScopedCaptureGenerated base commonLeft commonRight graph tail)
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
      (seedScope : OriginalOwnerScope common ownerRaw commonLeft commonRight seed.depth
        (seed.owner.context seed.initialContext))
      (seedGenerated : ScopedCaptureGenerated base seedScope.left seedScope.right seedScope.graph seed.frame.raw)
      (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        locals σ available ownerInitial rawCapture leftValue rightValue)
      (scopes : ∀ entry ∈ entries, OriginalOwnerScope common ownerRaw commonLeft commonRight entry.depth
        (entry.owner.context entry.initialContext))
      (owners : ∀ entry member, ScopedCaptureGenerated base (scopes entry member).left
        (scopes entry member).right (scopes entry member).graph entry.frame.raw) :
      ScopedCaptureGenerated base commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance)
        (.group tail domain ownerOrdered ownerInitial (richGroupedEntriesRaw entries))


private theorem capture_lift_comp (raw common : Subst) (anchor : VExpr) :
    raw.lift.comp (common.cons anchor) = (raw.comp common).cons anchor := by
  funext index
  cases index <;> simp [Subst.comp, Subst.lift, Subst.cons, lift_subst_cons]

private theorem capture_weaken_comp (raw common : Subst) (ρ : Lift) :
    (raw.lift_r ρ).comp common = raw.comp (Subst.lift_l ρ common) := by
  funext index
  exact subst_lift'

/-- Realization is derived for the entire generated source map. In
particular fresh common binders require no original typing of their displayed
annotation in a synthetic common context. -/
theorem ScopedCaptureGenerated.realizations
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : ScopedCaptureGenerated base commonLeft commonRight graph frame) :
    σ = raw.comp commonLeft ∧ τ = raw.comp commonRight := by
  induction generated with
  | tail generated valid ih =>
    exact ⟨congrArg Subst.tail ih.1, congrArg Subst.tail ih.2⟩
  | merge _ _ first _ => exact first
  | reserveCapture _ _ ih => exact ih
  | reserveBind _ _ ih => exact ih
  | original generated => exact generated.realizations
  | empty => exact ⟨rfl, rfl⟩
  | bind generated domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    rw [capture_lift_comp, capture_lift_comp]
    rw [ih.1, ih.2]
    exact ⟨rfl, rfl⟩
  | weaken generated insertion leftTail rightTail ih =>
    rw [capture_weaken_comp, capture_weaken_comp, leftTail, rightTail]
    exact ih
  | capture generated domain initial argument location lineage query queryAvailable certificate resources typed
      arguments needs bounded covered ih =>
    rcases ih with ⟨left, right⟩
    constructor
    · rw [left]
      funext index
      cases index with
      | zero => exact subst_subst.symm
      | succ index => rfl
    · rw [right]
      funext index
      cases index with
      | zero => exact subst_subst.symm
      | succ index => rfl
  | group generated domain ownerGenerated nominalGraph nominal provenance displayed ownerOrdered ownerInitial entries owners ih ownerIH =>
    rcases ih with ⟨left, right⟩
    rcases ownerIH with ⟨ownerLeft, ownerRight⟩
    constructor
    · rw [left, ownerLeft]
      funext index
      cases index with
      | zero =>
        simp only [Subst.comp, Subst.cons]
        rw [← subst_subst, displayed]
      | succ index => rfl
    · rw [right, ownerRight]
      funext index
      cases index with
      | zero =>
        simp only [Subst.comp, Subst.cons]
        rw [← subst_subst, displayed]
      | succ index => rfl

  | scopedGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered ownerInitial
      seed seedScope seedGenerated entries scopes owners ih seedIH ownerIH =>
    have leftValueEq := seed.left_eq.symm
    rw [seed.expression_eq, seedIH.1, subst_lift', seedScope.leftRealization] at leftValueEq
    have rightValueEq := seed.right_eq.symm
    rw [seed.expression_eq, seedIH.2, subst_lift', seedScope.rightRealization] at rightValueEq
    constructor
    · rw [ih.1]
      funext index
      cases index with
      | zero => simpa only [Subst.cons, Subst.comp, ← subst_subst, displayed] using leftValueEq
      | succ index => rfl
    · rw [ih.2]
      funext index
      cases index with
      | zero => simpa only [Subst.cons, Subst.comp, ← subst_subst, displayed] using rightValueEq
      | succ index => rfl


theorem ScopedCaptureGenerated.groupOfValues
    {base : OriginalCaptureBase env U registry target}
      {context : ContextDerivation headerEnv U headerSource}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame headerEnv env U registry target context locals σ τ available}
      (generated : ScopedCaptureGenerated base commonLeft commonRight graph tail)
      (domain : EndpointRef headerEnv U headerSource A (.sort level))
      {ownerContext : ContextDerivation ownerEnv U ownerSource}
      {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
      {ownerFrame : RawOriginalRichFrame ownerEnv env U registry target ownerContext ownerLocals ownerLeft ownerRight ownerAvailable}
      (ownerGenerated : ScopedCaptureGenerated base commonLeft commonRight ownerGraph ownerFrame)
      {nominalContext : ContextDerivation nominalEnv U nominalSource}
      (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
      (nominal : EndpointState nominalEnv U nominalSource argument assigned)
      (provenance : EndpointProvenance nominalContext nominal)
      (displayed : rawCapture.subst ownerRaw = argument.subst nominalRaw)
      {field : EndpointRef ownerEnv U ownerSource fieldExpression fieldType}
      {major : EndpointRef ownerEnv U ownerSource majorExpression majorType}
      (ownerOrdered : ownerEnv.Ordered) (ownerInitial : List Closure)
      (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        locals σ available ownerInitial rawCapture leftValue rightValue)
      (owners : ∀ entry ∈ entries, Nonempty (OriginalFrameExtension ownerFrame entry.frame.raw))
      (leftEq : leftValue = rawCapture.subst ownerLeft)
      (rightEq : rightValue = rawCapture.subst ownerRight) :
      ScopedCaptureGenerated base commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance)
        (.group tail domain ownerOrdered ownerInitial (richGroupedEntriesRaw entries)) := by
  cases leftEq
  cases rightEq
  exact .group generated domain ownerGenerated nominalGraph nominal provenance displayed
    ownerOrdered ownerInitial entries owners


/-- Lift generation through the EXACT original binder trace emitted by query
traversal. This computes the common raw annotations and both common maps,
while retaining the already-constructed original occurrence frame. -/
theorem OriginalFrameExtension.generateScope
    {base : OriginalCaptureBase env U registry target}
    {startContext : ContextDerivation sourceEnv U startSource}
    {graph : OriginalCaptureMap (common := common) startContext raw}
    {start : RawOriginalRichFrame sourceEnv env U registry target startContext startLocals startLeft startRight startAvailable}
    {context : ContextDerivation sourceEnv U source}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (extension : OriginalFrameExtension start frame)
    (generated : ScopedCaptureGenerated base commonLeft commonRight graph start) :
    ∃ nextCommon nextRaw nextLeft nextRight,
      ∃ nextGraph : OriginalCaptureMap (common := nextCommon) context nextRaw,
      ScopedCaptureGenerated base nextLeft nextRight nextGraph frame ∧
      nextRaw = raw.liftN extension.length ∧
      Ctx.Lift' (.skipN .refl extension.length) common nextCommon ∧
      Subst.lift_l (.skipN .refl extension.length) nextLeft = commonLeft ∧
      Subst.lift_l (.skipN .refl extension.length) nextRight = commonRight := by
  induction extension with
  | refl => exact ⟨_, _, _, _, graph, generated, rfl, .refl, rfl, rfl⟩
  | bind previous domain certificate resources typed arguments needs bounded covered ih =>
    obtain ⟨nextCommon, nextRaw, nextLeft, nextRight, nextGraph, nextGenerated, rawEq, insertion, leftTail, rightTail⟩ := ih
    refine ⟨_, nextRaw.lift, _, _,
      .bind nextGraph domain _ rfl,
      .bind nextGenerated domain _ rfl certificate resources typed arguments needs bounded covered,
      ?_, .skip insertion, ?_, ?_⟩
    · rw [rawEq]; rfl
    · exact capture_tail_cons _ _ _ _ leftTail
    · exact capture_tail_cons _ _ _ _ rightTail


private def unweakenGenerated
    (base : OriginalCaptureBase env U registry target) (commonLeft commonRight : Subst)
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) : Prop :=
  match graph, frame with
  | .weaken (ρ := ρ) previous _, frame =>
    ScopedCaptureGenerated base (Subst.lift_l ρ commonLeft) (Subst.lift_l ρ commonRight) previous frame
  | _, _ => True

private theorem unweakenGenerated_merge
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {left : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable}
    {right : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable}
    (first : unweakenGenerated base commonLeft commonRight graph left)
    (second : unweakenGenerated base commonLeft commonRight graph right) :
    unweakenGenerated base commonLeft commonRight graph (.merge left right) := by
  cases graph <;> try trivial
  exact .merge first second

private theorem ScopedCaptureGenerated.unweakenInvariant
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : ScopedCaptureGenerated base commonLeft commonRight graph frame) :
    unweakenGenerated base commonLeft commonRight graph frame := by
  induction generated with
  | merge _ _ first second => exact unweakenGenerated_merge first second
  | original generated => cases generated <;> trivial
  | empty => trivial
  | tail => trivial
  | bind => trivial
  | capture => trivial
  | group => trivial
  | scopedGroup => trivial
  | reserveCapture => trivial
  | reserveBind => trivial
  | weaken generated insertion leftTail rightTail _ =>
    simpa only [unweakenGenerated, leftTail, rightTail] using generated

/-- An answer reconstructed below a common source weakening can be returned
at the original destination scope. Its actual source frame is unchanged. -/
theorem ScopedCaptureGenerated.unweaken
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {ρ : Lift} {insertion : Ctx.Lift' ρ common next}
    (generated : ScopedCaptureGenerated base nextLeft nextRight (.weaken graph insertion) frame) :
    ScopedCaptureGenerated base (Subst.lift_l ρ nextLeft) (Subst.lift_l ρ nextRight) graph frame :=
  generated.unweakenInvariant

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
