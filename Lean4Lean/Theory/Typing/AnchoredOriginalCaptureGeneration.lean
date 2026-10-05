import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureGraph
import Lean4Lean.Theory.Typing.AnchoredOriginalFrameExtension

/-! Generated realizations of recursive original source maps. The common
source frame is fixed once. Capture constructors retain their actual frame
construction and each grouped owner's source graph; equal realized target
terms alone are not a generation rule. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

structure OriginalCaptureBase (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) where
  sourceEnv : VEnv
  source : List VExpr
  context : ContextDerivation sourceEnv U source
  locals : List Nat
  left : Subst
  right : Subst
  available : Valuation
  frame : OriginalRichFrame sourceEnv env U registry target context locals left right available
  substitutions : Ctx.SubstEq env U target left right source

inductive OriginalCaptureGenerated
    (base : OriginalCaptureBase env U registry target) :
    {sourceEnv : VEnv} → {source : List VExpr} →
    {context : ContextDerivation sourceEnv U source} → {raw : Subst} →
    {locals : List Nat} → {σ τ : Subst} → {available : Valuation} →
    OriginalCaptureMap (common := base.source) context raw →
    RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available → Prop where
  | identity : OriginalCaptureGenerated base (.identity base.context) base.frame.raw
  | empty : OriginalCaptureGenerated base
      (.empty base.source : OriginalCaptureMap (sourceEnv := sourceEnv) (U := U) .nil .id)
      (.nil (locals := []) (σ := base.left) (τ := base.right) (available := fun _ => []))
  | capture
      {context : ContextDerivation sourceEnv U source}
      {graph : OriginalCaptureMap (common := base.source) context raw}
      {tail : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
      (generated : OriginalCaptureGenerated base graph tail)
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
      OriginalCaptureGenerated base
        (.capture graph domain graph argument
          ⟨_, _, _, root, initial, location, lineage.symm⟩)
        (.capture tail domain initial argument location lineage query queryAvailable certificate resources typed
          arguments needs bounded covered)
  | group
      {context : ContextDerivation headerEnv U headerSource}
      {graph : OriginalCaptureMap (common := base.source) context raw}
      {tail : RawOriginalRichFrame headerEnv env U registry target context locals σ τ available}
      (generated : OriginalCaptureGenerated base graph tail)
      (domain : EndpointRef headerEnv U headerSource A (.sort level))
      {ownerContext : ContextDerivation ownerEnv U ownerSource}
      (ownerGraph : OriginalCaptureMap (common := base.source) ownerContext ownerRaw)
      (owner : EndpointState ownerEnv U ownerSource argument assigned)
      (provenance : EndpointProvenance ownerContext owner)
      {field : EndpointRef base.sourceEnv U base.source fieldExpression fieldType}
      {major : EndpointRef base.sourceEnv U base.source majorExpression majorType}
      (capturedOrdered : base.sourceEnv.Ordered) (ownerInitial : List Closure)
      (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        locals σ available ownerInitial (argument.subst ownerRaw)
        ((argument.subst ownerRaw).subst base.left) ((argument.subst ownerRaw).subst base.right))
      (owners : ∀ entry ∈ entries,
        Nonempty (OriginalFrameExtension base.frame.raw entry.frame.raw)) :
      OriginalCaptureGenerated base (.capture graph domain ownerGraph owner provenance)
        (.group tail domain capturedOrdered ownerInitial (richGroupedEntriesRaw entries))

/-- Generated frames realize the whole source action, not merely the one
expression selected for the present query. -/
theorem OriginalCaptureGenerated.realizations
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := base.source) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : OriginalCaptureGenerated base graph frame) :
    σ = raw.comp base.left ∧ τ = raw.comp base.right := by
  induction generated with
  | identity => exact ⟨rfl, rfl⟩
  | empty => exact ⟨rfl, rfl⟩
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
  | group generated domain ownerGraph owner provenance capturedOrdered ownerInitial entries owners ih =>
    rcases ih with ⟨left, right⟩
    constructor
    · rw [left]
      funext index
      cases index <;> rfl
    · rw [right]
      funext index
      cases index <;> rfl


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
