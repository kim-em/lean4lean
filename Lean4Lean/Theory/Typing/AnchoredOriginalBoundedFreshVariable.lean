import Lean4Lean.Theory.Typing.AnchoredOriginalCappedBinderGuard
import Lean4Lean.Theory.Typing.AnchoredOriginalBoundedGeneratedReply

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem subst_eta (σ : Subst) : σ.tail.cons σ.head = σ := by
  funext index
  cases index <;> rfl

def freshVariableDisplay
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (annotation : VExpr) (displayed : A.subst raw = annotation)
    (node : EndpointState sourceEnv U (A :: source) (.bvar 0) assigned)
    (provenance : EndpointProvenance (.cons context domain) node) :
    OriginalNestedDisplay U (annotation :: common) (.bvar 0) (assigned.subst raw.lift) where
  sourceEnv := sourceEnv
  source := A :: source
  sourceExpression := .bvar 0
  sourceType := assigned
  context := .cons context domain
  node := node
  provenance := provenance
  raw := raw.lift
  graph := .bind graph domain annotation displayed
  expression_eq := rfl
  type_eq := rfl

/-- A need used at an actual fresh source binder is admitted by the common
cap, even when its frame is a merge of independently generated replies. -/
theorem CappedCaptureGenerated.freshNeedBound
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    {displayed : A.subst raw = annotation}
    {frame : RawOriginalRichFrame sourceEnv env U registry target (.cons context domain)
      locals σ τ available}
    (capped : CappedCaptureGenerated base commonCaps commonLeft commonRight
      (.bind graph domain annotation displayed) frame)
    (member : need ∈ available 0) : commonCaps 0 need :=
  capped.availableBound 0 need member

/-- Activate a previously unused fresh variable at any demand within its
common input cap. One original guard is extracted from the existing frame;
its certificate is available in the exact merged parent suffix. No F/R call
or pre-existing head resource is required, and capacity is unchanged. -/
theorem boundedFreshVariable
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    {annotation : VExpr} {displayed : A.subst raw = annotation}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered)
    (child : OriginalCaptureRealization (.bind graph domain annotation displayed)
      env registry target locals commonLeft commonRight available)
    (capped : CappedCaptureGenerated base commonCaps commonLeft commonRight
      (.bind graph domain annotation displayed) child.frame.raw)
    (closed : available.AtomClosed)
    (node : EndpointState sourceEnv U (A :: source) (.bvar 0) assigned)
    (provenance : EndpointProvenance (.cons context domain) node)
    (need : Need) (fits : commonCaps 0 need) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps
      (freshVariableDisplay graph domain annotation displayed node provenance)
      commonLeft commonRight need.profile (environmentCost (child.frame.dependencyEnvironment ordered))) := by
  obtain ⟨guard⟩ := capped.binderGuard
  obtain ⟨⟨parent, parentCapped⟩⟩ := capped.peelBinder child.frame.valid
  have localsEq := parentCapped.generated.locals_eq
  let certificate := localsEq.symm ▸ guard.certificate
  let frame := parent.frame.bind domain certificate guard.resources guard.typed guard.related
    (captureNeeds guard.input)
    (fun need member => (captureNeeds_covered guard.input need member).1)
    (fun need member => (captureNeeds_covered guard.input need member).2)
  have capEq : CaptureCaps.push (Need.Fits guard.input) (fun index => commonCaps (index + 1)) = commonCaps := by
    funext index
    cases index with
    | zero => exact guard.cap.symm
    | succ index => rfl
  have generated : CappedCaptureGenerated base commonCaps commonLeft commonRight
      (.bind graph domain annotation displayed) frame.raw := by
    have generated := CappedCaptureGenerated.bind parentCapped domain annotation displayed certificate
      guard.resources guard.typed guard.related (captureNeeds guard.input)
      (fun need member => (captureNeeds_covered guard.input need member).1)
      (fun need member => (captureNeeds_covered guard.input need member).2)
    have headLeft : (raw.lift.comp commonLeft).head = commonLeft.head := rfl
    have headRight : (raw.lift.comp commonRight).head = commonRight.head := rfl
    simpa only [frame, OriginalRichFrame.bind, capEq, headLeft, headRight, subst_eta] using generated
  have substitutions : Ctx.SubstEq env U target
      (((raw.lift.comp commonLeft).tail).cons (raw.lift.comp commonLeft).head)
      (((raw.lift.comp commonRight).tail).cons (raw.lift.comp commonRight).head) (A :: source) := by
    simpa only [subst_eta] using child.substitutions
  have parentClosed : Valuation.AtomClosed (fun index => available (index + 1)) :=
    fun index need member atom present => closed (index + 1) need member atom present
  have nextClosed := Valuation.push_atomized_closed parentClosed [⟨guard.rank, guard.input⟩]
  have bounded : ∀ actualOrdered : sourceEnv.Ordered,
      environmentCost (frame.dependencyEnvironment actualOrdered) ≤
        environmentCost (child.frame.dependencyEnvironment ordered) := by
    intro actualOrdered
    change environmentCost (.close (domain.dependencyOrigin actualOrdered)
      (parent.frame.dependencyEnvironment actualOrdered) :: parent.frame.dependencyEnvironment actualOrdered) ≤ _
    rw [generatedBinder_environmentCost]
    exact parent.domain_bound actualOrdered
  let query : RichGradedResult sourceEnv env U registry target node (Locals.push parent.locals)
      (((raw.lift.comp commonLeft).tail).cons (raw.lift.comp commonLeft).head)
      (Valuation.push (captureNeeds guard.input) (fun index => available (index + 1))) guard.input := {
    rank := guard.rank
    bound := Nat.le_refl _
    raw := guard.input
    footprint := [(0, Need.mk guard.rank guard.input)]
    observation := .legacy (.legacy (.var _ _ 0 guard.input))
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := by
      intro index need member
      cases List.mem_singleton.mp member
      exact List.mem_append_left _ (List.mem_singleton_self _)
    live := guard.related.live henv hscoped formed }
  have fitsGuard : Need.Fits guard.input need := by rw [guard.cap] at fits; exact fits
  exact BoundedGeneratedQueryReply.ofFrame
    (freshVariableDisplay graph domain annotation displayed node provenance) frame generated substitutions
    nextClosed (query.localDemand need fitsGuard.1 fitsGuard.2) bounded

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
