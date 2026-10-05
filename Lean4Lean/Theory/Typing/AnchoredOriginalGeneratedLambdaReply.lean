import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedLambdaDisplays
import Lean4Lean.Theory.Typing.AnchoredOriginalCappedBinderPeel
import Lean4Lean.Theory.Typing.AnchoredOriginalBoundedGeneratedReply
import Lean4Lean.Theory.Typing.AnchoredOriginalRichGradedLambda

/-! Close a query-selected lambda body at its actual original binder.
The output retains both the domain's resources and the body's new captures;
fresh binder caps and exact binder cost cancellation preserve the input budget. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem lift_comp (raw commonLeft : Subst) (anchor : VExpr) :
    raw.lift.comp (commonLeft.cons anchor) = (raw.comp commonLeft).cons anchor := by
  funext index
  cases index <;> simp [Subst.comp, Subst.lift, Subst.cons]

theorem boundedGeneratedLambdaReply
    {base : OriginalCaptureBase env U registry target}
    {commonCaps : CaptureCaps}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {codomain : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {body : EndpointState sourceEnv U (A :: source) b B}
    {hu : u.WF U} {hv : v.WF U}
    (location : Located root (.lam hu hv (.ref domain) codomain body))
    (initial : ContextDerivation sourceEnv U rootSource)
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (annotationEq : annotation = A.subst raw)
    (bodyEq : displayedBody = b.subst raw.lift)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered)
    (original : OriginalCaptureRealization graph env registry target
      (graph.locals base.locals) commonLeft commonRight available)
    (originalCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph original.frame.raw)
    (closed : available.AtomClosed)
    (domainCode : RichCert sourceEnv env U registry target (.ref domain)
      (graph.locals base.locals) (raw.comp commonLeft) true (ambient : Profile n) domainFootprint)
    (domainResources : domainFootprint.Available available)
    (key : Key n) (output : Atom n)
    (guard : LambdaGuard env U registry target (raw.comp commonLeft) A key ambient)
    (answer : BoundedGeneratedQueryReply base (commonCaps.push (Need.Fits key.input))
      (OriginalNestedDisplay.lambdaBody location initial graph annotationEq bodyEq)
      (commonLeft.cons key.anchor) (commonRight.cons key.anchor) (.singleton output)
      ((domain.dependencyOrigin ordered).weight * (1 + environmentCost (original.frame.dependencyEnvironment ordered)))) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps
      (OriginalNestedDisplay.lambda location initial graph annotationEq bodyEq)
      commonLeft commonRight (Profile.fn key output)
      (environmentCost (original.frame.dependencyEnvironment ordered))) := by
  obtain ⟨parentLocals, parent, parentCapped, _positions, _parentBound, parentDomainBound⟩ :=
    answer.answer.reply.realization.peelCappedBinder answer.answer.capped
  have same : parentLocals = graph.locals base.locals := parentCapped.generated.locals_eq
  subst parentLocals
  let nextAvailable := available.append (fun index => answer.answer.reply.available (index + 1))
  let next : OriginalCaptureRealization graph env registry target
      (graph.locals base.locals) commonLeft commonRight nextAvailable :=
    ⟨original.frame.merge parent.frame, original.substitutions⟩
  have nextCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph next.frame.raw :=
    .merge originalCapped parentCapped
  have nextClosed : nextAvailable.AtomClosed := by
    intro index need member selected present
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append_left _ (closed index need member selected present)
    · exact List.mem_append_right _ (answer.answer.reply.closed (index + 1) need member selected present)
  let needs := answer.answer.reply.available 0
  have needsBounded : ∀ need ∈ needs, need.rank ≤ n :=
    fun need member => (answer.answer.capped.availableBound 0 need member).1
  have needsCovered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms :=
    fun need member => (answer.answer.capped.availableBound 0 need member).2
  have included : ∀ index need, need ∈ answer.answer.reply.available index →
      need ∈ (nextAvailable.push needs) index := by
    intro index need member
    cases index with
    | zero => exact member
    | succ index => exact List.mem_append_right _ member
  have bodyClosed : (nextAvailable.push needs).AtomClosed := by
    intro index need member selected present
    cases index with
    | zero => exact answer.answer.reply.closed 0 need member selected present
    | succ index => exact nextClosed index need member selected present
  have localsEq : answer.answer.reply.locals = Locals.push (graph.locals base.locals) :=
    answer.answer.reply.locals_eq
  have bodyQuery : RichGradedResult sourceEnv env U registry target body
      (Locals.push (graph.locals base.locals)) ((raw.comp commonLeft).cons key.anchor)
      (nextAvailable.push needs) (.singleton output) := by
    simpa only [OriginalNestedDisplay.lambdaBody, localsEq, lift_comp] using
      answer.answer.reply.query.availableMono included
  have domainAvailable : domainFootprint.Available nextAvailable :=
    fun index need member => List.mem_append_left _ (domainResources index need member)
  obtain ⟨query⟩ := RichGradedResult.lam henv hscoped formed nextClosed codomain hu hv
    domainCode domainAvailable guard needs needsBounded
    (fun need member _ present => needsCovered need member _ present) bodyQuery bodyClosed
  refine ⟨⟨⟨⟨graph.locals base.locals, nextAvailable, next, nextCapped.generated, query, nextClosed⟩,
    nextCapped⟩, ?_⟩⟩
  intro otherOrdered
  have bodyBound := answer.bounded otherOrdered
  have bodyBound := Nat.le_trans (parentDomainBound otherOrdered) bodyBound
  have parentBound := generatedBinder_cancel (domain.dependencyOrigin ordered)
    (environmentCost (parent.frame.dependencyEnvironment ordered))
    (environmentCost (original.frame.dependencyEnvironment ordered)) bodyBound
  change environmentCost ((original.frame.merge parent.frame).dependencyEnvironment otherOrdered) ≤ _
  rw [OriginalRichFrame.merge_environmentCost]
  exact Nat.max_le.mpr ⟨Nat.le_refl _, parentBound⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
