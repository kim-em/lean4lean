import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedPiRow
import Lean4Lean.Theory.Typing.AnchoredOriginalCappedBinderPeel

/-! Close an actual query-selected Pi body over its reconstructed parent
frame. The original domain resources and all new captured body resources
are retained by a nonrecursive merge of their actual generated frames. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- The returned source certificate is a native Pi at the exact original
right domain/body occurrences. It uses the frozen row key unchanged. -/
theorem CappedGeneratedQueryReply.piCode
    {base : OriginalCaptureBase env U registry target}
    {commonCaps : CaptureCaps}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (location : Located root (.pi hu hv (.ref domain) body))
    (initial : ContextDerivation sourceEnv U rootSource)
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (annotationEq : annotation = A.subst raw)
    (bodyEq : displayedBody = B.subst raw.lift)
    (henv : env.Ordered)
    (original : OriginalCaptureRealization graph env registry target
      (graph.locals base.locals) commonLeft commonRight available)
    (originalCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph original.frame.raw)
    (closed : available.AtomClosed)
    (domainCode : RichCert sourceEnv env U registry target (.ref domain)
      (graph.locals base.locals) (raw.comp commonLeft) true (ambient : Profile n) domainFootprint)
    (domainResources : domainFootprint.Available available)
    (piGuard : PiGuard env U target (raw.comp commonLeft) A B prototypeDomain prototypeBody)
    (key : Key n) (output : Profile n)
    (guard : LambdaGuard env U registry target (raw.comp commonLeft) A key ambient)
    (sorted : output.HasType (.sort relevant))
    (answer : CappedGeneratedQueryReply base (commonCaps.push (Need.Fits key.input))
      (OriginalNestedDisplay.piBody location initial graph annotationEq bodyEq)
      (commonLeft.cons key.anchor) (commonRight.cons key.anchor) output) :
    ∃ nextAvailable, ∃ next : OriginalCaptureRealization graph env registry target
        (graph.locals base.locals) commonLeft commonRight nextAvailable,
      CappedCaptureGenerated base commonCaps commonLeft commonRight graph next.frame.raw ∧
      nextAvailable.AtomClosed ∧
      (∀ index need, need ∈ available index → need ∈ nextAvailable index) ∧
      (∀ ordered : sourceEnv.Ordered,
        environmentCost (next.frame.dependencyEnvironment ordered) ≤
          max (environmentCost (original.frame.dependencyEnvironment ordered))
            (environmentCost (answer.reply.realization.frame.dependencyEnvironment ordered))) ∧
      ∃ required, Nonempty (RichCert sourceEnv env U registry target (.pi hu hv (.ref domain) body)
        (graph.locals base.locals) (raw.comp commonLeft) relevant
        (Profile.pi prototypeDomain prototypeBody ambient [(key, output)]) required) ∧
        required.Available nextAvailable := by
  obtain ⟨outside, ⟨rows⟩, rowResources⟩ :=
    answer.piRow location initial graph annotationEq bodyEq henv key ambient output guard sorted
  obtain ⟨parentLocals, parent, parentCapped, _positions, parentBound, _parentDomainBound⟩ :=
    answer.reply.realization.peelCappedBinder answer.capped
  have same : parentLocals = graph.locals base.locals := parentCapped.generated.locals_eq
  subst parentLocals
  let nextAvailable := available.append (fun index => answer.reply.available (index + 1))
  let next : OriginalCaptureRealization graph env registry target
      (graph.locals base.locals) commonLeft commonRight nextAvailable :=
    ⟨original.frame.merge parent.frame, original.substitutions⟩
  have nextCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph next.frame.raw :=
    .merge originalCapped parentCapped
  refine ⟨nextAvailable, next, nextCapped, ?_, ?_, ?_, domainFootprint ++ outside,
    ⟨.pi hu hv domainCode piGuard rows⟩, ?_⟩
  · intro index need member selected selectedMember
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append_left _ (closed index need member selected selectedMember)
    · exact List.mem_append_right _ (answer.reply.closed (index + 1) need member selected selectedMember)
  · intro index need member
    exact List.mem_append_left _ member
  · intro ordered
    rw [OriginalRichFrame.merge_environmentCost]
    exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
      Nat.le_trans (parentBound ordered) (Nat.le_max_right _ _)⟩
  · intro index need member
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append_left _ (domainResources index need member)
    · exact List.mem_append_right _ (rowResources index need member)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
