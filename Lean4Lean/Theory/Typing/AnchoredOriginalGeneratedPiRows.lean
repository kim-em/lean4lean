import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedPiCode

/-! Finite native Pi row replies are combined independently. Every row has
its own generated captured resources, while their common original binder
cap is fixed before the recursive replies are computed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def RichRows.append
    (first : RichRows sourceEnv env U registry target domain body locals σ relevant ambient firstRows firstFootprint)
    (second : RichRows sourceEnv env U registry target domain body locals σ relevant ambient secondRows secondFootprint) :
    RichRows sourceEnv env U registry target domain body locals σ relevant ambient
      (firstRows ++ secondRows) (firstFootprint ++ secondFootprint) := by
  match first with
  | .nil => exact second
  | .cons guard certificate pack covered tail =>
    simpa only [List.cons_append, List.append_assoc] using
      RichRows.cons guard certificate pack covered (tail.append second)
termination_by firstRows.length
decreasing_by simp_wf

section
variable
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
    (commonLeft commonRight : Subst) (ambient : Profile n) (relevant : Bool)

/-- Actual finite lower-recursion answers, with their original body queries
and generated frames. No outgoing row or ambient code supplier is stored. -/
inductive CappedPiRowAnswers : List (Key n × Profile n) → Type where
  | nil : CappedPiRowAnswers []
  | cons (key : Key n) (output : Profile n)
      (guard : LambdaGuard env U registry target (raw.comp commonLeft) A key ambient)
      (sorted : output.HasType (.sort relevant))
      (answer : CappedGeneratedQueryReply base (commonCaps.push (Need.Fits key.input))
        (OriginalNestedDisplay.piBody location initial graph annotationEq bodyEq)
        (commonLeft.cons key.anchor) (commonRight.cons key.anchor) output)
      (tail : CappedPiRowAnswers rows) : CappedPiRowAnswers ((key, output) :: rows)

variable {location initial graph annotationEq bodyEq commonLeft commonRight ambient relevant}

/-- Each body answer is bounded by its own actual original fresh-binder
frame above the fixed parent, independently of other row answers. -/
def CappedPiRowAnswers.Bounded
    (answers : CappedPiRowAnswers (base := base) (commonCaps := commonCaps)
      location initial graph annotationEq bodyEq commonLeft commonRight ambient relevant rows)
    (original : OriginalCaptureRealization graph env registry target
      (graph.locals base.locals) commonLeft commonRight available) : Prop :=
  match answers with
  | .nil => True
  | .cons _ _ _ _ answer tail =>
      (∀ ordered : sourceEnv.Ordered,
        environmentCost (answer.reply.realization.frame.dependencyEnvironment ordered) ≤
          (domain.dependencyOrigin ordered).weight *
            (1 + environmentCost (original.frame.dependencyEnvironment ordered))) ∧ tail.Bounded original

/-- Closing all rows reconstructs their actual parent frames and merges
those frames without another recursive call. The exact binder equation
cancels each body capacity back to the unchanged parent capacity. -/
theorem CappedPiRowAnswers.assemble
    (henv : env.Ordered)
    (answers : CappedPiRowAnswers (base := base) (commonCaps := commonCaps)
      location initial graph annotationEq bodyEq commonLeft commonRight ambient relevant rows)
    (original : OriginalCaptureRealization graph env registry target
      (graph.locals base.locals) commonLeft commonRight available)
    (originalCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph original.frame.raw)
    (closed : available.AtomClosed)
    (bounded : answers.Bounded original) :
    ∃ nextAvailable, ∃ next : OriginalCaptureRealization graph env registry target
        (graph.locals base.locals) commonLeft commonRight nextAvailable,
      CappedCaptureGenerated base commonCaps commonLeft commonRight graph next.frame.raw ∧
      nextAvailable.AtomClosed ∧
      (∀ index need, need ∈ available index → need ∈ nextAvailable index) ∧
      (∀ ordered : sourceEnv.Ordered,
        environmentCost (next.frame.dependencyEnvironment ordered) ≤
          environmentCost (original.frame.dependencyEnvironment ordered)) ∧
      ∃ required, Nonempty (RichRows sourceEnv env U registry target (.ref domain) body
        (graph.locals base.locals) (raw.comp commonLeft) relevant ambient rows required) ∧
        required.Available nextAvailable := by
  induction answers with
  | nil =>
    exact ⟨available, original, originalCapped, closed, fun _ _ member => member,
      fun _ => Nat.le_refl _, [], ⟨.nil⟩, fun _ _ member => nomatch member⟩
  | cons key output guard sorted answer tail ih =>
    obtain ⟨tailAvailable, tailFrame, tailCapped, tailClosed, tailIncludes, tailBound,
      tailFootprint, ⟨tailRows⟩, tailResources⟩ := ih bounded.2
    obtain ⟨outside, ⟨headRows⟩, headResources⟩ :=
      answer.piRow location initial graph annotationEq bodyEq henv key ambient output guard sorted
    obtain ⟨parentLocals, parent, parentCapped, _positions, _parentBound, parentDomainBound⟩ :=
      answer.reply.realization.peelCappedBinder answer.capped
    have same : parentLocals = graph.locals base.locals := parentCapped.generated.locals_eq
    subst parentLocals
    have parentBound : ∀ ordered : sourceEnv.Ordered,
        environmentCost (parent.frame.dependencyEnvironment ordered) ≤
          environmentCost (original.frame.dependencyEnvironment ordered) := by
      intro ordered
      apply generatedBinder_cancel (domain.dependencyOrigin ordered)
      exact Nat.le_trans (parentDomainBound ordered) (bounded.1 ordered)
    let nextAvailable := tailAvailable.append (fun index => answer.reply.available (index + 1))
    let next : OriginalCaptureRealization graph env registry target
        (graph.locals base.locals) commonLeft commonRight nextAvailable :=
      ⟨tailFrame.frame.merge parent.frame, tailFrame.substitutions⟩
    refine ⟨nextAvailable, next, .merge tailCapped parentCapped, ?_, ?_, ?_,
      outside ++ tailFootprint, ⟨headRows.append tailRows⟩, ?_⟩
    · intro index need member selected selectedMember
      rcases List.mem_append.mp member with member | member
      · exact List.mem_append_left _ (tailClosed index need member selected selectedMember)
      · exact List.mem_append_right _ (answer.reply.closed (index + 1) need member selected selectedMember)
    · intro index need member
      exact List.mem_append_left _ (tailIncludes index need member)
    · intro ordered
      rw [OriginalRichFrame.merge_environmentCost]
      exact Nat.max_le.mpr ⟨tailBound ordered, parentBound ordered⟩
    · intro index need member
      rcases List.mem_append.mp member with member | member
      · exact List.mem_append_right _ (headResources index need member)
      · exact List.mem_append_left _ (tailResources index need member)

/-- Full finite native Pi reconstruction, with the actual domain query and
all independently generated body queries available at one capped frame. -/
theorem CappedPiRowAnswers.piCode
    (henv : env.Ordered)
    (answers : CappedPiRowAnswers (base := base) (commonCaps := commonCaps)
      location initial graph annotationEq bodyEq commonLeft commonRight ambient relevant rows)
    (original : OriginalCaptureRealization graph env registry target
      (graph.locals base.locals) commonLeft commonRight available)
    (originalCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph original.frame.raw)
    (closed : available.AtomClosed)
    (bounded : answers.Bounded original)
    (domainCode : RichCert sourceEnv env U registry target (.ref domain)
      (graph.locals base.locals) (raw.comp commonLeft) true ambient domainFootprint)
    (domainResources : domainFootprint.Available available)
    (piGuard : PiGuard env U target (raw.comp commonLeft) A B prototypeDomain prototypeBody) :
    ∃ nextAvailable, ∃ next : OriginalCaptureRealization graph env registry target
        (graph.locals base.locals) commonLeft commonRight nextAvailable,
      CappedCaptureGenerated base commonCaps commonLeft commonRight graph next.frame.raw ∧
      nextAvailable.AtomClosed ∧
      (∀ index need, need ∈ available index → need ∈ nextAvailable index) ∧
      (∀ ordered : sourceEnv.Ordered,
        environmentCost (next.frame.dependencyEnvironment ordered) ≤
          environmentCost (original.frame.dependencyEnvironment ordered)) ∧
      ∃ required, Nonempty (RichCert sourceEnv env U registry target (.pi hu hv (.ref domain) body)
        (graph.locals base.locals) (raw.comp commonLeft) relevant
        (Profile.pi prototypeDomain prototypeBody ambient rows) required) ∧
        required.Available nextAvailable := by
  obtain ⟨nextAvailable, next, capped, nextClosed, included, bound, required, ⟨codeRows⟩, resources⟩ :=
    answers.assemble henv original originalCapped closed bounded
  refine ⟨nextAvailable, next, capped, nextClosed, included, bound, domainFootprint ++ required,
    ⟨.pi hu hv domainCode piGuard codeRows⟩, ?_⟩
  intro index need member
  rcases List.mem_append.mp member with member | member
  · exact included index need (domainResources index need member)
  · exact resources index need member
end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
