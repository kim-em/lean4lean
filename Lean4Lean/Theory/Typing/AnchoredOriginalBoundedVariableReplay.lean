import Lean4Lean.Theory.Typing.AnchoredOriginalBoundedFreshVariable
import Lean4Lean.Theory.Typing.AnchoredOriginalRichVariableQueries
import Lean4Lean.Theory.Typing.AnchoredSortableVariableTrace

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem atomAction
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {a b : Atom n}
    (reply : BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight (.singleton a) capacity)
    (action : AtomAction env U registry target a b) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight (.singleton b) capacity) := by
  obtain ⟨query⟩ := reply.answer.reply.query.action henv hscoped formed action
  exact ⟨reply.mapQuery query⟩

private theorem replayLegacyVariable
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (emptyReply : ∀ n, BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight
      (.empty : Profile n) capacity)
    (leaf : ∀ need, need ∈ available index →
      Nonempty (BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight need.profile capacity))
    (trace : VariableTrace env U registry target index (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight profile capacity) := by
  induction trace with
  | leaf demand => exact leaf _ (resources _ _ List.mem_cons_self)
  | empty => exact ⟨emptyReply _⟩
  | union left right ihleft ihright =>
    obtain ⟨a⟩ := ihleft (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨b⟩ := ihright (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨a.union henv hscoped formed b⟩
  | view source view ih =>
    obtain ⟨a⟩ := ih resources
    exact atomAction henv hscoped formed a (.view view)
  | pad source ih =>
    obtain ⟨a⟩ := ih resources
    exact ⟨a.pad henv hscoped formed⟩
  | unpad source ih =>
    obtain ⟨a⟩ := ih resources
    exact ⟨a.unpad⟩
  | rowShift source ih =>
    obtain ⟨a⟩ := ih resources
    exact atomAction henv hscoped formed (a.pad henv hscoped formed) (.view (.commutePadFn _ _))

private theorem replaySortableVariable
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (emptyReply : ∀ n, BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight
      (.empty : Profile n) capacity)
    (leaf : ∀ need, need ∈ available index →
      Nonempty (BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight need.profile capacity))
    (trace : SortableVariableTrace env U registry target index (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight profile capacity) := by
  induction trace with
  | legacy trace => exact replayLegacyVariable henv hscoped formed emptyReply leaf trace resources
  | union left right ihleft ihright =>
    obtain ⟨a⟩ := ihleft (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨b⟩ := ihright (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨a.union henv hscoped formed b⟩
  | code source action sorted ih =>
    obtain ⟨a⟩ := ih resources
    exact ⟨a.codeAdapter henv hscoped formed action sorted⟩
  | action source action ih =>
    obtain ⟨a⟩ := ih resources
    exact atomAction henv hscoped formed a action
  | pad source ih =>
    obtain ⟨a⟩ := ih resources
    exact ⟨a.pad henv hscoped formed⟩
  | unpad source ih =>
    obtain ⟨a⟩ := ih resources
    exact ⟨a.unpad⟩

/-- Full variable-query reconstruction separates finite syntax replay from
actual source-slot lookup. Every requested leaf is witnessed by original
resource membership; code/action/grade wrappers are retained explicitly. -/
theorem RichObs.replayBoundedVariable
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {node : EndpointState sourceEnv U source (.bvar index) sourceAssigned}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (emptyReply : ∀ n, BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight
      (.empty : Profile n) capacity)
    (leaf : ∀ need, need ∈ available index →
      Nonempty (BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight need.profile capacity))
    (closed : available.AtomClosed)
    (query : RichObs sourceEnv env U registry target node locals σ (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight profile capacity) := by
  obtain ⟨required, ⟨source⟩, supplied⟩ := query.variableQuery closed resources
  exact replaySortableVariable henv hscoped formed emptyReply leaf source.variableTrace supplied

/-- Actual fresh-source membership drives every leaf of an arbitrary rich
query at bvar 0. The destination may use a different original domain proof
and an independently merged frame. No demand-fitting premise remains. -/
theorem boundedFreshVariableQuery
    {base : OriginalCaptureBase env U registry target}
    {leftContext : ContextDerivation leftEnv U leftSource}
    {leftGraph : OriginalCaptureMap (common := common) leftContext leftRaw}
    {leftDomain : EndpointRef leftEnv U leftSource leftA (.sort leftLevel)}
    {leftDisplayed : leftA.subst leftRaw = annotation}
    {leftFrame : RawOriginalRichFrame leftEnv env U registry target (.cons leftContext leftDomain)
      leftLocals leftσ leftτ leftAvailable}
    {rightContext : ContextDerivation rightEnv U rightSource}
    {rightGraph : OriginalCaptureMap (common := common) rightContext rightRaw}
    {rightDomain : EndpointRef rightEnv U rightSource rightA (.sort rightLevel)}
    {rightDisplayed : rightA.subst rightRaw = annotation}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : rightEnv.Ordered)
    (leftCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight
      (.bind leftGraph leftDomain annotation leftDisplayed) leftFrame)
    (right : OriginalCaptureRealization (.bind rightGraph rightDomain annotation rightDisplayed)
      env registry target rightLocals commonLeft commonRight rightAvailable)
    (rightCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight
      (.bind rightGraph rightDomain annotation rightDisplayed) right.frame.raw)
    (leftClosed : leftAvailable.AtomClosed) (rightClosed : rightAvailable.AtomClosed)
    {leftNode : EndpointState leftEnv U (leftA :: leftSource) (.bvar 0) leftAssigned}
    (rightNode : EndpointState rightEnv U (rightA :: rightSource) (.bvar 0) rightAssigned)
    (rightProvenance : EndpointProvenance (.cons rightContext rightDomain) rightNode)
    (query : RichObs leftEnv env U registry target leftNode leftLocals leftσ (profile : Profile n) footprint)
    (resources : footprint.Available leftAvailable) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps
      (freshVariableDisplay rightGraph rightDomain annotation rightDisplayed rightNode rightProvenance)
      commonLeft commonRight profile (environmentCost (right.frame.dependencyEnvironment ordered))) := by
  apply query.replayBoundedVariable henv hscoped formed
    (fun _ => .empty _ right rightCapped rightClosed (fun _ => Nat.le_refl _))
    (fun need member => boundedFreshVariable henv hscoped formed ordered right rightCapped rightClosed
      rightNode rightProvenance need (leftCapped.freshNeedBound member)) leftClosed resources

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
