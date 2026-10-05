import Lean4Lean.Theory.Typing.AnchoredOriginalBoundedGeneratedReply
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedApplicationReindex

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Independent child reconstructions keep their own finite frames. Only
resource membership is enlarged in the merged frame; neither child is
recursively replayed against newly added demands. -/
theorem boundedGeneratedApplicationReply
    {base : OriginalCaptureBase env U registry target}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {parent : EndpointState sourceEnv U source (.app f a) assigned}
    (location : Located root parent)
    (initial : ContextDerivation sourceEnv U rootSource)
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {fn : EndpointState sourceEnv U source f (.forallE A B)}
    {arg : EndpointState sourceEnv U source a A}
    {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (route : PrefixRoute sourceEnv U source (.app f a) parent (.app hu hv domain body fn arg result))
    (functionEq : displayedFunction = f.subst raw)
    (argumentEq : displayedArgument = a.subst raw)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {key : Key n} {output : Atom n} {rawInput : Profile n}
    (function : BoundedGeneratedQueryReply base commonCaps
      (applicationGeneratedFunctionSourceDisplay location initial graph route functionEq)
      commonLeft commonRight (Profile.fn key output) capacity)
    (argument : BoundedGeneratedQueryReply base commonCaps
      (applicationGeneratedArgumentSourceDisplay location initial graph route argumentEq)
      commonLeft commonRight rawInput capacity)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (a.subst (raw.comp commonLeft))
      (a.subst (raw.comp commonLeft))) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps
      (applicationGeneratedSourceDisplay location initial graph functionEq argumentEq)
      commonLeft commonRight (.singleton output) capacity) := by
  rcases function with ⟨⟨⟨functionLocals, functionAvailable, functionFrame, functionGenerated,
    functionQuery, functionClosed⟩, functionCapped⟩, functionBound⟩
  rcases argument with ⟨⟨⟨argumentLocals, argumentAvailable, argumentFrame, argumentGenerated,
    argumentQuery, argumentClosed⟩, argumentCapped⟩, argumentBound⟩
  have localsEq : functionLocals = argumentLocals :=
    functionGenerated.locals_eq.trans argumentGenerated.locals_eq.symm
  cases localsEq
  let available := functionAvailable.append argumentAvailable
  let frame := functionFrame.frame.merge argumentFrame.frame
  have firstIncluded : ∀ index need, need ∈ functionAvailable index → need ∈ available index :=
    fun _ _ member => List.mem_append_left _ member
  have secondIncluded : ∀ index need, need ∈ argumentAvailable index → need ∈ available index :=
    fun _ _ member => List.mem_append_right _ member
  have closed : available.AtomClosed := by
    intro index need member selected present
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append_left _ (functionClosed index need member selected present)
    · exact List.mem_append_right _ (argumentClosed index need member selected present)
  obtain ⟨query⟩ := RichGradedResult.app henv hscoped formed closed domain body result hu hv
    (functionQuery.availableMono firstIncluded) (argumentQuery.availableMono secondIncluded) arguments admitted
  refine ⟨⟨⟨{
    locals := functionLocals
    available := available
    realization := ⟨frame, functionFrame.substitutions⟩
    generated := .merge functionGenerated argumentGenerated
    query := {
      rank := query.rank, bound := query.bound, raw := query.raw, footprint := query.footprint
      observation := .route route query.observation
      adapter := query.adapter, resources := query.resources, live := query.live }
    closed := closed }, .merge functionCapped argumentCapped⟩, ?_⟩⟩
  intro ordered
  rw [OriginalRichFrame.merge_environmentCost]
  exact Nat.max_le.mpr ⟨functionBound ordered, argumentBound ordered⟩

/-- Output actions keep the same selected source frame and capacity. -/
theorem BoundedGeneratedQueryReply.outputPath
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {a : Atom n} {b : Atom m}
    (reply : BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight (.singleton a) capacity)
    (path : GeneralOutputPath env U registry target a b) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight (.singleton b) capacity) := by
  obtain ⟨query⟩ := reply.answer.reply.query.outputPath henv hscoped formed path
  exact ⟨reply.mapQuery query⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
