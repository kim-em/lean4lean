import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedResourceCaps

/-! Query-selected output frames retain the pre-answer recursion capacity.
Unary query actions retain the same frame; finite union merges actual frames
with maximum cost, so it preserves the capacity without recursive replay. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

noncomputable def RichGradedResult.adaptRequest
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (answer : RichGradedResult sourceEnv env U registry target node locals σ available (rawInput : Profile k))
    (queryBound : n ≤ k)
    (adapter : GeneralNormalProfileAdapter env U registry target rawInput (raiseProfile k queryBound (input : Profile n))) :
    RichGradedResult sourceEnv env U registry target node locals σ available input := {
  rank := answer.rank, bound := Nat.le_trans queryBound answer.bound
  raw := answer.raw, footprint := answer.footprint, observation := answer.observation
  adapter := by
    have mapped := GeneralNormalProfileAdapter.raise henv hscoped formed answer.bound adapter
    have combined := GeneralProfileAdapter.comp answer.adapter mapped
    simpa only [raiseProfile_trans] using combined
  resources := answer.resources, live := answer.live }

structure BoundedGeneratedQueryReply
    (base : OriginalCaptureBase env U registry target)
    (commonCaps : CaptureCaps)
    (display : OriginalNestedDisplay U common expression assigned)
    (commonLeft commonRight : Subst) (requested : Profile n) (capacity : Nat) where
  answer : CappedGeneratedQueryReply base commonCaps display commonLeft commonRight requested
  bounded : ∀ ordered : display.sourceEnv.Ordered,
    environmentCost (answer.reply.realization.frame.dependencyEnvironment ordered) ≤ capacity

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {base : OriginalCaptureBase env U registry target}
  {display : OriginalNestedDisplay U common expression assigned}

def BoundedGeneratedQueryReply.mapQuery
    (reply : BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight requested capacity)
    (query : RichGradedResult display.sourceEnv env U registry target display.node reply.answer.reply.locals
      (display.raw.comp commonLeft) reply.answer.reply.available next) :
    BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight next capacity :=
  ⟨⟨{ reply.answer.reply with query := query }, reply.answer.capped⟩, reply.bounded⟩

def BoundedGeneratedQueryReply.empty
    {base : OriginalCaptureBase env U registry target}
    (display : OriginalNestedDisplay U common expression assigned)
    (frame : OriginalCaptureRealization display.graph env registry target locals commonLeft commonRight available)
    (capped : CappedCaptureGenerated base commonCaps commonLeft commonRight display.graph frame.frame.raw)
    (closed : available.AtomClosed)
    (bounded : ∀ ordered : display.sourceEnv.Ordered,
      environmentCost (frame.frame.dependencyEnvironment ordered) ≤ capacity) :
    BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight (.empty : Profile n) capacity :=
  ⟨⟨⟨locals, available, frame, capped.generated, .empty, closed⟩, capped⟩, bounded⟩

noncomputable def BoundedGeneratedQueryReply.union
    {p q : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (left : BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight p capacity)
    (right : BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight q capacity) :
    BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight (p.union q) capacity :=
  ⟨left.answer.union henv hscoped formed right.answer, fun ordered =>
    (left.answer.reply.merge henv hscoped formed right.answer.reply).environment_le
      ordered (left.bounded ordered) (right.bounded ordered)⟩

noncomputable def BoundedGeneratedQueryReply.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {requested : Profile n}
    (reply : BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight requested capacity) :
    BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight requested.pad capacity :=
  reply.mapQuery (reply.answer.reply.query.pad henv hscoped formed)

def BoundedGeneratedQueryReply.unpad
    {requested : Profile n}
    (reply : BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight requested.pad capacity) :
    BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight requested capacity :=
  reply.mapQuery reply.answer.reply.query.unpad

noncomputable def BoundedGeneratedQueryReply.codeAdapter
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {profile : Profile n} {output : Profile m}
    (reply : BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight profile capacity)
    (action : SortableCodeAction env U registry target relevant profile next output)
    (sorted : profile.HasType (.sort relevant)) :
    BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight output capacity :=
  reply.mapQuery (reply.answer.reply.query.codeAdapter henv hscoped formed action sorted)

theorem BoundedGeneratedQueryReply.action
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {a b : Atom n}
    (reply : BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight (.singleton a) capacity)
    (action : AtomAction env U registry target a b) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight (.singleton b) capacity) := by
  obtain ⟨query⟩ := reply.answer.reply.query.action henv hscoped formed action
  exact ⟨reply.mapQuery query⟩

noncomputable def BoundedGeneratedQueryReply.restrict
    {p q : Profile n}
    (reply : BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight p capacity)
    (included : ∀ atom ∈ q.atoms, atom ∈ p.atoms) :
    BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight q capacity :=
  reply.mapQuery (reply.answer.reply.query.restrict included)

noncomputable def BoundedGeneratedQueryReply.localDemand
    {input : Profile n}
    (reply : BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight input capacity)
    (need : Need) (bounded : need.rank ≤ n)
    (covered : ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight need.profile capacity :=
  reply.mapQuery (reply.answer.reply.query.localDemand need bounded covered)

theorem BoundedGeneratedQueryReply.ofFrame
    (display : OriginalNestedDisplay U common expression assigned)
    (frame : OriginalRichFrame display.sourceEnv env U registry target display.context locals σ τ available)
    (capped : CappedCaptureGenerated base commonCaps commonLeft commonRight display.graph frame.raw)
    (substitutions : Ctx.SubstEq env U target σ τ display.source)
    (closed : available.AtomClosed)
    (query : RichGradedResult display.sourceEnv env U registry target display.node locals σ available requested)
    (bounded : ∀ ordered : display.sourceEnv.Ordered,
      environmentCost (frame.dependencyEnvironment ordered) ≤ capacity) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight requested capacity) := by
  obtain ⟨left, right⟩ := capped.generated.realizations
  subst σ
  subst τ
  exact ⟨⟨⟨⟨locals, available, ⟨frame, substitutions⟩, capped.generated, query, closed⟩, capped⟩, bounded⟩⟩

theorem BoundedGeneratedQueryReply.unweaken
    {commonCaps nextCaps : CaptureCaps}
    {ρ : Lift} (insertion : Ctx.Lift' ρ common next)
    (leftTail : Subst.lift_l ρ nextLeft = commonLeft)
    (rightTail : Subst.lift_l ρ nextRight = commonRight)
    (capsTail : (fun index => nextCaps (ρ.liftVar index)) = commonCaps)
    (reply : BoundedGeneratedQueryReply base nextCaps (display.weaken insertion)
      nextLeft nextRight requested capacity) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight requested capacity) := by
  have capped := reply.answer.capped.unweaken
  rw [leftTail, rightTail, capsTail] at capped
  exact BoundedGeneratedQueryReply.ofFrame display reply.answer.reply.realization.frame capped
    reply.answer.reply.realization.substitutions reply.answer.reply.closed reply.answer.reply.query reply.bounded

/-- Semantics and a raw path accompany the same bounded source answer.
The path is independent of whether the requested code profile is empty. -/
structure BoundedParameterReply
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    (start : VExpr) (display : OriginalNestedDisplay U common expression assigned)
    (commonLeft commonRight : Subst) (profile : Profile n) (capacity : Nat) where
  reply : BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight profile capacity
  related : TypeRelated env U registry target start (expression.subst commonLeft) profile
  path : TypeConversion env U target start (expression.subst commonLeft)

/-- Source R may discover a different prior frame. Literal source-display
agreement preserves both semantic channels at the exact requested profile. -/
def BoundedParameterReply.reindex
    {left : OriginalNestedDisplay U common expression leftType}
    {right : OriginalNestedDisplay U common expression rightType}
    (answer : BoundedParameterReply base commonCaps start left commonLeft commonRight profile capacity)
    (replayed : BoundedGeneratedQueryReply base commonCaps right commonLeft commonRight profile nextCapacity) :
    BoundedParameterReply base commonCaps start right commonLeft commonRight profile nextCapacity :=
  ⟨replayed, answer.related, answer.path⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
