import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientCaptureGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalBoundedGeneratedReply
import Lean4Lean.Theory.Typing.AnchoredOriginalTypeRouteSyntax

/-! Actual query-reply construction preserves positive hereditary
generation, including the route histories hidden behind captured slots. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

/-- Both directions retain the endpoints of the SAME original equality.
Reversal does not manufacture a new symmetry derivation or change its cost. -/
structure OriginalDirectionalEqualityResult
    (original : Derivation sourceEnv U source A B assigned) (forward : Bool)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ τ : Subst) (available : Valuation) (profile : Profile n) where
  support : Profile n
  related : Related env U registry target
    ((if forward then A else B).subst σ) ((if !forward then A else B).subst τ)
    (assigned.subst σ) profile support
  rightQuery : RichGradedResult sourceEnv env U registry target
    (.ref (originalTypeRouteSide original (!forward))) locals τ available profile

/-- The actual chosen query frame retains hereditary generation, including
its scoped owners and dormant histories. -/
structure AmbientBoundedGeneratedQueryReply
    (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    (display : OriginalNestedDisplay U common expression assigned)
    (left right : Subst) (profile : Profile n) (capacity : Nat)
    extends BoundedGeneratedQueryReply base caps display left right profile capacity where
  generation : AmbientCaptureGenerated base caps left right display.graph
    toBoundedGeneratedQueryReply.answer.reply.realization.frame.raw

/-- Assigned comparison returns semantics and the SAME hereditarily generated
selected frame, including for an empty requested profile. -/
structure AmbientBoundedParameterReply
    (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    (start : VExpr) (display : OriginalNestedDisplay U common expression assigned)
    (left right : Subst) (profile : Profile n) (capacity : Nat)
    extends BoundedParameterReply base caps start display left right profile capacity where
  generation : AmbientCaptureGenerated base caps left right display.graph
    toBoundedParameterReply.reply.answer.reply.realization.frame.raw

theorem AmbientBoundedGeneratedQueryReply.ambient
    (reply : AmbientBoundedGeneratedQueryReply base caps display left right profile capacity) :
    reply.answer.reply.realization.frame.Ambient := reply.generation.ambient.2

theorem AmbientBoundedParameterReply.ambient
    (reply : AmbientBoundedParameterReply base caps start display left right profile capacity) :
    reply.reply.answer.reply.realization.frame.Ambient := reply.generation.ambient.2

theorem GeneratedQueryReply.merge_ambientGenerated
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {p q : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (left : GeneratedQueryReply base display commonLeft commonRight p)
    (right : GeneratedQueryReply base display commonLeft commonRight q)
    (leftGenerated : AmbientCaptureGenerated base caps commonLeft commonRight display.graph left.realization.frame.raw)
    (rightGenerated : AmbientCaptureGenerated base caps commonLeft commonRight display.graph right.realization.frame.raw) :
    AmbientCaptureGenerated base caps commonLeft commonRight display.graph
      (left.merge henv hscoped formed right).reply.realization.frame.raw := by
  rcases left with ⟨leftLocals, leftAvailable, leftFrame, leftGenerated', leftQuery, leftClosed⟩
  rcases right with ⟨rightLocals, rightAvailable, rightFrame, rightGenerated', rightQuery, rightClosed⟩
  have localsEq : leftLocals = rightLocals :=
    leftGenerated'.locals_eq.trans rightGenerated'.locals_eq.symm
  cases localsEq
  exact .merge leftGenerated rightGenerated

def AmbientBoundedGeneratedQueryReply.empty
    {base : OriginalCaptureBase env U registry target}
    (display : OriginalNestedDisplay U common expression assigned)
    (frame : OriginalCaptureRealization display.graph env registry target locals commonLeft commonRight available)
    (generated : AmbientCaptureGenerated base caps commonLeft commonRight display.graph frame.frame.raw)
    (closed : available.AtomClosed)
    (bounded : ∀ ordered : display.sourceEnv.Ordered,
      environmentCost (frame.frame.dependencyEnvironment ordered) ≤ capacity) :
    AmbientBoundedGeneratedQueryReply base caps display commonLeft commonRight (.empty : Profile n) capacity :=
  ⟨.empty display frame generated.capped closed bounded, generated⟩

def AmbientBoundedGeneratedQueryReply.mapQuery
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    (reply : AmbientBoundedGeneratedQueryReply base caps display commonLeft commonRight requested capacity)
    (query : RichGradedResult display.sourceEnv env U registry target display.node reply.answer.reply.locals
      (display.raw.comp commonLeft) reply.answer.reply.available next) :
    AmbientBoundedGeneratedQueryReply base caps display commonLeft commonRight next capacity :=
  ⟨reply.toBoundedGeneratedQueryReply.mapQuery query, reply.generation⟩

noncomputable def AmbientBoundedGeneratedQueryReply.union
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {p q : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (left : AmbientBoundedGeneratedQueryReply base caps display commonLeft commonRight p capacity)
    (right : AmbientBoundedGeneratedQueryReply base caps display commonLeft commonRight q capacity) :
    AmbientBoundedGeneratedQueryReply base caps display commonLeft commonRight (p.union q) capacity :=
  ⟨left.toBoundedGeneratedQueryReply.union henv hscoped formed right.toBoundedGeneratedQueryReply,
    left.answer.reply.merge_ambientGenerated henv hscoped formed right.answer.reply
      left.generation right.generation⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
