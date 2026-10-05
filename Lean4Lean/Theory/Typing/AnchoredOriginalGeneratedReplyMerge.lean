import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedFrameLocals
import Lean4Lean.Theory.Typing.AnchoredOriginalRichOutputReplay

/-! Independent generated replies merge their actual frames and finite
resources. No recursive replay is performed at an enlarged environment;
the merged environment costs exactly the maximum of the two inputs. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Source syntax does not depend on the resource table. A finite inclusion
changes only the proof that its retained footprint is available. -/
def RichGradedResult.availableMono
    (query : RichGradedResult sourceEnv env U registry target node locals σ available requested)
    (included : ∀ index need, need ∈ available index → need ∈ next index) :
    RichGradedResult sourceEnv env U registry target node locals σ next requested :=
  { query with resources := fun index need member => included index need (query.resources index need member) }

structure GeneratedReplyMerge
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {p q : Profile n}
    (left : GeneratedQueryReply base display commonLeft commonRight p)
    (right : GeneratedQueryReply base display commonLeft commonRight q) where
  reply : GeneratedQueryReply base display commonLeft commonRight (p.union q)
  leftAvailable : ∀ index need, need ∈ left.available index → need ∈ reply.available index
  rightAvailable : ∀ index need, need ∈ right.available index → need ∈ reply.available index
  environment : ∀ ordered : display.sourceEnv.Ordered,
    environmentCost (reply.realization.frame.dependencyEnvironment ordered) =
      max (environmentCost (left.realization.frame.dependencyEnvironment ordered))
        (environmentCost (right.realization.frame.dependencyEnvironment ordered))

/-- Both heterogeneous owner ledgers remain intact. Fresh original binders
remain intact too; lookup in the resulting frame selects the branch whose
finite resource table supplied the requested need. -/
noncomputable def GeneratedQueryReply.merge
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {p q : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (left : GeneratedQueryReply base display commonLeft commonRight p)
    (right : GeneratedQueryReply base display commonLeft commonRight q) :
    GeneratedReplyMerge left right := by
  rcases left with ⟨leftLocals, leftAvailable, leftFrame, leftGenerated, leftQuery, leftClosed⟩
  rcases right with ⟨rightLocals, rightAvailable, rightFrame, rightGenerated, rightQuery, rightClosed⟩
  have localsEq : leftLocals = rightLocals :=
    leftGenerated.locals_eq.trans rightGenerated.locals_eq.symm
  cases localsEq
  let combined := leftFrame.frame.merge rightFrame.frame
  have leftIncluded : ∀ index need, need ∈ leftAvailable index →
      need ∈ (leftAvailable.append rightAvailable) index :=
    fun _ _ member => List.mem_append_left _ member
  have rightIncluded : ∀ index need, need ∈ rightAvailable index →
      need ∈ (leftAvailable.append rightAvailable) index :=
    fun _ _ member => List.mem_append_right _ member
  refine ⟨⟨leftLocals, leftAvailable.append rightAvailable,
    ⟨combined, leftFrame.substitutions⟩, .merge leftGenerated rightGenerated,
    (leftQuery.availableMono leftIncluded).union henv hscoped formed
      (rightQuery.availableMono rightIncluded), ?_⟩,
    leftIncluded, rightIncluded, fun ordered => leftFrame.frame.merge_environmentCost ordered rightFrame.frame⟩
  intro index need member selected present
  rcases List.mem_append.mp member with member | member
  · exact List.mem_append_left _ (leftClosed index need member selected present)
  · exact List.mem_append_right _ (rightClosed index need member selected present)

noncomputable def GeneratedQueryReply.union
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {p q : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (left : GeneratedQueryReply base display commonLeft commonRight p)
    (right : GeneratedQueryReply base display commonLeft commonRight q) :
    GeneratedQueryReply base display commonLeft commonRight (p.union q) :=
  (left.merge henv hscoped formed right).reply

/-- A reserve established for both independent replies still bounds the
merged reply. In particular union does not spend a query-count reserve. -/
theorem GeneratedReplyMerge.environment_le
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {p q : Profile n}
    {left : GeneratedQueryReply base display commonLeft commonRight p}
    {right : GeneratedQueryReply base display commonLeft commonRight q}
    (merged : GeneratedReplyMerge left right) (ordered : display.sourceEnv.Ordered)
    (leftBound : environmentCost (left.realization.frame.dependencyEnvironment ordered) ≤ capacity)
    (rightBound : environmentCost (right.realization.frame.dependencyEnvironment ordered) ≤ capacity) :
    environmentCost (merged.reply.realization.frame.dependencyEnvironment ordered) ≤ capacity := by
  rw [merged.environment]
  exact Nat.max_le.mpr ⟨leftBound, rightBound⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
