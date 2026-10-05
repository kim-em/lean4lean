import Lean4Lean.Theory.Typing.AnchoredOriginalCapturedQueryData
import Lean4Lean.Theory.Typing.AnchoredOriginalCapturedHeadQuery
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedBaseFreeze

/-! The finite argument-call ledger is selected from the actual captured
body footprint. Each returned observation is frozen at the original whole
source frame; no prechosen argument supply is an input. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem CappedCaptureGenerated.argumentQueries
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation headerEnv U headerSource}
    {graph : OriginalCaptureMap (common := common) context raw}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {ownerContext : ContextDerivation ownerEnv U ownerSource}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    {owner : EndpointState ownerEnv U ownerSource argument assigned}
    {provenance : EndpointProvenance ownerContext owner}
    {frame : RawOriginalRichFrame headerEnv env U registry target (.cons context domain) locals σ τ available}
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight
      (.capture graph domain ownerGraph owner provenance) frame)
    (valid : frame.Valid) (substitutions : Ctx.SubstEq env U target σ τ (A :: headerSource))
    (ordered : headerEnv.Ordered) (needs : List Need)
    (resources : ∀ need ∈ needs, need ∈ available 0)
    (budget : environmentCost (frame.dependencyEnvironment ordered) ≤ capacity) :
    Nonempty (CapturedArgumentQueries base commonCaps common commonLeft commonRight
      (argument.subst ownerRaw) capacity needs) := by
  induction needs with
  | nil => exact ⟨.nil⟩
  | cons need needs ih =>
    obtain ⟨head⟩ := generated.headQuery valid substitutions ordered need (resources need List.mem_cons_self)
    obtain ⟨tail⟩ := ih (fun need member => resources need (List.mem_cons_of_mem _ member))
    exact ⟨.cons (head.enlarge budget) tail⟩

def CapturedArgumentQueries.Calls
    {base : OriginalCaptureBase env U registry target}
    (queries : CapturedArgumentQueries base commonCaps common commonLeft commonRight expression capacity needs)
    (destination : OriginalNestedDisplay U common expression assigned)
    (ordered : destination.sourceEnv.Ordered) (limit : Nat) : Prop :=
  match queries with
  | .nil => True
  | .cons head tail =>
      GeneratedObservationCall base head.caps head.display (destination.weaken head.insertion)
        head.left head.right head.ordered ordered limit ∧ tail.Calls destination ordered limit

/-- The recursive clauses refer only to the fixed finite original occurrences
selected above. Every answer is returned to the original identity frame by
its hereditary cap; it cannot add unavailable original variables. -/
theorem CapturedArgumentQueries.supplyAtBase
    {base : OriginalCaptureBase env U registry target}
    {node : EndpointState base.sourceEnv U base.source expression assigned}
    (provenance : EndpointProvenance base.context node)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : base.sourceEnv.Ordered) (closed : base.available.AtomClosed)
    (queries : CapturedArgumentQueries base base.initialCaps base.source base.left base.right expression capacity needs)
    (scheduled : needs ≠ [] → richSchedule .expressionReindex
      (capacity + (Closure.close (node.dependencyOrigin ordered) (base.frame.dependencyEnvironment ordered)).cost) < limit)
    (calls : queries.Calls (OriginalNestedDisplay.identity base node provenance) ordered limit) :
    Nonempty (RichArgumentSupply base.sourceEnv env U registry target node base.locals base.left base.available needs) := by
  induction queries with
  | nil => exact ⟨.nil⟩
  | cons head tail ih =>
    obtain ⟨answer⟩ := head.replay henv hscoped formed closed (OriginalNestedDisplay.identity base node provenance)
      ordered base.identityRealization base.identityCapped closed (scheduled (by simp)) calls.1
    obtain ⟨rest⟩ := ih (fun _ => scheduled (by simp)) calls.2
    exact ⟨.cons answer.answer.freezeBase rest⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
