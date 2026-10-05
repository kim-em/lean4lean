import Lean4Lean.Theory.Typing.AnchoredOriginalCapturedHeadQueryAmbient
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientReply
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientResourceClosure

/-! Replay the finite, positively generated owner ledger using actual lower
original calls, then return every selected answer to the fixed source base. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
set_option Elab.async false

private def unweakenAmbient
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    (commonLeft commonRight : Subst)
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) : Prop :=
  match graph, frame with
  | .weaken (ρ := ρ) previous _, frame =>
    AmbientCaptureGenerated base (fun index => commonCaps (ρ.liftVar index))
      (Subst.lift_l ρ commonLeft) (Subst.lift_l ρ commonRight) previous frame
  | _, _ => True

private theorem unweakenAmbient_merge
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {left : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable}
    {right : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable}
    (first : unweakenAmbient base commonCaps commonLeft commonRight graph left)
    (second : unweakenAmbient base commonCaps commonLeft commonRight graph right) :
    unweakenAmbient base commonCaps commonLeft commonRight graph (.merge left right) := by
  cases graph <;> try trivial
  exact .merge first second

private theorem AmbientCaptureGenerated.unweakenInvariant
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight graph frame) :
    unweakenAmbient base commonCaps commonLeft commonRight graph frame := by
  induction generated with
  | merge _ _ first second => exact unweakenAmbient_merge first second
  | identity | empty | tail | bind | capture | reserveCapture | reserveBind | historyGroup => trivial
  | weaken generated insertion leftTail rightTail capsTail _ =>
    simpa only [unweakenAmbient, leftTail, rightTail, capsTail] using generated

theorem AmbientCaptureGenerated.unweaken
    {base : OriginalCaptureBase env U registry target} {nextCaps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {ρ : Lift} {insertion : Ctx.Lift' ρ common next}
    (generated : AmbientCaptureGenerated base nextCaps nextLeft nextRight (.weaken graph insertion) frame) :
    AmbientCaptureGenerated base (fun index => nextCaps (ρ.liftVar index))
      (Subst.lift_l ρ nextLeft) (Subst.lift_l ρ nextRight) graph frame :=
  generated.unweakenInvariant

theorem OriginalCaptureRealization.weakenAmbient
    {base : OriginalCaptureBase env U registry target}
    {commonCaps nextCaps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (previous : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight graph previous.frame.raw)
    {ρ : Lift} (insertion : Ctx.Lift' ρ common next)
    (leftTail : Subst.lift_l ρ nextLeft = commonLeft)
    (rightTail : Subst.lift_l ρ nextRight = commonRight)
    (capsTail : (fun index => nextCaps (ρ.liftVar index)) = commonCaps) :
    ∃ result : OriginalCaptureRealization (.weaken graph insertion) env registry target
        locals nextLeft nextRight available,
      AmbientCaptureGenerated base nextCaps nextLeft nextRight (.weaken graph insertion) result.frame.raw ∧
      ∀ ordered : sourceEnv.Ordered,
        result.frame.dependencyEnvironment ordered = previous.frame.dependencyEnvironment ordered :=
  (AmbientCaptureGenerated.weaken generated insertion leftTail rightTail capsTail).realize
    previous.frame previous.substitutions

theorem AmbientBoundedGeneratedQueryReply.ofFrame
    {base : OriginalCaptureBase env U registry target}
    (display : OriginalNestedDisplay U common expression assigned)
    (frame : OriginalRichFrame display.sourceEnv env U registry target display.context locals σ τ available)
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight display.graph frame.raw)
    (substitutions : Ctx.SubstEq env U target σ τ display.source)
    (closed : available.AtomClosed)
    (query : RichGradedResult display.sourceEnv env U registry target display.node locals σ available requested)
    (bounded : ∀ ordered : display.sourceEnv.Ordered,
      environmentCost (frame.dependencyEnvironment ordered) ≤ capacity) :
    Nonempty (AmbientBoundedGeneratedQueryReply base commonCaps display commonLeft commonRight requested capacity) := by
  obtain ⟨left, right⟩ := generated.capped.generated.realizations
  subst σ
  subst τ
  exact ⟨⟨⟨⟨⟨locals, available, ⟨frame, substitutions⟩, generated.capped.generated, query, closed⟩,
    generated.capped⟩, bounded⟩, generated⟩⟩

theorem AmbientBoundedGeneratedQueryReply.unweaken
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {commonCaps nextCaps : CaptureCaps}
    {ρ : Lift} (insertion : Ctx.Lift' ρ common next)
    (leftTail : Subst.lift_l ρ nextLeft = commonLeft)
    (rightTail : Subst.lift_l ρ nextRight = commonRight)
    (capsTail : (fun index => nextCaps (ρ.liftVar index)) = commonCaps)
    (reply : AmbientBoundedGeneratedQueryReply base nextCaps (display.weaken insertion)
      nextLeft nextRight requested capacity) :
    Nonempty (AmbientBoundedGeneratedQueryReply base commonCaps display commonLeft commonRight requested capacity) := by
  have generated := reply.generation.unweaken
  rw [leftTail, rightTail, capsTail] at generated
  exact AmbientBoundedGeneratedQueryReply.ofFrame display reply.answer.reply.realization.frame generated
    reply.answer.reply.realization.substitutions reply.answer.reply.closed reply.answer.reply.query reply.bounded

/-- Replay the actual selected head through the uniformly bounded original
bank. Closing its resources, entering its scope, adapting, and leaving that
scope all retain the same positively generated answer. -/
theorem AmbientCapturedHeadQuery.replay
    {assigned : VExpr} {available : Valuation} {locals : List Nat}
    {base : OriginalCaptureBase env U registry target}
    (head : AmbientCapturedHeadQuery base commonCaps common commonLeft commonRight expression need capacity)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (baseClosed : base.available.AtomClosed)
    (destination : OriginalNestedDisplay U common expression assigned)
    (ordered : destination.sourceEnv.Ordered)
    (frame : OriginalCaptureRealization destination.graph env registry target locals commonLeft commonRight available)
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight destination.graph frame.frame.raw)
    (closed : available.AtomClosed)
    (scheduled : richSchedule .expressionReindex
      (capacity + (Closure.close (destination.node.dependencyOrigin ordered) (frame.frame.dependencyEnvironment ordered)).cost) < limit)
    (bank : OriginalLowerCallBank env U registry limit) :
    Nonempty (AmbientBoundedGeneratedQueryReply base commonCaps destination commonLeft commonRight need.profile
      (environmentCost (frame.frame.dependencyEnvironment ordered))) := by
  obtain ⟨sourceAvailable, source, sourceGenerated, included, sourceClosed, sourceEnvironment⟩ :=
    head.realization.closeResourcesAmbient head.generated baseClosed
  obtain ⟨next, nextGenerated, sameEnvironment⟩ := frame.weakenAmbient generated head.insertion
    head.leftTail head.rightTail head.capsTail
  have bound : richSchedule .expressionReindex
      ((Closure.close (head.display.node.dependencyOrigin head.ordered) (source.frame.dependencyEnvironment head.ordered)).cost +
       (Closure.close (destination.node.dependencyOrigin ordered) (next.frame.dependencyEnvironment ordered)).cost) < limit := by
    rw [sourceEnvironment, sameEnvironment]
    exact Nat.lt_of_le_of_lt (by
      change 3 * (_ + _) + 2 ≤ 3 * (_ + _) + 2
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 (Nat.add_le_add_right head.cost _)) 2) scheduled
  obtain ⟨answer⟩ := bank.observation base head.caps head.display (destination.weaken head.insertion)
    head.left head.right head.ordered ordered
    source sourceGenerated sourceClosed next nextGenerated closed bound head.query
    (fun i n h => included i n (head.resources i n h))
  rw [sameEnvironment ordered] at answer
  exact (answer.mapQuery (answer.answer.reply.query.adaptRequest henv hscoped formed head.bound head.adapter)).unweaken
    head.insertion head.leftTail head.rightTail head.capsTail

/-- The finite calls are obtained from the original bank at the selected
owner witnesses. Every returned query is frozen to the actual source base;
there is no per-route or per-head semantic answer premise. -/
theorem CapturedArgumentQueries.supplyAtAmbientBase
    {base : OriginalCaptureBase env U registry target}
    {node : EndpointState base.sourceEnv U base.source expression assigned}
    (provenance : EndpointProvenance base.context node)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : base.sourceEnv.Ordered) (closed : base.available.AtomClosed)
    (baseAmbient : base.frame.Ambient)
    (queries : CapturedArgumentQueries base base.initialCaps base.source base.left base.right expression capacity needs)
    (generated : queries.AmbientGenerated)
    (scheduled : needs ≠ [] → richSchedule .expressionReindex
      (capacity + (Closure.close (node.dependencyOrigin ordered) (base.frame.dependencyEnvironment ordered)).cost) < limit)
    (bank : OriginalLowerCallBank env U registry limit) :
    Nonempty (RichArgumentSupply base.sourceEnv env U registry target node base.locals base.left base.available needs) := by
  induction queries with
  | nil => exact ⟨.nil⟩
  | cons head tail ih =>
    let selected : AmbientCapturedHeadQuery _ _ _ _ _ _ _ _ := ⟨head, generated.1⟩
    obtain ⟨answer⟩ := selected.replay henv hscoped formed closed (OriginalNestedDisplay.identity base node provenance)
      ordered base.identityRealization (.identity baseAmbient) closed (scheduled (by simp)) bank
    obtain ⟨rest⟩ := ih generated.2 (fun _ => scheduled (by simp))
    exact ⟨.cons answer.answer.freezeBase rest⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
