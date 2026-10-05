import Lean4Lean.Theory.Typing.AnchoredOriginalConstructorSpineReply
import Lean4Lean.Theory.Typing.AnchoredOriginalSourceConstructorBinder
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalConstructorFramePositions

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private LambdaGuard.anchorRelated from Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiReindex
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 2000000

private theorem drop_at {xs : List α} {index : Nat} {value : α}
    (member : xs[index]? = some value) : xs.drop index = value :: xs.drop (index + 1) := by
  induction xs generalizing index with
  | nil => simp at member
  | cons head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at member
              subst head; rfl
    | succ index => exact ih member

private theorem lift_comp_anchor (raw common : Subst) (anchor : VExpr) :
    raw.lift.comp (common.cons anchor) = (raw.comp common).cons anchor := by
  funext index
  cases index <;> simp [Subst.comp, Subst.lift, Subst.cons]

private theorem plan_sizeOf_substCast
    (equal : σ = τ)
    (query : RichConstructorPlan env U registry target header name levels signature context σ arguments demand footprint) :
    sizeOf (equal ▸ query) = sizeOf query := by
  cases equal
  rfl

/-- Reindex the finite native plan using only actual original code calls.
The destination telescope is obtained by `originalConstructorSpine`. -/
theorem RichConstructorPlan.reindexSpine
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {leftHeader : EndpointRef leftEnv U [] declaredType (.sort leftHeaderLevel)}
    {rightHeader : EndpointRef rightEnv U [] declaredType (.sort rightHeaderLevel)}
    {signature : ConstantTelescope declaredType}
    {leftContext : ContextDerivation leftEnv U source}
    {rightContext : ContextDerivation rightEnv U source}
    {leftGraph : OriginalCaptureMap (common := common) leftContext raw}
    {rightGraph : OriginalCaptureMap (common := common) rightContext raw}
    {rightNode : EndpointState rightEnv U source (wrapForalls remaining signature.result) (.sort rightLevel)}
    (henv : env.Ordered)
    (bank : StagedOriginalLowerCallBank env U registry stage limit)
    (lower : callStage < stage)
    (leftOrdered : leftEnv.Ordered) (rightOrdered : rightEnv.Ordered)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (leftFrame : OriginalCaptureRealization leftGraph env registry target
      (List.range arguments.length) commonLeft commonRight leftAvailable)
    (leftGenerated : SourceCaptureGenerated (SourceAtStage callStage) base caps
      commonLeft commonRight leftGraph leftFrame.frame.raw)
    (leftClosed : leftAvailable.AtomClosed)
    (rightFrame : OriginalCaptureRealization rightGraph env registry target
      (List.range arguments.length) commonLeft commonRight rightAvailable)
    (rightGenerated : SourceCaptureGenerated (SourceAtStage callStage) base caps
      commonLeft commonRight rightGraph rightFrame.frame.raw)
    (rightClosed : rightAvailable.AtomClosed)
    (included : ∀ index need, need ∈ leftAvailable index → need ∈ rightAvailable index)
    (remainingEq : remaining = signature.domains.drop arguments.length)
    (spine : OriginalConstructorSpine (header := rightHeader) signature.result rightContext remaining rightNode)
    (plan : RichConstructorPlan env U registry target leftHeader name levels signature
      leftContext (raw.comp commonLeft) arguments demand footprint)
    (resources : footprint.Available leftAvailable) :
    Nonempty (ConstructorSpineReply (base := base) (caps := caps) (header := rightHeader)
      (signature := signature) (node := rightNode) (SourceAtStage callStage)
      name levels arguments rightFrame rightOrdered demand) := by
  match plan with
  | .terminal saturated shape relevant resultNode location lineage captures resultCode =>
    have empty : remaining = [] := by simpa [saturated] using remainingEq
    clear remainingEq
    subst remaining
    cases spine with
    | terminal rightLocation rightLineage =>
      let left := constructorOccurrenceDisplay location lineage leftGraph
      let right := constructorOccurrenceDisplay rightLocation rightLineage rightGraph
      obtain ⟨answer⟩ := bank.constructorTerminalReindex henv lower leftOrdered rightOrdered
        (leftDisplay := left) (rightDisplay := right) leftFrame leftGenerated leftClosed
        rightFrame rightGenerated rightClosed resultCode
        (fun i need member => resources i need (List.mem_append_right _ member))
      let terminal := RichConstructorPlanResult.terminal (name := name) (levels := levels)
        saturated shape relevant rightLocation rightLineage captures answer.certificate
        (fun i need member => answer.included i need (included i need
          (resources i need (List.mem_append_left _ member)))) answer.resources
      exact ⟨⟨_, answer.nextFrame, answer.generation, answer.closed, answer.included,
        terminal.toProfile, answer.bounded⟩⟩
  | .terminalRecord registered lookup nameEq bounded saturated shape resultNode location lineage captures resultCode origins =>
    have empty : remaining = [] := by simpa [saturated] using remainingEq
    clear remainingEq
    subst remaining
    cases spine with
    | terminal rightLocation rightLineage =>
      let left := constructorOccurrenceDisplay location lineage leftGraph
      let right := constructorOccurrenceDisplay rightLocation rightLineage rightGraph
      obtain ⟨answer⟩ := bank.constructorTerminalReindex henv lower leftOrdered rightOrdered
        (leftDisplay := left) (rightDisplay := right) leftFrame leftGenerated leftClosed
        rightFrame rightGenerated rightClosed resultCode
        (fun i need member => resources i need (List.mem_append_right _ member))
      let terminal := RichConstructorPlanResult.terminalRecord (name := name) (levels := levels)
        registered lookup nameEq bounded saturated shape rightLocation rightLineage
        captures answer.certificate origins
        (fun i need member => answer.included i need (included i need
          (resources i need (List.mem_append_left _ member)))) answer.resources
      exact ⟨⟨_, answer.nextFrame, answer.generation, answer.closed, answer.included,
        terminal.toProfile, answer.bounded⟩⟩
  | .view old change =>
    obtain ⟨answer⟩ := old.reindexSpine henv bank lower leftOrdered rightOrdered leftBelow rightBelow
      leftFrame leftGenerated leftClosed rightFrame rightGenerated rightClosed included remainingEq spine resources
    exact ⟨{ answer with result := answer.result.view change }⟩
  | .pad old =>
    obtain ⟨answer⟩ := old.reindexSpine henv bank lower leftOrdered rightOrdered leftBelow rightBelow
      leftFrame leftGenerated leftClosed rightFrame rightGenerated rightClosed included remainingEq spine resources
    exact ⟨{ answer with result := answer.result.pad }⟩
  | .binder (key := key) (bodyFootprint := bodyFootprint) origin original location lineage domainCode guard body pack covered =>
    have shape := remainingEq.trans (drop_at origin)
    clear remainingEq
    subst remaining
    cases spine with
    | binder hu hv route rightLocation rightLineage childSpine =>
      let left := constructorOccurrenceDisplay location lineage leftGraph
      let right := constructorOccurrenceDisplay rightLocation rightLineage rightGraph
      obtain ⟨domainAnswer⟩ := bank.constructorTerminalReindex henv lower leftOrdered rightOrdered
        (leftDisplay := left) (rightDisplay := right) leftFrame leftGenerated leftClosed
        rightFrame rightGenerated rightClosed domainCode
        (fun i need member => resources i need (List.mem_append_left _ member))
      have needsBound := fun need member => (pack.atomized_localNeeds need member).1
      have needsCovered := fun need member atom present =>
        covered atom ((pack.atomized_localNeeds need member).2 atom present)
      obtain ⟨leftChild, leftChildGenerated, leftEnvironment⟩ := leftFrame.bindSource
        leftGenerated original _ rfl leftBelow domainCode
        (fun i need member => resources i need (List.mem_append_left _ member)) guard.inputTyped
        (LambdaGuard.anchorRelated henv guard) (guard.path.cast guard.anchor.1)
        _ needsBound needsCovered
      obtain ⟨rightChild, rightChildGenerated, rightEnvironment⟩ := domainAnswer.nextFrame.bindSource
        domainAnswer.generation _ _ rfl rightBelow domainAnswer.certificate domainAnswer.resources
        guard.inputTyped (LambdaGuard.anchorRelated henv guard) (guard.path.cast guard.anchor.1)
        _ needsBound needsCovered
      have childIncluded : ∀ index need,
          need ∈ (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) leftAvailable) index →
          need ∈ (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) domainAnswer.nextAvailable) index := by
        intro index need member
        cases index with
        | zero => exact member
        | succ index => exact domainAnswer.included index need (included index need member)
      have bodyResources := pack.available_atomized_localNeeds
        (fun i need member => resources i need (List.mem_append_right _ member))
      let bodyQuery := (lift_comp_anchor raw commonLeft key.anchor).symm ▸ body
      have bodySize : sizeOf bodyQuery = sizeOf body :=
        plan_sizeOf_substCast (lift_comp_anchor raw commonLeft key.anchor).symm body
      have localEq : Locals.push (List.range arguments.length) = List.range (arguments ++ [key.anchor]).length := by
        simp only [List.length_append, List.length_singleton, List.range_succ_eq_map, Locals.push]
      obtain ⟨leftChild', leftChildGenerated', _leftPositions⟩ :=
        leftChild.changePositions leftChildGenerated localEq
      obtain ⟨rightChild', rightChildGenerated', rightPositions⟩ :=
        rightChild.changePositions rightChildGenerated localEq
      obtain ⟨childAnswer⟩ := bodyQuery.reindexSpine henv bank lower leftOrdered rightOrdered
        leftBelow rightBelow leftChild' leftChildGenerated'
        (Valuation.push_atomized_closed leftClosed _) rightChild' rightChildGenerated'
        (Valuation.push_atomized_closed domainAnswer.closed _) childIncluded
        (by simp only [List.length_append, List.length_singleton]) childSpine bodyResources
      have domainResources := fun index need member => childAnswer.included (index+1) need
        (domainAnswer.resources index need member)
      have childResult := childAnswer.result.toAtom
      simp only [lift_comp_anchor] at childResult
      obtain ⟨chosenChild, chosenGenerated, chosenPositions⟩ :=
        childAnswer.nextFrame.changePositions childAnswer.generation localEq.symm
      obtain ⟨parent, parentGenerated, ⟨closedResult⟩, domainBound⟩ := childResult.closeSelectedBinder
        hu hv origin rightLocation rightLineage chosenChild chosenGenerated
        domainAnswer.certificate domainResources guard
      refine ⟨⟨_, parent, parentGenerated, ?_, ?_, closedResult.toProfile.restoreRoute route, ?_⟩⟩
      · exact fun index need member atom present => childAnswer.closed (index+1) need member atom present
      · exact fun index need member => childAnswer.included (index+1) need (domainAnswer.included index need member)
      · have bound := childAnswer.bounded
        rw [rightPositions rightOrdered, rightEnvironment rightOrdered, generatedBinder_environmentCost] at bound
        rw [← chosenPositions rightOrdered] at bound
        have bound := Nat.le_trans (domainBound rightOrdered) bound
        exact Nat.le_trans (generatedBinder_cancel _ _ _ bound) domainAnswer.bounded
termination_by sizeOf plan

decreasing_by
  all_goals simp_wf
  all_goals first | omega | (rw [bodySize]; omega)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
