import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderSourceGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalStagedClosedHeaderReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalTemplateComparison
import Lean4Lean.Theory.Typing.AnchoredOriginalSourceTypeRouteGeneration

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace RetainedHeaderUniverse

private theorem source_trans
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {middle : OriginalNestedDisplay U common middleExpression middleAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    (firstGenerated : first.SourceGenerated P base caps)
    (secondGenerated : second.SourceGenerated P base caps) :
    (first.trans second).SourceGenerated P base caps := by
  exact sourceGenerated_trans firstGenerated secondGenerated

private theorem source_same
    (left : OriginalNestedDisplay U common leftExpression leftAssigned)
    (right : OriginalNestedDisplay U common rightExpression rightAssigned)
    (same : leftExpression = rightExpression)
    (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
    (leftBelow : left.sourceEnv ≤ env) (rightBelow : right.sourceEnv ≤ env)
    (leftSource : P left.sourceEnv) (rightSource : P right.sourceEnv)
    (generated : SourceCaptureGenerated P base caps commonLeft commonRight right.graph frame.realization.frame.raw) :
    (RawGeneratedTypeRoute.sameExpression left right same lf rf initial frame).SourceGenerated P base caps := by
  exact sourceGenerated_same left right same lf rf initial frame leftBelow rightBelow
    leftSource rightSource generated

/-- Closed R freezes the selected output back to the actual empty baseline.
Both source stages are checked before the recursive call; proof size is free
only because this call really lowers the declaration coordinate. -/
private theorem reindexClosed
    (henv : env.Ordered)
    (bank : StagedOriginalLowerCallBank env U registry stage limit)
    (lf : leftEnv.Ordered) (rf : rightEnv.Ordered)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (leftStage : lf.constantCount < stage) (rightStage : rf.constantCount < stage)
    (left : EndpointRef leftEnv U [] expression (.sort leftLevel))
    (right : EndpointRef rightEnv U [] expression (.sort rightLevel))
    (certificate : RichCert leftEnv env U registry target (.ref left) [] σ relevant profile []) :
    Nonempty (RichCert rightEnv env U registry target (.ref right) [] σ relevant profile []) := by
  let callStage := max lf.constantCount rf.constantCount
  let rightFrame := OriginalRichFrame.nil (sourceEnv := rightEnv) (env := env)
    (U := U) (registry := registry) (target := target) (locals := [])
    (σ := σ) (τ := σ) (available := fun _ => [])
  let base := rightFrame.captureBase (.nil : Ctx.SubstEq env U target σ σ [])
  let destination := OriginalNestedDisplay.identity base (.ref right) (.ofLocation .here .nil)
  let source : OriginalNestedDisplay U [] expression (.sort leftLevel) := {
    sourceEnv := leftEnv, source := [], sourceExpression := expression
    sourceType := .sort leftLevel, context := .nil, node := .ref left
    provenance := .ofLocation .here .nil, raw := .id, graph := .empty []
    expression_eq := subst_id.symm, type_eq := subst_id.symm }
  let sourceFrame : OriginalCaptureRealization source.graph env registry target [] σ σ
      (fun _ => []) := ⟨.nil, .nil⟩
  have sourceGenerated : SourceCaptureGenerated (SourceAtStage callStage) base base.initialCaps
      σ σ source.graph sourceFrame.frame.raw :=
    .empty [] σ σ leftBelow (fun _ => Nat.le_max_left _ _)
  have destinationAmbient : rightFrame.Ambient := by
    change (RawOriginalRichFrame.nil (sourceEnv := rightEnv) (env := env)).Ambient
    rw [RawOriginalRichFrame.Ambient.eq_def]
    exact ⟨rightBelow, trivial⟩
  have destinationSources : rightFrame.raw.AllSources (SourceAtStage callStage) := by
    rw [RawOriginalRichFrame.AllSources.eq_def]
    exact ⟨fun _ => Nat.le_max_right _ _, trivial⟩
  have destinationGenerated : SourceCaptureGenerated (SourceAtStage callStage) base base.initialCaps
      σ σ destination.graph base.identityRealization.frame.raw :=
    .identity destinationAmbient destinationSources
  obtain ⟨reply⟩ := bank.observation callStage base base.initialCaps source destination σ σ lf rf
    sourceFrame sourceGenerated (by intro _ _ member; cases member)
    base.identityRealization destinationGenerated (by intro _ _ member; cases member)
    (.left _ _ (Nat.max_lt.mpr ⟨leftStage, rightStage⟩)) (.code certificate)
    (by intro _ _ member; cases member)
  obtain ⟨footprint, ⟨output⟩, available⟩ := reply.answer.freezeBase.code henv certificate.formed
  have empty : footprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro entry member
    exact List.not_mem_nil (available entry.1 entry.2 member)
  subst footprint
  exact ⟨output⟩

/-- Productive universe transfer to the SAME retained declaration endpoint.
The three recursive calls are actual R/F/R calls in strictly earlier sources;
neither a normalized header query nor its semantic answer is an input. -/
theorem replay
    {U : Nat} {leftLevels rightLevels : List VLevel}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : StagedOriginalLowerCallBank env U registry stage limit)
    (leftOrigin : ConstantHeaderOrigin leftEnv name info)
    (rightOrigin : ConstantHeaderOrigin rightEnv name info)
    (leftOrdered : leftEnv.Ordered) (rightOrdered : rightEnv.Ordered)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (leftStage : SourceAtStage stage leftEnv) (rightStage : SourceAtStage stage rightEnv)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (certificate : RichCert leftOrigin.source env U registry target
      (.ref (leftOrigin.familyHeader leftWF).reference) [] σ relevant profile []) :
    Nonempty (TemplateCodeResult env U registry target
      (.ref (leftOrigin.familyHeader leftWF).reference)
      (.ref (rightOrigin.familyHeader rightWF).reference) [] σ σ (fun _ => []) relevant profile) := by
  let equality := original rightOrigin leftWF rightWF equivalent
  have leftEarlier := originalHeader_stage_lt leftOrigin leftOrdered leftStage
  have rightEarlier := originalHeader_stage_lt rightOrigin rightOrdered rightStage
  obtain ⟨atEquality⟩ := reindexClosed henv bank leftOrigin.ordered rightOrigin.ordered
    (leftOrigin.sourceBelow.trans leftBelow) (rightOrigin.sourceBelow.trans rightBelow)
    leftEarlier rightEarlier (leftOrigin.familyHeader leftWF).reference (.left equality) certificate
  let equalityFrame := OriginalRichFrame.nil (sourceEnv := rightOrigin.source) (env := env)
    (U := U) (registry := registry) (target := target) (locals := [])
    (σ := σ) (τ := σ) (available := fun _ => [])
  have ambient : equalityFrame.Ambient := by
    change (RawOriginalRichFrame.nil (sourceEnv := rightOrigin.source) (env := env)).Ambient
    rw [RawOriginalRichFrame.Ambient.eq_def]
    exact ⟨rightOrigin.sourceBelow.trans rightBelow, trivial⟩
  have sources : equalityFrame.AllSources (SourceAtStage rightOrigin.ordered.constantCount) := by
    rw [OriginalRichFrame.AllSources, RawOriginalRichFrame.AllSources.eq_def]
    exact ⟨fun _ => Nat.le_refl _, trivial⟩
  obtain ⟨changed⟩ := bank.equality rightOrigin.ordered.constantCount rightOrigin.ordered
    (rightOrigin.sourceBelow.trans rightBelow) .nil equality true target [] σ (fun _ => [])
    equalityFrame ambient sources (.left _ _ rightEarlier)
    (by intro _ _ member; cases member) formed .nil (.code atEquality)
    (by intro _ _ member; cases member)
  obtain ⟨footprint, ⟨rightCertificate⟩, resources⟩ := changed.rightQuery.code henv certificate.formed
  have empty : footprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro entry member
    exact List.not_mem_nil (resources entry.1 entry.2 member)
  subst footprint
  obtain ⟨output⟩ := reindexClosed henv bank rightOrigin.ordered rightOrigin.ordered
    (rightOrigin.sourceBelow.trans rightBelow) (rightOrigin.sourceBelow.trans rightBelow)
    rightEarlier rightEarlier (.right equality) (rightOrigin.familyHeader rightWF).reference rightCertificate
  have raw := (equality.forget.defeq.mono (rightOrigin.sourceBelow.trans rightBelow)).substDF
    henv (by trivial) formed (show Ctx.SubstEq env U target σ σ [] from .nil)
  exact ⟨{
    footprint := [], certificate := output
    resources := by intro _ _ member; cases member
    related := changed.related.code_of_sortable henv hscoped formed certificate.formed
    path := .single (by simpa only [subst_sort] using raw) }⟩

end RetainedHeaderUniverse
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
