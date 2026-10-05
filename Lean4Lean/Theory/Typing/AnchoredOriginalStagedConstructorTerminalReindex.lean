import Lean4Lean.Theory.Typing.AnchoredOriginalStagedLowerCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedReplyMerge
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeAction

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 1200000

/-- A result-code reconstruction keeps the destination's existing capture
resources. Both actual frames survive; the returned code is not relabelled. -/
structure ConstructorTerminalReindex
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {display : OriginalNestedDisplay U common expression assigned}
    (P : VEnv → Prop) (left right : Subst)
    (frame : OriginalCaptureRealization display.graph env registry target locals left right available)
    (ordered : display.sourceEnv.Ordered) (relevant : Bool) (profile : Profile n) where
  nextAvailable : Valuation
  nextFrame : OriginalCaptureRealization display.graph env registry target locals left right nextAvailable
  generation : SourceCaptureGenerated P base caps left right display.graph nextFrame.frame.raw
  closed : nextAvailable.AtomClosed
  included : ∀ index need, need ∈ available index → need ∈ nextAvailable index
  footprint : Footprint
  certificate : RichCert display.sourceEnv env U registry target display.node locals
    (display.raw.comp left) relevant profile footprint
  resources : footprint.Available nextAvailable
  bounded : environmentCost (nextFrame.frame.dependencyEnvironment ordered) ≤
    environmentCost (frame.frame.dependencyEnvironment ordered)

/-- Merge the selected code frame with the original capture frame. The
maximum environment bound avoids multiplying the reserve by field count. -/
theorem SourceBoundedGeneratedQueryReply.retainConstructorCaptures
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {display : OriginalNestedDisplay U common expression assigned}
    (henv : env.Ordered) (ordered : display.sourceEnv.Ordered)
    (frame : OriginalCaptureRealization display.graph env registry target locals left right available)
    (generated : SourceCaptureGenerated P base caps left right display.graph frame.frame.raw)
    (closed : available.AtomClosed)
    (reply : SourceBoundedGeneratedQueryReply P base caps display left right profile
      (environmentCost (frame.frame.dependencyEnvironment ordered)))
    (formed : profile.HasType (.sort relevant)) :
    Nonempty (ConstructorTerminalReindex (base := base) (caps := caps) P left right frame ordered relevant profile) := by
  rcases reply with ⟨⟨⟨⟨chosenLocals, chosenAvailable, chosenFrame, chosenGenerated,
    chosenQuery, chosenClosed⟩, chosenCapped⟩, bound⟩, chosenSources⟩
  have sameLocals : locals = chosenLocals :=
    generated.capped.generated.locals_eq.trans chosenGenerated.locals_eq.symm
  cases sameLocals
  obtain ⟨footprint, ⟨certificate⟩, resources⟩ := chosenQuery.code henv formed
  let combined := frame.frame.merge chosenFrame.frame
  have oldIncluded : ∀ index need, need ∈ available index →
      need ∈ (available.append chosenAvailable) index :=
    fun _ _ member => List.mem_append_left _ member
  have newIncluded : ∀ index need, need ∈ chosenAvailable index →
      need ∈ (available.append chosenAvailable) index :=
    fun _ _ member => List.mem_append_right _ member
  refine ⟨⟨available.append chosenAvailable,
    ⟨combined, frame.substitutions⟩, .merge generated chosenSources, ?_,
    oldIncluded, footprint, certificate,
    (fun index need member => newIncluded index need (resources index need member)), ?_⟩⟩
  · intro index need member atom present
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append_left _ (closed index need member atom present)
    · exact List.mem_append_right _ (chosenClosed index need member atom present)
  · change environmentCost ((frame.frame.merge chosenFrame.frame).dependencyEnvironment ordered) ≤ _
    rw [frame.frame.merge_environmentCost]
    exact Nat.max_le.mpr ⟨Nat.le_refl _, bound ordered⟩

/-- Actual earlier-header result comparison followed by capture-preserving
reconstruction. Registration descriptors and frozen requests may be copied
unchanged: only the result certificate changes original provenance. -/
theorem StagedOriginalLowerCallBank.constructorTerminalReindex
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {leftDisplay : OriginalNestedDisplay U common expression leftAssigned}
    {rightDisplay : OriginalNestedDisplay U common expression rightAssigned}
    (henv : env.Ordered)
    (bank : StagedOriginalLowerCallBank env U registry stage limit)
    (lower : callStage < stage)
    (leftOrdered : leftDisplay.sourceEnv.Ordered)
    (rightOrdered : rightDisplay.sourceEnv.Ordered)
    (leftFrame : OriginalCaptureRealization leftDisplay.graph env registry target
      leftLocals commonLeft commonRight leftAvailable)
    (leftGenerated : SourceCaptureGenerated (SourceAtStage callStage) base caps
      commonLeft commonRight leftDisplay.graph leftFrame.frame.raw)
    (leftClosed : leftAvailable.AtomClosed)
    (rightFrame : OriginalCaptureRealization rightDisplay.graph env registry target
      rightLocals commonLeft commonRight rightAvailable)
    (rightGenerated : SourceCaptureGenerated (SourceAtStage callStage) base caps
      commonLeft commonRight rightDisplay.graph rightFrame.frame.raw)
    (rightClosed : rightAvailable.AtomClosed)
    (certificate : RichCert leftDisplay.sourceEnv env U registry target leftDisplay.node
      leftLocals (leftDisplay.raw.comp commonLeft) relevant profile footprint)
    (resources : footprint.Available leftAvailable) :
    Nonempty (ConstructorTerminalReindex (base := base) (caps := caps)
      (SourceAtStage callStage) commonLeft commonRight rightFrame rightOrdered relevant profile) := by
  obtain ⟨reply⟩ := bank.observation callStage base caps leftDisplay rightDisplay
    commonLeft commonRight leftOrdered rightOrdered leftFrame leftGenerated leftClosed
    rightFrame rightGenerated rightClosed (Prod.Lex.left _ _ lower)
    (.code certificate) resources
  exact reply.retainConstructorCaptures henv rightOrdered rightFrame rightGenerated
    rightClosed certificate.formed

/-- In particular any already constructed demand-order capture list survives
result-code reindexing, including repeated field positions and the empty list. -/
theorem ConstructorTerminalReindex.captureResources
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {display : OriginalNestedDisplay U common expression assigned}
    {frame : OriginalCaptureRealization display.graph env registry target locals left right available}
    {ordered : display.sourceEnv.Ordered}
    (answer : ConstructorTerminalReindex (base := base) (caps := caps)
      P left right frame ordered relevant profile)
    {captureFootprint : Footprint}
    (captureResources : captureFootprint.Available available) :
    captureFootprint.Available answer.nextAvailable :=
  fun index need member => answer.included index need (captureResources index need member)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
