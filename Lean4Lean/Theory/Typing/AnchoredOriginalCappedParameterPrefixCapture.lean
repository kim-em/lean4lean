import Lean4Lean.Theory.Typing.AnchoredOriginalFirstParameterCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedResourceCaps

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Forget only the completed alignment. The independent activation seed
keeps the actual whole original query and its actual semantic source frame. -/
def RichGroupedCaptureEntry.pending
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (closed : entry.ownerAvailable.AtomClosed) :
    PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue where
  owner := entry.owner
  ownerLocals := entry.ownerLocals
  ownerLeft := entry.ownerLeft
  ownerRight := entry.ownerRight
  ownerAvailable := entry.ownerAvailable
  ownerClosed := closed
  initialContext := entry.initialContext
  frame := entry.frame
  substitutions := entry.substitutions
  frame_environment_le := entry.frame_environment_le
  depth := entry.depth
  sourcePrefix := entry.sourcePrefix
  source_eq := entry.source_eq
  depth_eq := entry.depth_eq
  expression_eq := entry.expression_eq
  left_eq := entry.left_eq
  right_eq := entry.right_eq
  rank := entry.queryRank
  input := entry.queryInput
  footprint := entry.footprint
  query := entry.query
  queryAvailable := entry.queryAvailable

/-- A real first slot in any one of the retained declaration contexts.
Its nominal owner and full generated owner-frame provenance are retained. -/
def CappedFirstParameterSlot
    {sourceEnv : VEnv} {headerEnv : VEnv} {U : Nat}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (domain : EndpointRef headerEnv U [] A (.sort level))
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target context ownerLocals σ τ available)
    (nominal : EndpointState sourceEnv U source argument assigned)
    (provenance : EndpointProvenance context nominal)
    (ordered : sourceEnv.Ordered) (commonLeft commonRight : Subst) (ownerInitial : List Closure) (rawCapture : VExpr) (input : Profile n) : Prop :=
  ∃ entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      [] commonLeft (fun _ => []) ownerInitial rawCapture (rawCapture.subst σ) (rawCapture.subst τ),
    (⟨entry.rank, entry.input⟩ : Need) = ⟨n, input⟩ ∧
    Nonempty (OriginalFrameExtension ownerFrame.raw entry.frame.raw) ∧
    CappedCaptureGenerated base commonCaps commonLeft commonRight
      (.capture (.empty common) domain graph nominal provenance)
      ((OriginalRichFrame.nil (σ := commonLeft) (τ := commonRight) (locals := []) (available := fun _ => [])).group
        domain ordered ownerInitial [entry]).raw


theorem CappedFirstParameterSlot.realign
    {sourceEnv oldEnv headerEnv : VEnv} {U : Nat}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {oldDomain : EndpointRef oldEnv U [] oldA (.sort oldLevel)}
    (domain : EndpointRef headerEnv U [] A (.sort level))
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target context ownerLocals σ τ available)
    (ownerGenerated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph ownerFrame.raw)
    (nominal : EndpointState sourceEnv U source argument assigned)
    (provenance : EndpointProvenance context nominal)
    (displayed : rawCapture.subst raw = argument.subst raw)
    (henv : env.Ordered) (ordered : sourceEnv.Ordered)
    (entry : RichGroupedCaptureEntry (field := field) (major := major) oldDomain env registry target
      [] commonLeft (fun _ => []) ownerInitial rawCapture (rawCapture.subst σ) (rawCapture.subst τ))
    (ownerClosed : entry.ownerAvailable.AtomClosed)
    (extension : OriginalFrameExtension ownerFrame.raw entry.frame.raw)
    (input : (⟨entry.rank, entry.input⟩ : Need) = ⟨n, demand⟩)
    (transfer : RichCodeTransfer env U registry target (.ref oldDomain) (.ref domain)
      [] [] commonLeft commonLeft (fun _ => []) (fun _ => []))
    (path : TypeConversion env U target (oldA.subst commonLeft) (A.subst commonLeft)) :
    CappedFirstParameterSlot (base := base) (commonCaps := commonCaps) (field := field) (major := major) domain graph ownerFrame nominal provenance
      ordered commonLeft commonRight ownerInitial rawCapture (demand : Profile n) := by
  let changed := entry.realign henv transfer path
  refine ⟨changed, input, ⟨extension⟩, ?_⟩
  apply CappedCaptureGenerated.group (CappedCaptureGenerated.empty common commonLeft commonRight)
    domain ownerGenerated graph nominal provenance displayed ordered ownerInitial
    (changed.pending ownerClosed) extension [changed]
  intro selected member
  cases List.mem_singleton.mp member
  exact ⟨extension⟩

/-- The next family/common and constructor/common contexts are generated
from the same original owner frame. The bridge context is produced only
when the actual retained universe comparison is used. -/
theorem FirstParameterPrefixTransfers.captureGroupsCapped
    {packet : OriginalProjectionParameters sourceEnv U name info seedLevels}
    {requestedWF : ∀ level ∈ requestedLevels, level.WF U}
    {seedWF : ∀ level ∈ seedLevels, level.WF U}
    {equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels}
    {cells : FirstProjectionParameterCells packet requestedWF seedWF equivalent}
    {familyHead : NormalizedFamilyPrefix packet}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target context ownerLocals σ τ available)
    (ownerGenerated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph ownerFrame.raw)
    (nominal : EndpointState sourceEnv U source argument assigned)
    (provenance : EndpointProvenance context nominal)
    (displayed : rawCapture.subst raw = argument.subst raw)
    (henv : env.Ordered) (ordered : sourceEnv.Ordered)
    (entry : RichGroupedCaptureEntry (field := field) (major := major) familyHead.domainOriginal env registry target
      [] commonLeft (fun _ => []) ownerInitial rawCapture (rawCapture.subst σ) (rawCapture.subst τ))
    (ownerClosed : entry.ownerAvailable.AtomClosed)
    (extension : OriginalFrameExtension ownerFrame.raw entry.frame.raw)
    (input : (⟨entry.rank, entry.input⟩ : Need) = ⟨n, demand⟩)
    (transfers : FirstParameterPrefixTransfers cells familyHead env registry target commonLeft) :
    CappedFirstParameterSlot (base := base) (commonCaps := commonCaps) (field := field) (major := major) (.left cells.familyCell.original)
      graph ownerFrame nominal provenance ordered commonLeft commonRight ownerInitial rawCapture (demand : Profile n) ∧
    CappedFirstParameterSlot (base := base) (commonCaps := commonCaps) (field := field) (major := major) (.left cells.constructorCell.original)
      graph ownerFrame nominal provenance ordered commonLeft commonRight ownerInitial rawCapture demand ∧
    (seedLevels = requestedLevels ∨
      CappedFirstParameterSlot (base := base) (commonCaps := commonCaps) (field := field) (major := major) (.left cells.universeCell.original)
        graph ownerFrame nominal provenance ordered commonLeft commonRight ownerInitial rawCapture demand) := by
  refine ⟨CappedFirstParameterSlot.realign _ graph ownerFrame ownerGenerated nominal provenance displayed
    henv ordered entry ownerClosed extension input transfers.seed transfers.seedPath,
    CappedFirstParameterSlot.realign _ graph ownerFrame ownerGenerated nominal provenance displayed
      henv ordered entry ownerClosed extension input transfers.requested transfers.requestedPath, ?_⟩
  rcases transfers.bridge with same | bridge
  · exact Or.inl same
  · exact Or.inr (CappedFirstParameterSlot.realign _ graph ownerFrame ownerGenerated nominal provenance displayed
      henv ordered entry ownerClosed extension input bridge transfers.seedPath)


/-- The separate original prefixes required by subsequent parameter
comparisons. An unused reflexive universe trace is deliberately absent. -/
def CappedFirstParameterPrefixes
    {packet : OriginalProjectionParameters sourceEnv U name info seedLevels}
    {requestedWF : ∀ level ∈ requestedLevels, level.WF U}
    {seedWF : ∀ level ∈ seedLevels, level.WF U}
    {equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels}
    (cells : FirstProjectionParameterCells packet requestedWF seedWF equivalent)
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target context ownerLocals σ τ available)
    (nominal : EndpointState sourceEnv U source argument assigned)
    (provenance : EndpointProvenance context nominal)
    (ordered : sourceEnv.Ordered) (commonLeft commonRight : Subst)
    (ownerInitial : List Closure) (rawCapture : VExpr) (input : Profile n) : Prop :=
    CappedFirstParameterSlot (base := base) (commonCaps := commonCaps) (field := field) (major := major) (.left cells.familyCell.original)
      graph ownerFrame nominal provenance ordered commonLeft commonRight ownerInitial rawCapture input ∧
    CappedFirstParameterSlot (base := base) (commonCaps := commonCaps) (field := field) (major := major) (.left cells.constructorCell.original)
      graph ownerFrame nominal provenance ordered commonLeft commonRight ownerInitial rawCapture input ∧
    (seedLevels = requestedLevels ∨
      CappedFirstParameterSlot (base := base) (commonCaps := commonCaps) (field := field) (major := major) (.left cells.universeCell.original)
        graph ownerFrame nominal provenance ordered commonLeft commonRight ownerInitial rawCapture input)


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
