import Lean4Lean.Theory.Typing.AnchoredOriginalFirstParameterCalls
import Lean4Lean.Theory.Typing.AnchoredOriginalParameterCells

/-! Retain the intermediate original common-parameter answers. They build
the actual contexts required by the next declaration cell; a constructor
capture alone does not supply those original contexts. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

structure FirstParameterPrefixTransfers
    {packet : OriginalProjectionParameters sourceEnv U name info seedLevels}
    {requestedWF : ∀ level ∈ requestedLevels, level.WF U}
    {seedWF : ∀ level ∈ seedLevels, level.WF U}
    {equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels}
    (cells : FirstProjectionParameterCells packet requestedWF seedWF equivalent)
    (familyHead : NormalizedFamilyPrefix packet)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr) (σ : Subst) : Prop where
  seed : RichCodeTransfer env U registry target (.ref familyHead.domainOriginal) (.ref (.left cells.familyCell.original))
    [] [] σ σ (fun _ => []) (fun _ => [])
  seedPath : TypeConversion env U target (familyHead.domainExpression.subst σ) ((cells.common.instL seedLevels).subst σ)
  requested : RichCodeTransfer env U registry target (.ref familyHead.domainOriginal) (.ref (.left cells.constructorCell.original))
    [] [] σ σ (fun _ => []) (fun _ => [])
  requestedPath : TypeConversion env U target (familyHead.domainExpression.subst σ) ((cells.common.instL requestedLevels).subst σ)
  bridge : seedLevels = requestedLevels ∨
    (RichCodeTransfer env U registry target (.ref familyHead.domainOriginal) (.ref (.left cells.universeCell.original))
      [] [] σ σ (fun _ => []) (fun _ => []))

theorem FirstParameterCellCalls.prefixTransfers
    {packet : OriginalProjectionParameters sourceEnv U name info seedLevels}
    {requestedWF : ∀ level ∈ requestedLevels, level.WF U}
    {seedWF : ∀ level ∈ seedLevels, level.WF U}
    {equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels}
    {ordered : sourceEnv.Ordered}
    {cells : FirstProjectionParameterCells packet requestedWF seedWF equivalent}
    {familyHead : NormalizedFamilyPrefix packet}
    {ctorHead : FirstConstructorParameterPrefix ordered cells}
    (henv : env.Ordered) (below : sourceEnv ≤ env) (formed : OnCtx target (env.IsType U))
    (positive : 0 < info.nparams)
    (calls : FirstParameterCellCalls cells familyHead ctorHead env registry target σ) :
    FirstParameterPrefixTransfers cells familyHead env registry target σ := by
  have sourceEq := cells.normalizedDomain familyHead positive
  have seedPath : TypeConversion env U target (familyHead.domainExpression.subst σ)
      ((cells.common.instL seedLevels).subst σ) := by
    have raw := (cells.familyCell.original.forget.defeq.mono (packet.origin.baseBelow.trans below)).substDF
      henv (Ctx.SubstEq.wf (show Ctx.SubstEq env U target σ σ [] from .nil)) formed (.nil : Ctx.SubstEq env U target σ σ [])
    rw [sourceEq]
    exact .single raw.symm
  have seed : RichCodeTransfer env U registry target (.ref familyHead.domainOriginal)
      (.ref (.left cells.familyCell.original)) [] [] σ σ (fun _ => []) (fun _ => []) := by
    intro relevant n profile footprint query resources
    obtain ⟨first⟩ := calls.familyR query resources
    obtain ⟨second⟩ := calls.familyF first.certificate first.resources
    exact ⟨{ second with related := first.related.trans henv second.related }⟩
  cases calls.levels with
  | same equal sourceR =>
    refine ⟨seed, seedPath, ?_, ?_, Or.inl equal⟩
    · intro relevant n profile footprint query resources
      obtain ⟨first⟩ := seed query resources
      obtain ⟨second⟩ := sourceR first.certificate first.resources
      exact ⟨{ second with related := first.related.trans henv second.related }⟩
    · simpa only [equal] using seedPath
  | changed seedR universeF requestedR =>
    have bridge : RichCodeTransfer env U registry target (.ref familyHead.domainOriginal)
        (.ref (.left cells.universeCell.original)) [] [] σ σ (fun _ => []) (fun _ => []) := by
      intro relevant n profile footprint query resources
      obtain ⟨first⟩ := seed query resources
      obtain ⟨second⟩ := seedR first.certificate first.resources
      exact ⟨{ second with related := first.related.trans henv second.related }⟩
    refine ⟨seed, seedPath, ?_, ?_, Or.inr bridge⟩
    · intro relevant n profile footprint query resources
      obtain ⟨first⟩ := bridge query resources
      obtain ⟨second⟩ := universeF first.certificate first.resources
      obtain ⟨third⟩ := requestedR second.certificate second.resources
      exact ⟨{ third with related := first.related.trans henv (second.related.trans henv third.related) }⟩
    · have raw := (cells.universeCell.original.forget.defeq.mono (packet.origin.baseBelow.trans below)).substDF
        henv (Ctx.SubstEq.wf (show Ctx.SubstEq env U target σ σ [] from .nil)) formed (.nil : Ctx.SubstEq env U target σ σ [])
      exact seedPath.trans (.single raw)

/-- A real first slot in any one of the retained declaration contexts.
Its nominal owner and full generated owner-frame provenance are retained. -/
def GeneratedFirstParameterSlot
    {sourceEnv : VEnv} {headerEnv : VEnv} {U : Nat}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (domain : EndpointRef headerEnv U [] A (.sort level))
    {base : OriginalCaptureBase env U registry target}
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
    ScopedCaptureGenerated base commonLeft commonRight
      (.capture (.empty common) domain graph nominal provenance)
      ((OriginalRichFrame.nil (σ := commonLeft) (τ := commonRight) (locals := []) (available := fun _ => [])).group
        domain ordered ownerInitial [entry]).raw


theorem GeneratedFirstParameterSlot.realign
    {sourceEnv oldEnv headerEnv : VEnv} {U : Nat}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {oldDomain : EndpointRef oldEnv U [] oldA (.sort oldLevel)}
    (domain : EndpointRef headerEnv U [] A (.sort level))
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target context ownerLocals σ τ available)
    (ownerGenerated : ScopedCaptureGenerated base commonLeft commonRight graph ownerFrame.raw)
    (nominal : EndpointState sourceEnv U source argument assigned)
    (provenance : EndpointProvenance context nominal)
    (displayed : rawCapture.subst raw = argument.subst raw)
    (henv : env.Ordered) (ordered : sourceEnv.Ordered)
    (entry : RichGroupedCaptureEntry (field := field) (major := major) oldDomain env registry target
      [] commonLeft (fun _ => []) ownerInitial rawCapture (rawCapture.subst σ) (rawCapture.subst τ))
    (extension : OriginalFrameExtension ownerFrame.raw entry.frame.raw)
    (input : (⟨entry.rank, entry.input⟩ : Need) = ⟨n, demand⟩)
    (transfer : RichCodeTransfer env U registry target (.ref oldDomain) (.ref domain)
      [] [] commonLeft commonLeft (fun _ => []) (fun _ => []))
    (path : TypeConversion env U target (oldA.subst commonLeft) (A.subst commonLeft)) :
    GeneratedFirstParameterSlot (base := base) (field := field) (major := major) domain graph ownerFrame nominal provenance
      ordered commonLeft commonRight ownerInitial rawCapture (demand : Profile n) := by
  let changed := entry.realign henv transfer path
  refine ⟨changed, input, ⟨extension⟩, ?_⟩
  apply ScopedCaptureGenerated.group (ScopedCaptureGenerated.empty common commonLeft commonRight)
    domain ownerGenerated graph nominal provenance displayed ordered ownerInitial [changed]
  intro selected member
  cases List.mem_singleton.mp member
  exact ⟨extension⟩

/-- The next family/common and constructor/common contexts are generated
from the same original owner frame. The bridge context is produced only
when the actual retained universe comparison is used. -/
theorem FirstParameterPrefixTransfers.captureGroups
    {packet : OriginalProjectionParameters sourceEnv U name info seedLevels}
    {requestedWF : ∀ level ∈ requestedLevels, level.WF U}
    {seedWF : ∀ level ∈ seedLevels, level.WF U}
    {equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels}
    {cells : FirstProjectionParameterCells packet requestedWF seedWF equivalent}
    {familyHead : NormalizedFamilyPrefix packet}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target context ownerLocals σ τ available)
    (ownerGenerated : ScopedCaptureGenerated base commonLeft commonRight graph ownerFrame.raw)
    (nominal : EndpointState sourceEnv U source argument assigned)
    (provenance : EndpointProvenance context nominal)
    (displayed : rawCapture.subst raw = argument.subst raw)
    (henv : env.Ordered) (ordered : sourceEnv.Ordered)
    (entry : RichGroupedCaptureEntry (field := field) (major := major) familyHead.domainOriginal env registry target
      [] commonLeft (fun _ => []) ownerInitial rawCapture (rawCapture.subst σ) (rawCapture.subst τ))
    (extension : OriginalFrameExtension ownerFrame.raw entry.frame.raw)
    (input : (⟨entry.rank, entry.input⟩ : Need) = ⟨n, demand⟩)
    (transfers : FirstParameterPrefixTransfers cells familyHead env registry target commonLeft) :
    GeneratedFirstParameterSlot (base := base) (field := field) (major := major) (.left cells.familyCell.original)
      graph ownerFrame nominal provenance ordered commonLeft commonRight ownerInitial rawCapture (demand : Profile n) ∧
    GeneratedFirstParameterSlot (base := base) (field := field) (major := major) (.left cells.constructorCell.original)
      graph ownerFrame nominal provenance ordered commonLeft commonRight ownerInitial rawCapture demand ∧
    (seedLevels = requestedLevels ∨
      GeneratedFirstParameterSlot (base := base) (field := field) (major := major) (.left cells.universeCell.original)
        graph ownerFrame nominal provenance ordered commonLeft commonRight ownerInitial rawCapture demand) := by
  refine ⟨GeneratedFirstParameterSlot.realign _ graph ownerFrame ownerGenerated nominal provenance displayed
    henv ordered entry extension input transfers.seed transfers.seedPath,
    GeneratedFirstParameterSlot.realign _ graph ownerFrame ownerGenerated nominal provenance displayed
      henv ordered entry extension input transfers.requested transfers.requestedPath, ?_⟩
  rcases transfers.bridge with same | bridge
  · exact Or.inl same
  · exact Or.inr (GeneratedFirstParameterSlot.realign _ graph ownerFrame ownerGenerated nominal provenance displayed
      henv ordered entry extension input bridge transfers.seedPath)


/-- The separate original prefixes required by subsequent parameter
comparisons. An unused reflexive universe trace is deliberately absent. -/
def GeneratedFirstParameterPrefixes
    {packet : OriginalProjectionParameters sourceEnv U name info seedLevels}
    {requestedWF : ∀ level ∈ requestedLevels, level.WF U}
    {seedWF : ∀ level ∈ seedLevels, level.WF U}
    {equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels}
    (cells : FirstProjectionParameterCells packet requestedWF seedWF equivalent)
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target context ownerLocals σ τ available)
    (nominal : EndpointState sourceEnv U source argument assigned)
    (provenance : EndpointProvenance context nominal)
    (ordered : sourceEnv.Ordered) (commonLeft commonRight : Subst)
    (ownerInitial : List Closure) (rawCapture : VExpr) (input : Profile n) : Prop :=
    GeneratedFirstParameterSlot (base := base) (field := field) (major := major) (.left cells.familyCell.original)
      graph ownerFrame nominal provenance ordered commonLeft commonRight ownerInitial rawCapture input ∧
    GeneratedFirstParameterSlot (base := base) (field := field) (major := major) (.left cells.constructorCell.original)
      graph ownerFrame nominal provenance ordered commonLeft commonRight ownerInitial rawCapture input ∧
    (seedLevels = requestedLevels ∨
      GeneratedFirstParameterSlot (base := base) (field := field) (major := major) (.left cells.universeCell.original)
        graph ownerFrame nominal provenance ordered commonLeft commonRight ownerInitial rawCapture input)


/-- The generated first common slot is the actual context retained by the
next cell, because its proof is the trace's unique closed original cell. -/
theorem FirstParameterCell.contextOfSingle
    {trace : OriginalContextEquality sourceEnv U source destination}
    (first : FirstParameterCell trace A B)
    (tail : OriginalContextEquality sourceEnv U [A] [B])
    (retained : ∀ root ∈ tail.roots, root ∈ trace.roots) :
    tail.context = .cons .nil (.left first.original) := by
  cases tail with
  | cons previous original =>
    cases previous
    have same := trace.closedRoot_unique
      (⟨[], .nil, A, B, _, original⟩ : ParameterEqualityRoot sourceEnv U)
      first.root (retained _ List.mem_cons_self) first.retained rfl rfl
    cases first with
    | mk level firstOriginal firstRetained =>
      cases same
      rfl

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
