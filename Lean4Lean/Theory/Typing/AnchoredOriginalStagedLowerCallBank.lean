import Lean4Lean.Theory.Typing.AnchoredOriginalLowerCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureGeneration

/-! A two-coordinate interface for the checked native-header and eta steps.
Ordinary original calls lower their closure schedule at a fixed declaration
stage; retained native headers can lower the stage independently of proof size.
Every selected R/C output preserves the SAME hereditary stage witness.
This is a conditional induction hypothesis, not the complete global motive:
canonical definition bodies also require equation cutoffs and stratified fuel
preserved on the selected outputs. Record terminals now retain raw projection
guards without borrowing later metadata proofs; complete record reconstruction
and equality dispatch still have to be connected. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096

/-- The actual chosen query frame retains hereditary generation, including
its scoped owners and dormant histories. -/
structure SourceBoundedGeneratedQueryReply (P : VEnv → Prop)
    (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    (display : OriginalNestedDisplay U common expression assigned)
    (left right : Subst) (profile : Profile n) (capacity : Nat)
    extends BoundedGeneratedQueryReply base caps display left right profile capacity where
  generation : SourceCaptureGenerated P base caps left right display.graph
    toBoundedGeneratedQueryReply.answer.reply.realization.frame.raw

/-- Assigned comparison returns semantics and the SAME hereditarily generated
selected frame, including for an empty requested profile. -/
structure SourceBoundedParameterReply (P : VEnv → Prop)
    (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    (start : VExpr) (display : OriginalNestedDisplay U common expression assigned)
    (left right : Subst) (profile : Profile n) (capacity : Nat)
    extends BoundedParameterReply base caps start display left right profile capacity where
  generation : SourceCaptureGenerated P base caps left right display.graph
    toBoundedParameterReply.reply.answer.reply.realization.frame.raw

theorem SourceBoundedGeneratedQueryReply.ambient
    (reply : SourceBoundedGeneratedQueryReply P base caps display left right profile capacity) :
    reply.answer.reply.realization.frame.Ambient := reply.generation.ambientGenerated.ambient.2

theorem SourceBoundedParameterReply.ambient
    (reply : SourceBoundedParameterReply P base caps start display left right profile capacity) :
    reply.reply.answer.reply.realization.frame.Ambient := reply.generation.ambientGenerated.ambient.2

def SourceGeneratedObservationCall (P : VEnv → Prop)
    (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    (left : OriginalNestedDisplay U common expression leftAssigned)
    (right : OriginalNestedDisplay U common expression rightAssigned)
    (commonLeft commonRight : Subst) (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (callStage stage limit : Nat) : Prop :=
  ∀ {leftLocals leftAvailable}
    (leftFrame : OriginalCaptureRealization left.graph env registry target leftLocals commonLeft commonRight leftAvailable),
    SourceCaptureGenerated P base caps commonLeft commonRight left.graph leftFrame.frame.raw →
    leftAvailable.AtomClosed →
    ∀ {rightLocals rightAvailable}
    (rightFrame : OriginalCaptureRealization right.graph env registry target rightLocals commonLeft commonRight rightAvailable),
    SourceCaptureGenerated P base caps commonLeft commonRight right.graph rightFrame.frame.raw →
    rightAvailable.AtomClosed →
    Prod.Lex Nat.lt Nat.lt (callStage, richSchedule .expressionReindex
      ((Closure.close (left.node.dependencyOrigin lf) (leftFrame.frame.dependencyEnvironment lf)).cost +
       (Closure.close (right.node.dependencyOrigin rf) (rightFrame.frame.dependencyEnvironment rf)).cost)) (stage, limit) →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
    RichObs left.sourceEnv env U registry target left.node leftLocals (left.raw.comp commonLeft) profile footprint →
    footprint.Available leftAvailable →
    Nonempty (SourceBoundedGeneratedQueryReply P base caps right commonLeft commonRight profile
      (environmentCost (rightFrame.frame.dependencyEnvironment rf)))

def SourceGeneratedAssignedCall (P : VEnv → Prop)
    (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    (left : OriginalNestedDisplay U common expression leftAssigned)
    (right : OriginalNestedDisplay U common expression rightAssigned)
    (commonLeft commonRight : Subst) (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (callStage stage limit : Nat) : Prop :=
  ∀ {leftLocals leftAvailable}
    (leftFrame : OriginalCaptureRealization left.graph env registry target leftLocals commonLeft commonRight leftAvailable),
    SourceCaptureGenerated P base caps commonLeft commonRight left.graph leftFrame.frame.raw →
    leftAvailable.AtomClosed →
    ∀ {rightLocals rightAvailable}
    (rightFrame : OriginalCaptureRealization right.graph env registry target rightLocals commonLeft commonRight rightAvailable),
    SourceCaptureGenerated P base caps commonLeft commonRight right.graph rightFrame.frame.raw →
    rightAvailable.AtomClosed →
    Prod.Lex Nat.lt Nat.lt (callStage, richSchedule .assignedComparison
      ((Closure.close (left.node.dependencyOrigin lf) (leftFrame.frame.dependencyEnvironment lf)).cost +
       (Closure.close (right.node.dependencyOrigin rf) (rightFrame.frame.dependencyEnvironment rf)).cost)) (stage, limit) →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint} {relevant : Bool},
    RichCert left.sourceEnv env U registry target left.node.typeFormation.node leftLocals
      (left.raw.comp commonLeft) relevant profile footprint →
    footprint.Available leftAvailable →
    Nonempty (SourceBoundedParameterReply P base caps (leftAssigned.subst commonLeft)
      right.formationDisplay commonLeft commonRight profile
      (environmentCost (rightFrame.frame.dependencyEnvironment rf)))

/-- Neither this bank nor the old uniform bank is proved globally yet.
The stage qualification on actual frames is essential at an earlier-header edge. -/
structure StagedOriginalLowerCallBank (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (stage limit : Nat) : Prop where
  computational :
    ∀ callStage,
    ∀ {sourceEnv : VEnv} (ordered : sourceEnv.Ordered), sourceEnv ≤ env →
    ∀ {rootSource : List VExpr} {rootExpression rootType : VExpr}
      {root : EndpointRef sourceEnv U rootSource rootExpression rootType},
    ∀ (initial : ContextDerivation sourceEnv U rootSource)
      {source : List VExpr} {expression assignedType : VExpr}
      {node : EndpointState sourceEnv U source expression assignedType} (location : Located root node),
    ∀ target locals σ τ available,
    ∀ frame : OriginalRichFrame sourceEnv env U registry target
      (location.contextDerivation initial) locals σ τ available,
    frame.Ambient →
    frame.AllSources (SourceAtStage callStage) →
    Prod.Lex Nat.lt Nat.lt (callStage, richSchedule .fundamental
      (Closure.close (node.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost) (stage, limit) →
    available.AtomClosed → OnCtx target (env.IsType U) → Ctx.SubstEq env U target σ τ source →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
    RichObs sourceEnv env U registry target node locals σ profile footprint →
    footprint.Available available →
    Nonempty (RichComputationalValue sourceEnv env U registry target node locals σ τ available profile)
  equality :
    ∀ callStage,
    ∀ {sourceEnv : VEnv} (ordered : sourceEnv.Ordered), sourceEnv ≤ env →
    ∀ {source : List VExpr} (context : ContextDerivation sourceEnv U source)
      {A B assigned : VExpr} (original : Derivation sourceEnv U source A B assigned) (forward : Bool),
    ∀ target locals σ available,
    ∀ frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available,
    frame.Ambient →
    frame.AllSources (SourceAtStage callStage) →
    Prod.Lex Nat.lt Nat.lt (callStage, richSchedule .fundamental
      (Closure.close (original.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost) (stage, limit) →
    available.AtomClosed → OnCtx target (env.IsType U) → Ctx.SubstEq env U target σ σ source →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
    RichObs sourceEnv env U registry target (.ref (originalTypeRouteSide original forward)) locals σ profile footprint →
    footprint.Available available →
    Nonempty (OriginalDirectionalEqualityResult original forward env registry target locals σ σ available profile)
  observation :
    ∀ callStage,
    ∀ {target : List VExpr} (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps),
    ∀ {common : List VExpr} {expression leftAssigned rightAssigned : VExpr},
    ∀ (left : OriginalNestedDisplay U common expression leftAssigned)
      (right : OriginalNestedDisplay U common expression rightAssigned)
      (commonLeft commonRight : Subst) (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered),
    SourceGeneratedObservationCall (SourceAtStage callStage) base caps left right commonLeft commonRight lf rf callStage stage limit
  assigned :
    ∀ callStage,
    ∀ {target : List VExpr} (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps),
    ∀ {common : List VExpr} {expression leftAssigned rightAssigned : VExpr},
    ∀ (left : OriginalNestedDisplay U common expression leftAssigned)
      (right : OriginalNestedDisplay U common expression rightAssigned)
      (commonLeft commonRight : Subst) (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered),
    SourceGeneratedAssignedCall (SourceAtStage callStage) base caps left right commonLeft commonRight lf rf callStage stage limit

/-- The actual retained earlier header is a legal lexicographic call even
when it differs from the header selected by the local constDF measure. -/
theorem StagedOriginalLowerCallBank.closedHeaderComputational
    (bank : StagedOriginalLowerCallBank env U registry stage limit)
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (sourceStage : SourceAtStage stage sourceEnv)
    {levels : List VLevel}
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (formed : OnCtx target (env.IsType U))
    (query : RichObs origin.source env U registry target
      (.ref (origin.familyHeader levelsWF).reference) [] σ (profile : Profile n) []) :
    Nonempty (RichComputationalValue origin.source env U registry target
      (.ref (origin.familyHeader levelsWF).reference) [] σ τ (fun _ => []) profile) := by
  let frame := OriginalRichFrame.nil (sourceEnv := origin.source) (env := env)
    (U := U) (registry := registry) (target := target) (locals := [])
    (σ := σ) (τ := τ) (available := fun _ => [])
  have ambient : frame.Ambient := by
    change (RawOriginalRichFrame.nil (sourceEnv := origin.source) (env := env)).Ambient
    rw [RawOriginalRichFrame.Ambient.eq_def]
    exact ⟨origin.sourceBelow.trans below, trivial⟩
  have bounded : frame.AllSources (SourceAtStage origin.ordered.constantCount) := by
    change (RawOriginalRichFrame.nil (sourceEnv := origin.source) (env := env)).AllSources _
    rw [RawOriginalRichFrame.AllSources.eq_def]
    exact ⟨fun _ => Nat.le_refl _, trivial⟩
  apply bank.computational origin.ordered.constantCount origin.ordered (origin.sourceBelow.trans below)
    .nil (.here (root := (origin.familyHeader levelsWF).reference)) target [] σ τ
    (fun _ => []) frame ambient bounded
  · exact originalHeader_lex_lt origin ordered sourceStage _ _
  · intro _ _ member; cases member
  · exact formed
  · exact .nil
  · exact query
  · intro _ _ member; cases member

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
