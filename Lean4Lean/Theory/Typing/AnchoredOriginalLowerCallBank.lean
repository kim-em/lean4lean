import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientReply
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientCaptureGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRouteCalls
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameAmbient
import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureGraphAmbient

/-! Uniform strictly smaller original induction clauses. Every semantic
source environment is required to be an actual subenvironment of the target;
a generated frame alone does not provide that inclusion. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

def AmbientGeneratedObservationCall
    (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    (left : OriginalNestedDisplay U common expression leftAssigned)
    (right : OriginalNestedDisplay U common expression rightAssigned)
    (commonLeft commonRight : Subst) (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (limit : Nat) : Prop :=
  ∀ {leftLocals leftAvailable}
    (leftFrame : OriginalCaptureRealization left.graph env registry target leftLocals commonLeft commonRight leftAvailable),
    AmbientCaptureGenerated base caps commonLeft commonRight left.graph leftFrame.frame.raw →
    leftAvailable.AtomClosed →
    ∀ {rightLocals rightAvailable}
    (rightFrame : OriginalCaptureRealization right.graph env registry target rightLocals commonLeft commonRight rightAvailable),
    AmbientCaptureGenerated base caps commonLeft commonRight right.graph rightFrame.frame.raw →
    rightAvailable.AtomClosed →
    richSchedule .expressionReindex
      ((Closure.close (left.node.dependencyOrigin lf) (leftFrame.frame.dependencyEnvironment lf)).cost +
       (Closure.close (right.node.dependencyOrigin rf) (rightFrame.frame.dependencyEnvironment rf)).cost) < limit →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
    RichObs left.sourceEnv env U registry target left.node leftLocals (left.raw.comp commonLeft) profile footprint →
    footprint.Available leftAvailable →
    Nonempty (AmbientBoundedGeneratedQueryReply base caps right commonLeft commonRight profile
      (environmentCost (rightFrame.frame.dependencyEnvironment rf)))

def AmbientGeneratedAssignedCall
    (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    (left : OriginalNestedDisplay U common expression leftAssigned)
    (right : OriginalNestedDisplay U common expression rightAssigned)
    (commonLeft commonRight : Subst) (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (limit : Nat) : Prop :=
  ∀ {leftLocals leftAvailable}
    (leftFrame : OriginalCaptureRealization left.graph env registry target leftLocals commonLeft commonRight leftAvailable),
    AmbientCaptureGenerated base caps commonLeft commonRight left.graph leftFrame.frame.raw →
    leftAvailable.AtomClosed →
    ∀ {rightLocals rightAvailable}
    (rightFrame : OriginalCaptureRealization right.graph env registry target rightLocals commonLeft commonRight rightAvailable),
    AmbientCaptureGenerated base caps commonLeft commonRight right.graph rightFrame.frame.raw →
    rightAvailable.AtomClosed →
    richSchedule .assignedComparison
      ((Closure.close (left.node.dependencyOrigin lf) (leftFrame.frame.dependencyEnvironment lf)).cost +
       (Closure.close (right.node.dependencyOrigin rf) (rightFrame.frame.dependencyEnvironment rf)).cost) < limit →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint} {relevant : Bool},
    RichCert left.sourceEnv env U registry target left.node.typeFormation.node leftLocals
      (left.raw.comp commonLeft) relevant profile footprint →
    footprint.Available leftAvailable →
    Nonempty (AmbientBoundedParameterReply base caps (leftAssigned.subst commonLeft)
      right.formationDisplay commonLeft commonRight profile
      (environmentCost (rightFrame.frame.dependencyEnvironment rf)))

/-- Unary F is restricted to actual hereditary ambient frames. -/
def OriginalAmbientComputationalInductionAt
    (env : VEnv) (registry : CanonicalHead.Registry) (ordered : sourceEnv.Ordered)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    {node : EndpointState sourceEnv U source expression assigned}
    (location : Located root node) (limit : Nat) : Prop :=
  ∀ target locals σ τ available,
    ∀ frame : OriginalRichFrame sourceEnv env U registry target
      (location.contextDerivation initial) locals σ τ available,
    frame.Ambient →
    (Closure.close (node.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost < limit →
    available.AtomClosed → OnCtx target (env.IsType U) → Ctx.SubstEq env U target σ τ source →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
    RichObs sourceEnv env U registry target node locals σ profile footprint →
    footprint.Available available →
    Nonempty (RichComputationalValue sourceEnv env U registry target node locals σ τ available profile)

def OriginalAmbientCodeInductionAt
    (env : VEnv) (registry : CanonicalHead.Registry) (ordered : sourceEnv.Ordered)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    {node : EndpointState sourceEnv U source expression (.sort level)}
    (location : Located root node) (limit : Nat) : Prop :=
  ∀ target locals σ τ available,
    ∀ frame : OriginalRichFrame sourceEnv env U registry target
      (location.contextDerivation initial) locals σ τ available,
    frame.Ambient →
    (Closure.close (node.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost < limit →
    available.AtomClosed → OnCtx target (env.IsType U) → Ctx.SubstEq env U target σ τ source →
    RichCodeTransfer env U registry target node node locals locals σ τ available available

def OriginalAmbientEqualityInductionAt
    (env : VEnv) (registry : CanonicalHead.Registry) (ordered : sourceEnv.Ordered)
    (context : ContextDerivation sourceEnv U source)
    (original : Derivation sourceEnv U source A B assigned) (limit : Nat) : Prop :=
  ∀ target locals σ available,
    ∀ frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available,
    frame.Ambient →
    richSchedule .fundamental
      (Closure.close (original.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost < limit →
    available.AtomClosed → OnCtx target (env.IsType U) → Ctx.SubstEq env U target σ σ source →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
    RichObs sourceEnv env U registry target (.ref (.left original)) locals σ profile footprint →
    footprint.Available available →
    Nonempty (OriginalEqualityQueryResult original env registry target locals σ σ available profile)

def OriginalAmbientParameterEqualityInductionAt
    (env : VEnv) (registry : CanonicalHead.Registry) (ordered : sourceEnv.Ordered)
    (context : ContextDerivation sourceEnv U source)
    (original : Derivation sourceEnv U source A B (.sort level)) (forward : Bool) (limit : Nat) : Prop :=
  ∀ target locals σ available,
    ∀ frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available,
    frame.Ambient →
    richSchedule .fundamental
      (Closure.close (original.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost < limit →
    available.AtomClosed → OnCtx target (env.IsType U) → Ctx.SubstEq env U target σ σ source →
    RichCodeTransfer env U registry target (.ref (parameterEqualitySide original forward))
      (.ref (parameterEqualitySide original (!forward))) locals locals σ σ available available

/-- This is the lower mutual-induction hypothesis, not an independently
proved fundamental theorem. Every clause has a strict original schedule and
all hidden source owners must belong to the target environment. -/
structure OriginalLowerCallBank (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (limit : Nat) : Prop where
  computational :
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
    richSchedule .fundamental
      (Closure.close (node.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost < limit →
    available.AtomClosed → OnCtx target (env.IsType U) → Ctx.SubstEq env U target σ τ source →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
    RichObs sourceEnv env U registry target node locals σ profile footprint →
    footprint.Available available →
    Nonempty (RichComputationalValue sourceEnv env U registry target node locals σ τ available profile)
  equality :
    ∀ {sourceEnv : VEnv} (ordered : sourceEnv.Ordered), sourceEnv ≤ env →
    ∀ {source : List VExpr} (context : ContextDerivation sourceEnv U source)
      {A B assigned : VExpr} (original : Derivation sourceEnv U source A B assigned) (forward : Bool),
    ∀ target locals σ available,
    ∀ frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available,
    frame.Ambient →
    richSchedule .fundamental
      (Closure.close (original.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost < limit →
    available.AtomClosed → OnCtx target (env.IsType U) → Ctx.SubstEq env U target σ σ source →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
    RichObs sourceEnv env U registry target (.ref (originalTypeRouteSide original forward)) locals σ profile footprint →
    footprint.Available available →
    Nonempty (OriginalDirectionalEqualityResult original forward env registry target locals σ σ available profile)
  observation :
    ∀ {target : List VExpr} (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps),
    ∀ {common : List VExpr} {expression leftAssigned rightAssigned : VExpr},
    ∀ (left : OriginalNestedDisplay U common expression leftAssigned)
      (right : OriginalNestedDisplay U common expression rightAssigned)
      (commonLeft commonRight : Subst) (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered),
    AmbientGeneratedObservationCall base caps left right commonLeft commonRight lf rf limit
  assigned :
    ∀ {target : List VExpr} (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps),
    ∀ {common : List VExpr} {expression leftAssigned rightAssigned : VExpr},
    ∀ (left : OriginalNestedDisplay U common expression leftAssigned)
      (right : OriginalNestedDisplay U common expression rightAssigned)
      (commonLeft commonRight : Subst) (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered),
    AmbientGeneratedAssignedCall base caps left right commonLeft commonRight lf rf limit

namespace OriginalLowerCallBank
variable (bank : OriginalLowerCallBank env U registry limit)
include bank

/-- Narrow the phase-indexed F clause to a parent's raw closure bound while
retaining the hereditary ambient premise on every selected frame. -/
theorem computationalAt
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource) {assignedType : VExpr}
    {node : EndpointState sourceEnv U source expression assignedType} (location : Located root node)
    (parentBound : richSchedule .fundamental parentCost < limit) :
    OriginalAmbientComputationalInductionAt env registry ordered initial location parentCost := by
  intro target locals σ τ available frame ambient bound closed formed substitutions n profile footprint query resources
  exact bank.computational ordered below initial location target locals σ τ available frame ambient
    (Nat.lt_trans (richSchedule_strict bound _ _) parentBound) closed formed substitutions query resources

theorem codeAt
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    {node : EndpointState sourceEnv U source expression (.sort level)} (location : Located root node)
    (parentBound : richSchedule .fundamental parentCost < limit) :
    OriginalAmbientCodeInductionAt env registry ordered initial location parentCost := by
  intro target locals σ τ available frame ambient bound closed formed substitutions relevant n profile footprint query resources
  obtain ⟨answer⟩ := bank.computationalAt ordered below initial location parentBound target locals σ τ available frame
    ambient bound closed formed substitutions (.code query) resources
  exact answer.code henv hscoped formed query.formed

theorem equalityAt
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (context : ContextDerivation sourceEnv U source) {assignedType : VExpr}
    (original : Derivation sourceEnv U source A B assignedType) :
    OriginalAmbientEqualityInductionAt env registry ordered context original limit := by
  intro target locals σ available frame ambient bound closed formed substitutions n profile footprint query resources
  obtain ⟨answer⟩ := bank.equality ordered below context original true target locals σ available frame
    ambient bound closed formed substitutions query resources
  exact ⟨{ support := answer.support, related := answer.related, rightQuery := answer.rightQuery }⟩

/-- Sorted parameter equality is derived in both directions from the same
original equality clause, including the false-sortable certificate channel. -/
theorem parameterEqualityAt
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (context : ContextDerivation sourceEnv U source)
    (original : Derivation sourceEnv U source A B (.sort level)) (forward : Bool) :
    OriginalAmbientParameterEqualityInductionAt env registry ordered context original forward limit := by
  intro target locals σ available frame ambient bound closed formed substitutions relevant n profile footprint query resources
  have sourceSide : parameterEqualitySide original forward = originalTypeRouteSide original forward := by
    cases forward <;> rfl
  have targetSide : parameterEqualitySide original (!forward) = originalTypeRouteSide original (!forward) := by
    cases forward <;> rfl
  obtain ⟨answer⟩ := bank.equality ordered below context original forward target locals σ available frame
    ambient bound closed formed substitutions (.code (sourceSide ▸ query)) resources
  obtain ⟨outFootprint, ⟨certificate⟩, outResources⟩ := answer.rightQuery.code henv query.formed
  refine ⟨{
    footprint := outFootprint
    certificate := ?_
    resources := outResources
    related := answer.related.code_of_sortable henv hscoped formed query.formed }⟩
  exact targetSide.symm ▸ certificate

end OriginalLowerCallBank
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
