import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedFamilyCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalScopedCaptureRealization
import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationStep

/-! The generated captured-variable reindex step selects an actual queried
owner, reconstructs its common source scope, and invokes only that strictly
smaller original query. Destination resources are chosen by the answer. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem lifted_substitution (e : VExpr) (raw : Subst) (depth : Nat) :
    (e.lift' (.skipN .refl depth)).subst (raw.liftN depth) =
      (e.subst raw).lift' (.skipN .refl depth) := by
  have step (expression : VExpr) (ρ : Lift) :
      expression.lift' (.skip ρ) = (expression.lift' ρ).lift := by
    rw [lift_eq_lift', ← lift'_comp]
    rfl
  induction depth with
  | zero => simp [Subst.liftN]
  | succ depth ih =>
    change (e.lift' (.skip (.skipN .refl depth))).subst (raw.liftN depth).lift =
      (e.subst raw).lift' (.skip (.skipN .refl depth))
    rw [step, lift_subst_lift, ih, step]

noncomputable def HeaderOwner.provenance
    {source : List VExpr}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (owner : HeaderOwner field major) (initial : ContextDerivation sourceEnv U source) :
    EndpointProvenance (owner.context initial) owner.node := by
  cases owner with
  | inl node => exact .ofLocation node.location initial
  | inr node => exact .ofLocation node.location initial

/-- Actual binders surrounding one retained owner, expressed over the
possibly heterogeneous common source graph. -/
structure GeneratedOwnerScope
    (base : OriginalCaptureBase env U registry target)
    {ownerContext : ContextDerivation sourceEnv U source}
    (ownerGraph : OriginalCaptureMap (common := commonSource) ownerContext ownerRaw)
    (commonLeft commonRight : Subst)
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) where
  common : List VExpr
  raw : Subst
  left : Subst
  right : Subst
  graph : OriginalCaptureMap (common := common) (entry.owner.context entry.initialContext) raw
  generated : ScopedCaptureGenerated base left right graph entry.frame.raw
  insertion : Ctx.Lift' (.skipN .refl entry.depth) commonSource common
  leftTail : Subst.lift_l (.skipN .refl entry.depth) left = commonLeft
  rightTail : Subst.lift_l (.skipN .refl entry.depth) right = commonRight
  expression_eq : entry.owner.expression.subst raw =
    (rawCapture.subst ownerRaw).lift' (.skipN .refl entry.depth)

/-- Scope reconstruction follows the previously checked traversal trace,
including all original fresh-binder certificates and guards. -/
theorem RichGroupedCaptureEntry.generateOwnerScope
    {source : List VExpr} {ownerLocals : List Nat}
    {ownerLeft ownerRight : Subst} {ownerAvailable : Valuation}
    {base : OriginalCaptureBase env U registry target}
    {ownerContext : ContextDerivation sourceEnv U source}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target ownerContext ownerLocals ownerLeft ownerRight ownerAvailable)
    (ownerGenerated : ScopedCaptureGenerated base commonLeft commonRight ownerGraph ownerFrame.raw)
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (extension : OriginalFrameExtension ownerFrame.raw entry.frame.raw) :
    Nonempty (GeneratedOwnerScope base ownerGraph commonLeft commonRight entry) := by
  obtain ⟨nextCommon, nextRaw, nextLeft, nextRight, nextGraph, generated, rawEq, insertion, leftTail, rightTail⟩ :=
    extension.generateScope ownerGenerated
  have depthEq := (entry.extensionRealizations extension).1
  rw [depthEq] at rawEq insertion leftTail rightTail
  refine ⟨⟨nextCommon, nextRaw, nextLeft, nextRight, nextGraph, generated, insertion, leftTail, rightTail, ?_⟩⟩
  rw [entry.expression_eq, rawEq]
  exact lifted_substitution _ _ _

noncomputable def GeneratedOwnerScope.display
    {common : List VExpr}
    {base : OriginalCaptureBase env U registry target}
    {ownerContext : ContextDerivation sourceEnv U source}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue}
    (scope : GeneratedOwnerScope base ownerGraph commonLeft commonRight entry) :
    OriginalNestedDisplay U scope.common
      ((rawCapture.subst ownerRaw).lift' (.skipN .refl entry.depth))
      (entry.owner.assigned.subst scope.raw) := {
  sourceEnv := sourceEnv, source := entry.owner.source
  sourceExpression := entry.owner.expression, sourceType := entry.owner.assigned
  context := entry.owner.context entry.initialContext, node := entry.owner.node
  provenance := entry.owner.provenance entry.initialContext
  raw := scope.raw, graph := scope.graph
  expression_eq := scope.expression_eq.symm, type_eq := rfl }

/-- A recursive answer chooses its finite destination frame and resources.
The original endpoint and its generated source graph remain fixed. -/
structure GeneratedQueryReply
    (base : OriginalCaptureBase env U registry target)
    (display : OriginalNestedDisplay U common expression assigned)
    (commonLeft commonRight : Subst) (requested : Profile n) where
  locals : List Nat
  available : Valuation
  realization : OriginalCaptureRealization display.graph env registry target locals commonLeft commonRight available
  generated : ScopedCaptureGenerated base commonLeft commonRight display.graph realization.frame.raw
  query : RichGradedResult display.sourceEnv env U registry target display.node locals
    (display.raw.comp commonLeft) available requested
  closed : available.AtomClosed

noncomputable def GeneratedQueryReply.restrict
    (reply : GeneratedQueryReply base display commonLeft commonRight (input : Profile n))
    (need : Need) (bounded : need.rank ≤ n)
    (covered : ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    GeneratedQueryReply base display commonLeft commonRight need.profile :=
  { reply with query := reply.query.localDemand need bounded covered }

/-- Common source weakening never relabels the original destination node. -/
def OriginalNestedDisplay.weaken
    {common : List VExpr} {expression assigned : VExpr}
    (display : OriginalNestedDisplay U common expression assigned)
    {ρ : Lift} (insertion : Ctx.Lift' ρ common next) :
    OriginalNestedDisplay U next (expression.lift' ρ) (assigned.lift' ρ) where
  sourceEnv := display.sourceEnv
  source := display.source
  sourceExpression := display.sourceExpression
  sourceType := display.sourceType
  context := display.context
  node := display.node
  provenance := display.provenance
  raw := display.raw.lift_r ρ
  graph := OriginalCaptureMap.weaken display.graph insertion
  expression_eq := by
    rw [← lift'_subst]
    exact congrArg (fun e : VExpr => e.lift' ρ) display.expression_eq
  type_eq := by
    rw [← lift'_subst]
    exact congrArg (fun e : VExpr => e.lift' ρ) display.type_eq

theorem GeneratedQueryReply.ofFrame
    {locals : List Nat} {available : Valuation}
    {base : OriginalCaptureBase env U registry target}
    (display : OriginalNestedDisplay U common expression assigned)
    (frame : OriginalRichFrame display.sourceEnv env U registry target display.context locals σ τ available)
    (generated : ScopedCaptureGenerated base commonLeft commonRight display.graph frame.raw)
    (substitutions : Ctx.SubstEq env U target σ τ display.source)
    (closed : available.AtomClosed)
    (query : RichGradedResult display.sourceEnv env U registry target display.node locals σ available requested) :
    Nonempty (GeneratedQueryReply base display commonLeft commonRight requested) := by
  obtain ⟨left, right⟩ := generated.realizations
  subst σ
  subst τ
  exact ⟨⟨locals, available, ⟨frame, substitutions⟩, generated, query, closed⟩⟩

/-- Return a query-dependent recursive answer from an enlarged common scope;
its actual frame and source query are transported only by exact substitution
identities. Generation is inverted at the source weakening constructor. -/
theorem GeneratedQueryReply.unweaken
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {ρ : Lift} (insertion : Ctx.Lift' ρ common next)
    (leftTail : Subst.lift_l ρ nextLeft = commonLeft)
    (rightTail : Subst.lift_l ρ nextRight = commonRight)
    (reply : GeneratedQueryReply base (display.weaken insertion) nextLeft nextRight requested) :
    Nonempty (GeneratedQueryReply base display commonLeft commonRight requested) := by
  have generated := reply.generated.unweaken
  rw [leftTail, rightTail] at generated
  exact GeneratedQueryReply.ofFrame display reply.realization.frame generated
    reply.realization.substitutions reply.closed reply.query


/-- The whole original owner query, not only its type formation, is paid by
the concrete group slot. The destination contributes the same exact cost on
both sides of the ensuing recursive comparison. -/
theorem RichGroupedCapture.ownerQuery_bound
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (tail : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available ownerInitial rawCapture leftValue rightValue)
    {entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      locals σ available ownerInitial rawCapture leftValue rightValue}
    (member : entry ∈ entries) (lookupOrigin : Origin) :
    (Closure.close (entry.owner.node.dependencyOrigin ordered)
      (entry.frame.dependencyEnvironment ordered)).cost <
      (Closure.close lookupOrigin
        ((tail.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered)).cost := by
  rw [OriginalRichFrame.group_environment]
  have original := variable_lookup lookupOrigin
    (entries.lookup_member ordered headerOrdered member ownerInitial (tail.dependencyEnvironment headerOrdered))
  have actual : (Closure.close (entry.owner.node.dependencyOrigin ordered)
      (entry.frame.dependencyEnvironment ordered)).cost ≤
      (entry.owner.dependencyClosure ordered ownerInitial).cost :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left (entry.frame_environment_le ordered) _)
  exact Nat.lt_of_le_of_lt (Nat.le_trans actual (Nat.le_add_right _ _)) original

/-- The captured-variable source-reindex branch. Need membership chooses an
ACTUAL stored whole query. Its original binder scope is generated, the right
input frame is source-weakened, and the strictly smaller reply chooses its
own finite output frame. Restriction and scope return use that same reply. -/
theorem RichGroupedCapture.reindexGeneratedHead
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation headerEnv U headerSource}
    {graph : OriginalCaptureMap (common := common) context raw}
    (tail : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (generated : ScopedCaptureGenerated base commonLeft commonRight graph tail.raw)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    {ownerContext : ContextDerivation sourceEnv U source}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target ownerContext ownerLocals ownerLeft ownerRight ownerAvailable)
    (ownerGenerated : ScopedCaptureGenerated base commonLeft commonRight ownerGraph ownerFrame.raw)
    {nominalContext : ContextDerivation nominalEnv U nominalSource}
    (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
    (nominal : EndpointState nominalEnv U nominalSource argument assigned)
    (provenance : EndpointProvenance nominalContext nominal)
    (displayed : rawCapture.subst ownerRaw = argument.subst nominalRaw)
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available ownerInitial rawCapture leftValue rightValue)
    (owners : ∀ entry ∈ entries, Nonempty (OriginalFrameExtension ownerFrame.raw entry.frame.raw))
    (variableNode : EndpointState headerEnv U (A :: headerSource) (.bvar 0) variableType)
    (need : Need) (member : need ∈ entries.needs)
    (destination : OriginalNestedDisplay U common (rawCapture.subst ownerRaw) destinationType)
    (destinationOrdered : destination.sourceEnv.Ordered)
    (destinationFrame : OriginalCaptureRealization destination.graph env registry target
      destinationLocals commonLeft commonRight destinationAvailable)
    (destinationGenerated : ScopedCaptureGenerated base commonLeft commonRight destination.graph destinationFrame.frame.raw)
    (reindex : ∀ entry ∈ entries,
      ∀ scope : GeneratedOwnerScope base ownerGraph commonLeft commonRight entry,
      ∀ next : OriginalCaptureRealization (destination.weaken scope.insertion).graph env registry target
        destinationLocals scope.left scope.right destinationAvailable,
      ScopedCaptureGenerated base scope.left scope.right (destination.weaken scope.insertion).graph next.frame.raw →
      next.frame.dependencyEnvironment destinationOrdered = destinationFrame.frame.dependencyEnvironment destinationOrdered →
      richSchedule .expressionReindex
        ((Closure.close (entry.owner.node.dependencyOrigin ordered) (entry.frame.dependencyEnvironment ordered)).cost +
          (Closure.close (destination.node.dependencyOrigin destinationOrdered) (next.frame.dependencyEnvironment destinationOrdered)).cost) <
      richSchedule .expressionReindex
        ((Closure.close (variableNode.dependencyOrigin headerOrdered)
          ((tail.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered)).cost +
          (Closure.close (destination.node.dependencyOrigin destinationOrdered)
            (destinationFrame.frame.dependencyEnvironment destinationOrdered)).cost) →
      Nonempty (GeneratedQueryReply base (destination.weaken scope.insertion) scope.left scope.right entry.input)) :
    ScopedCaptureGenerated base commonLeft commonRight
      (.capture graph domain nominalGraph nominal provenance)
      ((tail.group domain ordered ownerInitial entries).raw) ∧
      Nonempty (GeneratedQueryReply base destination commonLeft commonRight need.profile) := by
  obtain ⟨entry, present, requested⟩ := List.mem_flatMap.mp member
  obtain ⟨extension⟩ := owners entry present
  have values := entry.extensionRealizations extension
  have inputGenerated := ScopedCaptureGenerated.groupOfValues generated domain ownerGenerated nominalGraph
    nominal provenance displayed ordered ownerInitial entries owners values.2.2.2.1 values.2.2.2.2
  obtain ⟨scope⟩ := entry.generateOwnerScope ownerFrame ownerGenerated extension
  obtain ⟨next, nextGenerated, sameEnvironment⟩ := destinationFrame.weakenGenerated destinationGenerated
    scope.insertion scope.leftTail scope.rightTail
  have bound : richSchedule .expressionReindex
      ((Closure.close (entry.owner.node.dependencyOrigin ordered) (entry.frame.dependencyEnvironment ordered)).cost +
        (Closure.close (destination.node.dependencyOrigin destinationOrdered) (next.frame.dependencyEnvironment destinationOrdered)).cost) <
      richSchedule .expressionReindex
      ((Closure.close (variableNode.dependencyOrigin headerOrdered)
        ((tail.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered)).cost +
        (Closure.close (destination.node.dependencyOrigin destinationOrdered)
          (destinationFrame.frame.dependencyEnvironment destinationOrdered)).cost) := by
    rw [sameEnvironment destinationOrdered]
    exact richSchedule_strict (Nat.add_lt_add_right
      (entries.ownerQuery_bound ordered headerOrdered tail present (variableNode.dependencyOrigin headerOrdered)) _) _ _
  obtain ⟨reply⟩ := reindex entry present scope next nextGenerated (sameEnvironment destinationOrdered) bound
  have requestedQuery := reply.restrict need (captureNeeds_covered entry.input need requested).1
    (captureNeeds_covered entry.input need requested).2
  exact ⟨inputGenerated, requestedQuery.unweaken scope.insertion scope.leftTail scope.rightTail⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
