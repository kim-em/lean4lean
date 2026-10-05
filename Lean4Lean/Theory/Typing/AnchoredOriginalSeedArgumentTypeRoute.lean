import Lean4Lean.Theory.Typing.AnchoredOriginalScopedSeedTypeRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentPair

/-! The first type-history edge compares actual TERM occurrences: a retained
whole cut and the independently checked argument of the assigned family.
Their types need not have the same source expression. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {headerAvailable : Valuation}

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

noncomputable def PendingRichCapture.scopeTermDisplay
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial argument leftValue rightValue)
    (scope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps pending.depth
      (pending.owner.context pending.initialContext)) :
    OriginalNestedDisplay U scope.scope ((argument.subst ownerRaw).lift' (.skipN .refl pending.depth))
      (pending.owner.assigned.subst scope.raw) where
  sourceEnv := sourceEnv
  source := pending.owner.source
  sourceExpression := pending.owner.expression
  sourceType := pending.owner.assigned
  context := pending.owner.context pending.initialContext
  node := pending.owner.node
  provenance := pending.owner.provenance pending.initialContext
  raw := scope.raw
  graph := scope.graph
  expression_eq := by rw [pending.expression_eq, scope.raw_eq, lifted_substitution]
  type_eq := rfl

theorem PendingRichCapture.scopeTermDisplay_formation
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial argument leftValue rightValue)
    (scope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps pending.depth
      (pending.owner.context pending.initialContext)) :
    (pending.scopeTermDisplay scope).formationDisplay = pending.assignedScopeDisplayRaw scope := rfl

/-- The actual selected family argument is weakened into the cut's common
scope. Its exact application location and inferred type are retained. -/
theorem PendingRichCapture.familyArgumentRoute
    {base : OriginalCaptureBase env U registry target}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) arguments)}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial argument leftValue rightValue)
    (scope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps pending.depth
      (pending.owner.context pending.initialContext))
    (index : Nat) (selected : arguments[index]? = some argument)
    (argumentGraph : OriginalCaptureMap (common := common)
      ((assignedFamilyApplication major index selected).argument.location.contextDerivation pending.initialContext)
      ownerRaw)
    (argumentFrame : OriginalCaptureRealization argumentGraph env registry target
      argumentLocals commonLeft commonRight argumentAvailable)
    (argumentCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight argumentGraph argumentFrame.frame.raw)
    (closed : argumentAvailable.AtomClosed) (ordered : sourceEnv.Ordered) :
    ∃ route : RawGeneratedTypeRoute env registry target scope.left scope.right
        (pending.assignedScopeDisplayRaw scope)
        ((OriginalNestedDisplay.ofOccurrence pending.initialContext
          (assignedFamilyApplication major index selected).argument.location argumentGraph).weaken
          scope.insertion).formationDisplay
        (pending.frame.dependencyEnvironment ordered)
        (argumentFrame.frame.dependencyEnvironment ordered),
      route.Generated base scope.caps ∧
      route.reserve = [Closure.bundle
        (Closure.close (pending.owner.node.dependencyOrigin ordered)
          (pending.frame.dependencyEnvironment ordered))
        (Closure.close ((assignedFamilyApplication major index selected).view.argument.dependencyOrigin ordered)
          (argumentFrame.frame.dependencyEnvironment ordered))] := by
  obtain ⟨actual, capped, same⟩ := argumentFrame.weakenCapped argumentCapped
    scope.insertion scope.leftTail scope.rightTail scope.capsTail
  let display := (OriginalNestedDisplay.ofOccurrence pending.initialContext
    (assignedFamilyApplication major index selected).argument.location argumentGraph).weaken scope.insertion
  let frame : OriginalTypeRouteFrame env registry target display.graph scope.left scope.right :=
    ⟨argumentLocals, argumentAvailable, actual, closed⟩
  let route := RawGeneratedTypeRoute.assigned (pending.scopeTermDisplay scope) display ordered ordered
    (pending.frame.dependencyEnvironment ordered) frame
  have generated : route.Generated base scope.caps := by
    refine ⟨?_, ?_⟩
    · dsimp only [route]
      rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
    · intro boxed member
      simp only [route, RawGeneratedTypeRoute.frames, List.mem_singleton] at member
      subst boxed
      exact capped
  rw [← same ordered]
  refine ⟨route, generated, ?_⟩
  simp only [route, RawGeneratedTypeRoute.reserve]
  rfl

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
