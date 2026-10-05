import Lean4Lean.Theory.Typing.AnchoredOriginalLambdaDiagonal

/-! Natural lambda type-code coherence for arbitrary current certificates.
Every recursive premise is fixed at actual original body/formation children;
all frames and finite row requests are constructed by this consumer. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem LamView.naturalQueries
    {commonAvailable : Valuation}
    {leftRoot : EndpointRef leftEnv U leftRootSource leftRootExpression leftRootType}
    {rightRoot : EndpointRef rightEnv U rightRootSource rightRootExpression rightRootType}
    {leftNode : EndpointState leftEnv U leftSource (.lam A expression) leftAssigned}
    {rightNode : EndpointState rightEnv U rightSource (.lam C otherExpression) rightAssigned}
    {leftStart : Located leftRoot leftNode} {rightStart : Located rightRoot rightNode}
    (leftView : LamView leftStart) (rightView : LamView rightStart)
    (leftInitial : ContextDerivation leftEnv U leftRootSource)
    (rightInitial : ContextDerivation rightEnv U rightRootSource)
    (leftInsertion : Ctx.Lift' leftMap leftSource displayed)
    (rightInsertion : Ctx.Lift' rightMap rightSource displayed)
    (leftAnnotation : annotation = A.lift' leftMap)
    (rightAnnotation : annotation = C.lift' rightMap)
    (leftExpression : displayedBody = expression.lift' leftMap.cons)
    (rightExpression : displayedBody = otherExpression.lift' rightMap.cons)
    (henv : env.Ordered) (hscoped : registry.Scoped) (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (bodyIH : DisplayCoherence env U registry
      (leftView.bodyDisplayAs leftInitial leftInsertion leftAnnotation leftExpression)
      (rightView.bodyDisplayAs rightInitial rightInsertion rightAnnotation rightExpression))
    (closed : commonAvailable.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (leftTail : TailFits leftEnv env U registry target leftSource leftLocals
      (Subst.lift_l leftMap common) (Subst.lift_l leftMap common)
      (fun index => commonAvailable (leftMap.liftVar index)))
    (rightTail : TailFits rightEnv env U registry target rightSource rightLocals
      (Subst.lift_l rightMap common) (Subst.lift_l rightMap common)
      (fun index => commonAvailable (rightMap.liftVar index)))
    (leftSubs : Ctx.SubstEq env U target
      (Subst.lift_l leftMap common) (Subst.lift_l leftMap common) leftSource)
    (rightSubs : Ctx.SubstEq env U target
      (Subst.lift_l rightMap common) (Subst.lift_l rightMap common) rightSource)
    (leftDomainIH : StateFundamental env registry
      (leftView.location.contextDerivation leftInitial) leftView.domain)
    (leftCodomainIH : StateFundamental env registry
      ((Located.lamCodomain leftView.location).contextDerivation leftInitial) leftView.codomain)
    (rightDomainIH : StateFundamental env registry
      (rightView.location.contextDerivation rightInitial) rightView.domain)
    (rightCodomainIH : StateFundamental env registry
      ((Located.lamCodomain rightView.location).contextDerivation rightInitial) rightView.codomain)
    (certificate : CodeCert env U registry target leftLocals (Subst.lift_l leftMap common)
      (.forallE A leftView.bodyType) profile footprint)
    (resources : footprint.Available (fun index => commonAvailable (leftMap.liftVar index))) :
    Nonempty (CodeTransferResult env U registry target rightLocals
      (Subst.lift_l leftMap common) (Subst.lift_l rightMap common)
      (fun index => commonAvailable (rightMap.liftVar index))
      (.forallE A leftView.bodyType) (.forallE C rightView.bodyType) profile) := by
  have sameDomain := leftAnnotation.symm.trans rightAnnotation
  have domains := OriginalFactorCut.realized_between_displays (common := common) sameDomain rfl rfl
  have leftClosed : Valuation.AtomClosed (fun index => commonAvailable (leftMap.liftVar index)) := by
    intro index need member atom present
    exact closed _ need member atom present
  have rightClosed : Valuation.AtomClosed (fun index => commonAvailable (rightMap.liftVar index)) := by
    intro index need member atom present
    exact closed _ need member atom present
  have formedA := leftView.domain.sound.defeq.mono leftBelow
  have formedC := rightView.domain.sound.defeq.mono rightBelow
  have hA := formedA.subst henv leftSubs.left hTarget
  have hC := formedC.subst henv rightSubs.left hTarget
  have hAnnotation : env.IsType U target (annotation.subst common) := by
    rw [leftAnnotation, subst_lift']
    exact ⟨_, hA⟩
  have rawBodies := LamView.rawBodyPath leftView rightView leftInitial rightInitial
    leftInsertion rightInsertion leftAnnotation rightAnnotation leftExpression rightExpression
    henv leftBelow rightBelow bodyIH closed hTarget leftTail rightTail leftSubs rightSubs hAnnotation
  have annotationRealized : annotation.subst common = A.subst (Subst.lift_l leftMap common) := by
    rw [leftAnnotation, subst_lift']
  rw [annotationRealized] at rawBodies
  have leftContext : OnCtx (A.subst (Subst.lift_l leftMap common) :: target) (env.IsType U) :=
    ⟨hTarget, _, hA⟩
  have rightContext : OnCtx (C.subst (Subst.lift_l rightMap common) :: target) (env.IsType U) :=
    ⟨hTarget, _, hC⟩
  have hB := (leftView.codomain.sound.defeq.mono leftBelow).subst henv
    (leftSubs.left.lift henv formedA) leftContext
  have hD := (rightView.codomain.sound.defeq.mono rightBelow).subst henv
    (rightSubs.left.lift henv formedC) rightContext
  have primitive : LambdaPiCase (env := env) (U := U) (registry := registry)
      (target := target) (leftLocals := leftLocals) (rightLocals := rightLocals)
      (σ := Subst.lift_l leftMap common) (τ := Subst.lift_l rightMap common)
      (leftAvailable := fun index => commonAvailable (leftMap.liftVar index))
      (rightAvailable := fun index => commonAvailable (rightMap.liftVar index))
      (A := A) (B := leftView.bodyType) (C := C) (D := rightView.bodyType) := by
    intro n ambient table prototypeDomain prototypeBody domainFootprint rowFootprint domain guard rows incoming
    have domainResources := fun i need member => incoming i need (List.mem_append_left _ member)
    have rowResources := fun i need member => incoming i need (List.mem_append_right _ member)
    obtain ⟨answers⟩ := LamView.rowAnswers leftView rightView leftInitial rightInitial
      leftInsertion rightInsertion leftAnnotation rightAnnotation leftExpression rightExpression
      henv leftBelow rightBelow bodyIH closed hTarget leftTail rightTail leftSubs rightSubs
      domain rows domainResources rowResources
    obtain ⟨rightFootprint, ⟨rightDomain⟩, rightResources⟩ :=
      OriginalFactorCut.CodeCert.betweenDisplays domain leftMap rightMap common rfl rfl sameDomain
        [] rightLocals domainResources (fun _ => rfl) (fun _ => rfl)
    obtain ⟨rightRows⟩ := answers.replay domains
    have rightGuard := guard.reindexBodies domains rawBodies
    have leftFormation := leftView.piDiagonal leftInitial henv hscoped leftBelow
      leftDomainIH leftCodomainIH leftClosed hTarget leftSubs leftTail
      domain guard rows domainResources rowResources
    have rightFormation := rightView.piDiagonal rightInitial henv hscoped rightBelow
      rightDomainIH rightCodomainIH rightClosed hTarget rightSubs rightTail
      rightDomain rightGuard rightRows.bodies rightResources rightRows.resources
    have domainChild : GradedTransfer env U registry target leftLocals
        (Subst.lift_l leftMap common) (Subst.lift_l leftMap common)
        (fun index => commonAvailable (leftMap.liftVar index)) A A (.sort leftView.domainLevel) :=
      (leftDomainIH target leftLocals _ _ _ leftClosed hTarget leftSubs
        (TailPairedFits.diagonal (leftView.location.contextDerivation leftInitial) leftTail)).1
    obtain ⟨domainAnswer⟩ := domain.transfer_graded henv hscoped hTarget leftClosed domainChild domainResources
    exact answers.comparePi henv hscoped hTarget domain guard (domain.pi guard rows).formed
      leftMap rightMap common rfl rfl sameDomain [] domainResources (fun _ => rfl) (fun _ => rfl)
      ⟨_, hA⟩ ⟨_, hB⟩ ⟨_, hD⟩ rawBodies domainAnswer.related leftFormation rightFormation
  exact CodeCert.transferLambdaPi henv hscoped primitive certificate resources

/-- The natural type path is produced even when no code query is requested. -/
theorem LamView.naturalPath
    {commonAvailable : Valuation}
    {leftRoot : EndpointRef leftEnv U leftRootSource leftRootExpression leftRootType}
    {rightRoot : EndpointRef rightEnv U rightRootSource rightRootExpression rightRootType}
    {leftNode : EndpointState leftEnv U leftSource (.lam A expression) leftAssigned}
    {rightNode : EndpointState rightEnv U rightSource (.lam C otherExpression) rightAssigned}
    {leftStart : Located leftRoot leftNode} {rightStart : Located rightRoot rightNode}
    (leftView : LamView leftStart) (rightView : LamView rightStart)
    (leftInitial : ContextDerivation leftEnv U leftRootSource)
    (rightInitial : ContextDerivation rightEnv U rightRootSource)
    (leftInsertion : Ctx.Lift' leftMap leftSource displayed)
    (rightInsertion : Ctx.Lift' rightMap rightSource displayed)
    (leftAnnotation : annotation = A.lift' leftMap)
    (rightAnnotation : annotation = C.lift' rightMap)
    (leftExpression : displayedBody = expression.lift' leftMap.cons)
    (rightExpression : displayedBody = otherExpression.lift' rightMap.cons)
    (henv : env.Ordered) (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (bodyIH : DisplayCoherence env U registry
      (leftView.bodyDisplayAs leftInitial leftInsertion leftAnnotation leftExpression)
      (rightView.bodyDisplayAs rightInitial rightInsertion rightAnnotation rightExpression))
    (closed : commonAvailable.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (leftTail : TailFits leftEnv env U registry target leftSource leftLocals
      (Subst.lift_l leftMap common) (Subst.lift_l leftMap common)
      (fun index => commonAvailable (leftMap.liftVar index)))
    (rightTail : TailFits rightEnv env U registry target rightSource rightLocals
      (Subst.lift_l rightMap common) (Subst.lift_l rightMap common)
      (fun index => commonAvailable (rightMap.liftVar index)))
    (leftSubs : Ctx.SubstEq env U target
      (Subst.lift_l leftMap common) (Subst.lift_l leftMap common) leftSource)
    (rightSubs : Ctx.SubstEq env U target
      (Subst.lift_l rightMap common) (Subst.lift_l rightMap common) rightSource)
    : TypeConversion env U target
      ((VExpr.forallE A leftView.bodyType).subst (Subst.lift_l leftMap common))
      ((VExpr.forallE C rightView.bodyType).subst (Subst.lift_l rightMap common)) := by
  have sameDomain := leftAnnotation.symm.trans rightAnnotation
  have domains := OriginalFactorCut.realized_between_displays (common := common) sameDomain rfl rfl
  have hA := (leftView.domain.sound.defeq.mono leftBelow).subst henv leftSubs.left hTarget
  have annotationRealized : annotation.subst common = A.subst (Subst.lift_l leftMap common) := by
    rw [leftAnnotation, subst_lift']
  have hAnnotation : env.IsType U target (annotation.subst common) := by
    rw [annotationRealized]; exact ⟨_, hA⟩
  have bodies := LamView.rawBodyPath leftView rightView leftInitial rightInitial
    leftInsertion rightInsertion leftAnnotation rightAnnotation leftExpression rightExpression
    henv leftBelow rightBelow bodyIH closed hTarget leftTail rightTail leftSubs rightSubs hAnnotation
  rw [annotationRealized] at bodies
  change TypeConversion env U target
    (.forallE (A.subst (Subst.lift_l leftMap common))
      (leftView.bodyType.subst (Subst.lift_l leftMap common).lift))
    (.forallE (C.subst (Subst.lift_l rightMap common))
      (rightView.bodyType.subst (Subst.lift_l rightMap common).lift))
  rw [← domains]
  exact TypeConversion.forallSameDomain hA bodies

/-- The two fixed formation F obligations are smaller than the selected
lambda C input. The actual codomain closure captures this side's own domain. -/
theorem LamView.formation_schedule
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.lam A expression) assigned}
    {start : Located root node} (view : LamView start)
    (initial : ContextDerivation sourceEnv U rootSource) (otherCost : Nat) :
    schedule .fundamental (Closure.close view.domain.origin
      (view.location.contextDerivation initial).closures).cost <
        schedule .coherence ((Closure.close node.origin (start.environment initial.closures)).cost + otherCost) ∧
    schedule .fundamental (Closure.close view.codomain.origin
      ((Located.lamCodomain view.location).contextDerivation initial).closures).cost <
        schedule .coherence ((Closure.close node.origin (start.environment initial.closures)).cost + otherCost) := by
  rw [Located.contextDerivation_closures, Located.contextDerivation_closures]
  have domainBound := binder_domain_cost view.domain.origin [view.codomain.origin, view.body.origin] []
    (view.location.environment initial.closures)
  have bodyBound := binder_body_cost (domain := view.domain.origin)
    (bodies := [view.codomain.origin, view.body.origin]) (children := [])
    (body := view.codomain.origin) (by simp) (view.location.environment initial.closures)
  constructor <;> apply schedule_strict
  · exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le domainBound (view.cost_le initial.closures))
      (Nat.le_add_right _ _)
  · exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le bodyBound (view.cost_le initial.closures))
      (Nat.le_add_right _ _)

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
