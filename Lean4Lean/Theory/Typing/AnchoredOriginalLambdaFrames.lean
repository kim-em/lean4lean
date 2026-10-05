import Lean4Lean.Theory.Typing.AnchoredOriginalLambdaWrappers
import Lean4Lean.Theory.Typing.AnchoredOriginalCoherenceContract
import Lean4Lean.Theory.Typing.AnchoredOriginalTailFuture

/-! Concrete binder frames for the fixed original lambda body pair.
Reorigin changes current syntax provenance along the same raw source context;
no unrestricted Fits producer is promoted to a TailFits producer. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def LamView.pushDisplayFits
    {n : Nat} {ambient : Profile n} {key : Key n} {commonAvailable : Valuation}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.lam A expression) assigned}
    {start : Located root node} (view : LamView start)
    (initial : ContextDerivation sourceEnv U rootSource)
    (insertion : Ctx.Lift' map source displayed)
    (annotation_eq : annotation = A.lift' map)
    (expression_eq : displayedBody = expression.lift' map.cons)
    (henv : env.Ordered) (hle : sourceEnv ≤ env)
    (tail : TailFits sourceEnv env U registry target source locals
      (Subst.lift_l map common) (Subst.lift_l map common)
      (fun index => commonAvailable (map.liftVar index)))
    (substitutions : Ctx.SubstEq env U target
      (Subst.lift_l map common) (Subst.lift_l map common) source)
    (domain : CodeCert env U registry target locals (Subst.lift_l map common) A ambient domainFootprint)
    (resources : domainFootprint.Available (fun index => commonAvailable (map.liftVar index)))
    (guard : LambdaGuard env U registry target (Subst.lift_l map common) A key ambient)
    (needs : List Need)
    (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms,
      atom ∈ (key.input : Profile n).atoms) :
    DisplayFits env registry target
      (view.bodyDisplayAs initial insertion annotation_eq expression_eq)
      (common.cons key.anchor) (Valuation.push needs commonAvailable) (Locals.push locals) := by
  have raw := guard.anchor.1
  have arguments : Related env U registry target key.anchor key.anchor
      (A.subst (Subst.lift_l map common)) key.input ambient := by
    obtain ⟨_, _, _, _, _, _, _, anchor⟩ := guard.anchor
    exact Related.convert henv guard.inputTyped guard.domains anchor
  let extended := tail.push (Classical.choose view.location.originalDomains.1)
    domain resources guard.inputTyped arguments needs bounded covered
  have realization : Subst.lift_l map.cons (common.cons key.anchor) =
      (Subst.lift_l map common).cons key.anchor := by
    funext index; cases index <;> rfl
  have valuation : (fun index => Valuation.push needs commonAvailable (map.cons.liftVar index)) =
      Valuation.push needs (fun index => commonAvailable (map.liftVar index)) := by
    funext index; cases index <;> rfl
  let packed : TailFits sourceEnv env U registry target (A :: source) (Locals.push locals)
      (Subst.lift_l map.cons (common.cons key.anchor))
      (Subst.lift_l map.cons (common.cons key.anchor))
      (fun index => Valuation.push needs commonAvailable (map.cons.liftVar index)) := by
    rw [realization, valuation]
    exact extended
  refine { fits := packed.reorigin ((Located.lamBody view.location).contextDerivation initial)
           original := packed.reorigin_contextDerivation _
           substitutions := ?_ }
  change Ctx.SubstEq env U target
      (Subst.lift_l map.cons (common.cons key.anchor))
      (Subst.lift_l map.cons (common.cons key.anchor)) (A :: source)
  rw [realization]
  exact .cons substitutions (view.domain.sound.defeq.mono hle) (guard.path.cast raw)

private def codeProfile {profile : Profile n}
    (_ : CodeCert env U registry target locals σ expression profile footprint) : Profile n := profile

private def codeFootprint {footprint : Footprint}
    (_ : CodeCert env U registry target locals σ expression profile footprint) : Footprint := footprint

private theorem lift_l_cons (map : Lift) (common : Subst) (anchor : VExpr) :
    Subst.lift_l map.cons (common.cons anchor) = (Subst.lift_l map common).cons anchor := by
  funext index; cases index <;> rfl

private theorem valuation_cons (map : Lift) (available : Valuation) (needs : List Need) :
    (fun index => Valuation.push needs available (map.cons.liftVar index)) =
      Valuation.push needs (fun index => available (map.liftVar index)) := by
  funext index; cases index <;> rfl

/-- Construct the finite reply tree by calling only the fixed original body
pair IH. Each call receives the actual source-tail frames at the stored anchor. -/
theorem LamView.rowAnswers
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
    {n : Nat} {ambient : Profile n} {table : List (Key n × Profile n)}
    (domain : CodeCert env U registry target leftLocals (Subst.lift_l leftMap common)
      A ambient domainFootprint)
    (rows : PiRows env U registry target leftLocals (Subst.lift_l leftMap common)
      A leftView.bodyType ambient table rowFootprint)
    (domainResources : domainFootprint.Available (fun index => commonAvailable (leftMap.liftVar index)))
    (resources : rowFootprint.Available (fun index => commonAvailable (leftMap.liftVar index))) :
    Nonempty (LambdaRowAnswers env U registry target leftLocals rightLocals
      (Subst.lift_l leftMap common) (Subst.lift_l rightMap common)
      (fun index => commonAvailable (rightMap.liftVar index)) A leftView.bodyType rightView.bodyType rows) := by
  have sameDomain := leftAnnotation.symm.trans rightAnnotation
  have domains := OriginalFactorCut.realized_between_displays (common := common) sameDomain rfl rfl
  obtain ⟨rightFootprint, ⟨rightDomain⟩, rightResources⟩ :=
    OriginalFactorCut.CodeCert.betweenDisplays domain leftMap rightMap common rfl rfl sameDomain
      [] rightLocals domainResources (fun _ => rfl) (fun _ => rfl)
  match rows with
  | .nil => exact ⟨.nil⟩
  | .cons guard body pack covered tail =>
    let bodyFootprint := codeFootprint body
    let needs := bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons
    have bounded := fun need member => (pack.atomized_localNeeds need member).1
    have coverage := fun need member atom present => covered atom
      ((pack.atomized_localNeeds need member).2 atom present)
    have rightGuard : LambdaGuard env U registry target (Subst.lift_l rightMap common)
        C _ ambient := {
      inputTyped := guard.inputTyped, formed := guard.formed,
      path := by rw [← domains]; exact guard.path,
      domains := by rw [← domains]; exact guard.domains,
      anchor := guard.anchor }
    let leftFrame := leftView.pushDisplayFits leftInitial leftInsertion leftAnnotation leftExpression
      henv leftBelow leftTail leftSubs domain domainResources guard needs bounded coverage
    let rightFrame := rightView.pushDisplayFits rightInitial rightInsertion rightAnnotation rightExpression
      henv rightBelow rightTail rightSubs rightDomain rightResources rightGuard needs bounded coverage
    have answer := bodyIH target (common.cons _) (Valuation.push needs commonAvailable)
      (Locals.push leftLocals) (Locals.push rightLocals)
      (Valuation.push_atomized_closed closed bodyFootprint.localNeeds) hTarget leftFrame rightFrame
    have leftValuation :
        (leftView.bodyDisplayAs leftInitial leftInsertion leftAnnotation leftExpression).sourceValuation
          (Valuation.push needs commonAvailable) =
        Valuation.push needs (fun index => commonAvailable (leftMap.liftVar index)) := by
      funext index; cases index <;> rfl
    have rightValuation :
        (rightView.bodyDisplayAs rightInitial rightInsertion rightAnnotation rightExpression).sourceValuation
          (Valuation.push needs commonAvailable) =
        Valuation.push needs (fun index => commonAvailable (rightMap.liftVar index)) := by
      funext index; cases index <;> rfl
    have request := answer.queries (profile := codeProfile body) (footprint := bodyFootprint)
    rw [leftValuation, rightValuation] at request
    dsimp only [EndpointDisplay.sourceSubst, EndpointDisplay.sourceValuation,
      LamView.bodyDisplayAs] at request
    simp only [lift_l_cons] at request
    obtain ⟨returned⟩ := request body (pack.available_atomized_localNeeds
      (fun i need member => resources i need (List.mem_append_left _ member)))
    obtain ⟨rest⟩ := LamView.rowAnswers leftView rightView leftInitial rightInitial
      leftInsertion rightInsertion leftAnnotation rightAnnotation leftExpression rightExpression
      henv leftBelow rightBelow bodyIH closed hTarget leftTail rightTail leftSubs rightSubs
      domain tail domainResources (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨.cons returned rest⟩
termination_by sizeOf rows

private theorem empty_guard
    (typed : env.HasType U target anchor (A.subst σ)) :
    LambdaGuard env U registry target σ A
      ⟨A.subst σ, anchor, (.empty : Profile 0)⟩ (.empty : Profile 0) := by
  have code : TypeRelated env U registry target (A.subst σ) (A.subst σ) (.empty : Profile 0) :=
    fun _ _ _ _ member => nomatch member
  have relation : Related env U registry target anchor anchor (A.subst σ)
      (.empty : Profile 0) (.empty : Profile 0) := fun _ member => nomatch member
  exact ⟨Profile.HasType.empty Profile.WF.empty,
    Profile.HasType.empty (Profile.HasType.sort true).wf_value, .refl, code,
    typed, typed, .empty, Profile.HasType.empty Profile.WF.empty,
    Profile.HasType.empty (Profile.HasType.sort true).wf_value, code, relation, relation⟩

/-- The raw body call has a fresh neutral target variable and an empty
semantic head ledger. Its original source domain is still retained exactly. -/
noncomputable def LamView.neutralDisplayFits
    {commonAvailable : Valuation}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.lam A expression) assigned}
    {start : Located root node} (view : LamView start)
    (initial : ContextDerivation sourceEnv U rootSource)
    (insertion : Ctx.Lift' map source displayed)
    (annotation_eq : annotation = A.lift' map)
    (expression_eq : displayedBody = expression.lift' map.cons)
    (henv : env.Ordered) (hle : sourceEnv ≤ env)
    (hTarget : OnCtx target (env.IsType U))
    (hAnnotation : env.IsType U target (annotation.subst common))
    (tail : TailFits sourceEnv env U registry target source locals
      (Subst.lift_l map common) (Subst.lift_l map common)
      (fun index => commonAvailable (map.liftVar index)))
    (substitutions : Ctx.SubstEq env U target
      (Subst.lift_l map common) (Subst.lift_l map common) source) :
    DisplayFits env registry (annotation.subst common :: target)
      (view.bodyDisplayAs initial insertion annotation_eq expression_eq)
      common.lift (Valuation.push [] (commonAvailable.rename (.skip .refl))) (Locals.push locals) := by
  let future : FutureInsertion env U target (annotation.subst common :: target) (.skip .refl) :=
    .skip (.refl hTarget) (Classical.choose_spec hAnnotation)
  have annotationRealized : A.subst (Subst.lift_l map common) = annotation.subst common := by
    rw [annotation_eq, subst_lift']
  have domainEq : A.subst (Subst.lift_l map (common.lift_r (.skip .refl))) =
      (annotation.subst common).lift := by
    change A.subst ((Subst.lift_l map common).lift_r (.skip .refl)) = _
    rw [← lift'_subst, annotationRealized, ← lift_eq_lift']
  have typedNeutral : env.HasType U (annotation.subst common :: target) (.bvar 0)
      (A.subst (Subst.lift_l map (common.lift_r (.skip .refl)))) := by
    rw [domainEq]
    exact .bvar .zero
  let domain : CodeCert env U registry (annotation.subst common :: target) locals
      (Subst.lift_l map (common.lift_r (.skip .refl))) A (.empty : Profile 0) [] :=
    .seed .empty (Profile.HasType.empty (Profile.HasType.sort true).wf_value)
  have commonLift : common.lift = (common.lift_r (.skip .refl)).cons (.bvar 0) := by
    funext index; cases index <;> simp only [Subst.lift, Subst.cons, Subst.lift_r, lift_eq_lift']
  rw [commonLift]
  exact view.pushDisplayFits initial insertion annotation_eq expression_eq henv hle
    (tail.future henv future) (substitutions.future henv future) domain
    (fun _ _ member => nomatch member) (empty_guard typedNeutral) []
    (fun _ member => nomatch member) (fun _ member => nomatch member)

/-- Raw body conversion comes from the same fixed original pair at a fresh
neutral target binder; it is independent of every finite incoming query. -/
theorem LamView.rawBodyPath
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
    (hAnnotation : env.IsType U target (annotation.subst common)) :
    TypeConversion env U (annotation.subst common :: target)
      (leftView.bodyType.subst (Subst.lift_l leftMap common).lift)
      (rightView.bodyType.subst (Subst.lift_l rightMap common).lift) := by
  let leftFrame := leftView.neutralDisplayFits leftInitial leftInsertion leftAnnotation leftExpression
    henv leftBelow hTarget hAnnotation leftTail leftSubs
  let rightFrame := rightView.neutralDisplayFits rightInitial rightInsertion rightAnnotation rightExpression
    henv rightBelow hTarget hAnnotation rightTail rightSubs
  have shiftedClosed : (Valuation.push [] (commonAvailable.rename (.skip .refl))).AtomClosed := by
    simpa only [List.nil_append, List.flatMap_nil] using
      Valuation.push_atomized_closed (closed.rename (.skip .refl)) []
  have answer := bodyIH (annotation.subst common :: target) common.lift
    (Valuation.push [] (commonAvailable.rename (.skip .refl)))
    (Locals.push leftLocals) (Locals.push rightLocals) shiftedClosed
    ⟨hTarget, hAnnotation⟩ leftFrame rightFrame
  simpa only [subst_lift', ← Subst.lift_l_lift] using answer.path

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
