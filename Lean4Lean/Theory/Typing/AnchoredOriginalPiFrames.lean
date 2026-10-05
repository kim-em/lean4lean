import Lean4Lean.Theory.Typing.AnchoredOriginalLambdaFrames
import Lean4Lean.Theory.Typing.AnchoredOriginalPiLevels

/-! Original Pi child displays and fresh-neutral frames preserve each source
endpoint's own captured domain formation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def PiView.bodyDisplay
    {root : EndpointRef env U rootSource rootExpression rootType}
    {node : EndpointState env U source (.forallE A expression) assigned}
    {start : Located root node} (view : PiView start)
    (initial : ContextDerivation env U rootSource)
    (insertion : Ctx.Lift' map source displayed) :
    EndpointDisplay env U (A.lift' map :: displayed)
      (expression.lift' map.cons) ((VExpr.sort view.bodyLevel).lift' map.cons) where
  source := A :: source
  sourceExpression := expression
  sourceType := (VExpr.sort view.bodyLevel)
  context := (Located.piBody view.location).contextDerivation initial
  node := view.body
  provenance := .ofLocation (.piBody view.location) initial
  map := map.cons
  insertion := insertion.cons
  expression_eq := rfl
  type_eq := rfl

/-- Exact common syntax is a display equality, never a replacement of the
original body or of the domain proof stored in its captured source context. -/
noncomputable def PiView.bodyDisplayAs
    {root : EndpointRef env U rootSource rootExpression rootType}
    {node : EndpointState env U source (.forallE A expression) assigned}
    {start : Located root node} (view : PiView start)
    (initial : ContextDerivation env U rootSource)
    (insertion : Ctx.Lift' map source displayed)
    (annotation_eq : annotation = A.lift' map)
    (expression_eq : displayedBody = expression.lift' map.cons) :
    EndpointDisplay env U (annotation :: displayed)
      displayedBody ((VExpr.sort view.bodyLevel).lift' map.cons) where
  source := A :: source
  sourceExpression := expression
  sourceType := (VExpr.sort view.bodyLevel)
  context := (Located.piBody view.location).contextDerivation initial
  node := view.body
  provenance := .ofLocation (.piBody view.location) initial
  map := map.cons
  insertion := by rw [annotation_eq]; exact insertion.cons
  expression_eq := expression_eq
  type_eq := rfl

noncomputable def PiView.pushDisplayFits
    {n : Nat} {ambient : Profile n} {key : Key n} {commonAvailable : Valuation}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A expression) assigned}
    {start : Located root node} (view : PiView start)
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
  refine { fits := packed.reorigin ((Located.piBody view.location).contextDerivation initial)
           original := packed.reorigin_contextDerivation _
           substitutions := ?_ }
  change Ctx.SubstEq env U target
      (Subst.lift_l map.cons (common.cons key.anchor))
      (Subst.lift_l map.cons (common.cons key.anchor)) (A :: source)
  rw [realization]
  exact .cons substitutions (view.domain.sound.defeq.mono hle) (guard.path.cast raw)

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
noncomputable def PiView.neutralDisplayFits
    {commonAvailable : Valuation}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A expression) assigned}
    {start : Located root node} (view : PiView start)
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


end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
