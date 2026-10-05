import Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalPiPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericDisplay

/-! Source displays for the two actual original children of a native Pi.
The common syntax is retained before target substitution. Entering a row
keeps the actual original domain in the generic frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalRecordSource OriginalTail
set_option backward.isDefEq.respectTransparency false

variable {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
variable {domain : EndpointRef sourceEnv U source A (.sort u)}
variable {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
variable {hu : u.WF U} {hv : v.WF U}

noncomputable def Located.piDisplayAs
    (location : Located root (.pi hu hv (.ref domain) body))
    (initial : ContextDerivation sourceEnv U rootSource)
    (insertion : Ctx.Lift' map source displayed)
    (annotationEq : annotation = A.lift' map)
    (bodyEq : displayedBody = B.lift' map.cons) :
    EndpointDisplay sourceEnv U displayed (.forallE annotation displayedBody) (.sort (.imax u v)) where
  source := source
  sourceExpression := .forallE A B
  sourceType := .sort (.imax u v)
  context := location.contextDerivation initial
  node := .pi hu hv (.ref domain) body
  provenance := .ofLocation location initial
  map := map
  insertion := insertion
  expression_eq := by simp only [lift', ← annotationEq, ← bodyEq]
  type_eq := rfl

noncomputable def Located.piDomainDisplayAs
    (location : Located root (.pi hu hv (.ref domain) body))
    (initial : ContextDerivation sourceEnv U rootSource)
    (insertion : Ctx.Lift' map source displayed)
    (annotationEq : annotation = A.lift' map) :
    EndpointDisplay sourceEnv U displayed annotation (.sort u) where
  source := source
  sourceExpression := A
  sourceType := .sort u
  context := (Located.piDomain location).contextDerivation initial
  node := .ref domain
  provenance := .ofLocation (.piDomain location) initial
  map := map
  insertion := insertion
  expression_eq := annotationEq
  type_eq := rfl

noncomputable def Located.piBodyDisplayAs
    (location : Located root (.pi hu hv (.ref domain) body))
    (initial : ContextDerivation sourceEnv U rootSource)
    (insertion : Ctx.Lift' map source displayed)
    (annotationEq : annotation = A.lift' map)
    (bodyEq : displayedBody = B.lift' map.cons) :
    EndpointDisplay sourceEnv U (annotation :: displayed) displayedBody (.sort v) where
  source := A :: source
  sourceExpression := B
  sourceType := .sort v
  context := (Located.piBody location).contextDerivation initial
  node := body
  provenance := .ofLocation (.piBody location) initial
  map := map.cons
  insertion := by rw [annotationEq]; exact insertion.cons
  expression_eq := bodyEq
  type_eq := rfl

theorem Located.piBody_originalContext
    (location : Located root (.pi hu hv (.ref domain) body))
    (initial : ContextDerivation sourceEnv U rootSource) :
    (Located.piBody location).contextDerivation initial =
      .cons (location.contextDerivation initial) domain := by
  change ContextDerivation.cons (location.contextDerivation initial)
    (Classical.choose location.originalDomains.1) = _
  have equal := Classical.choose_spec location.originalDomains.1
  have same : Classical.choose location.originalDomains.1 = domain := by
    exact (EndpointState.ref.inj equal).symm
  rw [same]

/-- Common source syntax, rather than equal target values, determines the
same ordinary domain/body comparison and the substitution at every anchor. -/
theorem pi_display_realizations
    (leftInsertion : Ctx.Lift' leftMap leftSource displayed)
    (rightInsertion : Ctx.Lift' rightMap rightSource displayed)
    (leftAnnotation : annotation = A.lift' leftMap)
    (rightAnnotation : annotation = C.lift' rightMap)
    (leftBody : displayedBody = B.lift' leftMap.cons)
    (rightBody : displayedBody = D.lift' rightMap.cons)
    (common : Subst) :
    (VExpr.forallE A B).subst (Subst.lift_l leftMap common) =
      (VExpr.forallE C D).subst (Subst.lift_l rightMap common) ∧
    ∀ anchor, B.subst ((Subst.lift_l leftMap common).cons anchor) =
      D.subst ((Subst.lift_l rightMap common).cons anchor) := by
  have sourceEq : (VExpr.forallE A B).lift' leftMap = (VExpr.forallE C D).lift' rightMap := by
    simp only [lift', ← leftAnnotation, ← rightAnnotation, ← leftBody, ← rightBody]
  have realized := congrArg (fun expression => expression.subst common) sourceEq
  simp only [subst_lift'] at realized
  exact ⟨realized, pi_realized_body_eq realized⟩

private def castFrame
    {first second : ContextDerivation sourceEnv U source}
    (contextEq : first = second) (leftEq : σ = σ') (rightEq : τ = τ')
    (frame : OriginalRichFrame sourceEnv env U registry target first locals σ τ available) :
    OriginalRichFrame sourceEnv env U registry target second locals σ' τ' available :=
  contextEq ▸ leftEq ▸ rightEq ▸ frame

private theorem castFrame_environment
    {first second : ContextDerivation sourceEnv U source}
    (contextEq : first = second) (leftEq : σ = σ') (rightEq : τ = τ')
    (frame : OriginalRichFrame sourceEnv env U registry target first locals σ τ available)
    (ordered : sourceEnv.Ordered) :
    (castFrame contextEq leftEq rightEq frame).dependencyEnvironment ordered =
      frame.dependencyEnvironment ordered := by
  cases contextEq
  cases leftEq
  cases rightEq
  rfl

/-- The frame presented to body R has exactly the context and substitution
of the original body display; no reorigining or manufactured typing is used. -/
noncomputable def _root_.Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource.OriginalPiSide.displayBodyFrame
    {context : ContextDerivation sourceEnv U source}
    (henv : env.Ordered)
    (location : Located root (.pi hu hv (.ref domain) body))
    (initial : ContextDerivation sourceEnv U rootSource)
    (lineage : location.contextDerivation initial = context)
    (insertion : Ctx.Lift' map source displayed)
    (annotationEq : annotation = A.lift' map)
    (bodyEq : displayedBody = B.lift' map.cons)
    (side : OriginalPiSide root initial env registry target context domain locals
      (Subst.lift_l map common) available (ambient : Profile n))
    (guard : LambdaGuard env U registry target (Subst.lift_l map common) A (key : Key n) ambient)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms) :
    OriginalRichFrame sourceEnv env U registry target
      (location.piBodyDisplayAs initial insertion annotationEq bodyEq).context (Locals.push locals)
      ((location.piBodyDisplayAs initial insertion annotationEq bodyEq).sourceSubst (common.cons key.anchor))
      ((location.piBodyDisplayAs initial insertion annotationEq bodyEq).sourceSubst (common.cons key.anchor))
      (available.push needs) := by
  change OriginalRichFrame sourceEnv env U registry target
    ((Located.piBody location).contextDerivation initial) (Locals.push locals)
    (Subst.lift_l map.cons (common.cons key.anchor))
    (Subst.lift_l map.cons (common.cons key.anchor)) (available.push needs)
  have realization : Subst.lift_l map.cons (common.cons key.anchor) =
      (Subst.lift_l map common).cons key.anchor := by
    funext index; cases index <;> rfl
  exact castFrame ((location.piBody_originalContext initial).trans
    (congrArg (fun ctx => ContextDerivation.cons ctx domain) lineage)).symm
    realization.symm realization.symm (side.atAnchor henv guard needs bounded covered)

noncomputable def _root_.Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource.OriginalRichDisplayFrame.piDomain
    (location : Located root (.pi hu hv (.ref domain) body))
    (initial : ContextDerivation sourceEnv U rootSource)
    (insertion : Ctx.Lift' map source displayed)
    (annotationEq : annotation = A.lift' map)
    (bodyEq : displayedBody = B.lift' map.cons)
    (frame : OriginalRichDisplayFrame env registry target
      (location.piDisplayAs initial insertion annotationEq bodyEq) common locals available) :
    OriginalRichDisplayFrame env registry target
      (location.piDomainDisplayAs initial insertion annotationEq) common locals available :=
  ⟨frame.frame, frame.substitutions⟩

noncomputable def _root_.Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource.OriginalPiSide.displayBodyFits
    {context : ContextDerivation sourceEnv U source}
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (location : Located root (.pi hu hv (.ref domain) body))
    (initial : ContextDerivation sourceEnv U rootSource)
    (lineage : location.contextDerivation initial = context)
    (insertion : Ctx.Lift' map source displayed)
    (annotationEq : annotation = A.lift' map)
    (bodyEq : displayedBody = B.lift' map.cons)
    (side : OriginalPiSide root initial env registry target context domain locals
      (Subst.lift_l map common) available (ambient : Profile n))
    (substitutions : Ctx.SubstEq env U target (Subst.lift_l map common)
      (Subst.lift_l map common) source)
    (guard : LambdaGuard env U registry target (Subst.lift_l map common) A (key : Key n) ambient)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms) :
    OriginalRichDisplayFrame env registry target
      (location.piBodyDisplayAs initial insertion annotationEq bodyEq) (common.cons key.anchor)
      (Locals.push locals) (available.push needs) where
  frame := side.displayBodyFrame henv location initial lineage insertion annotationEq bodyEq guard needs bounded covered
  substitutions := by
    change Ctx.SubstEq env U target (Subst.lift_l map.cons (common.cons key.anchor))
      (Subst.lift_l map.cons (common.cons key.anchor)) (A :: source)
    have realization : Subst.lift_l map.cons (common.cons key.anchor) =
        (Subst.lift_l map common).cons key.anchor := by
      funext index; cases index <;> rfl
    rw [realization]
    exact .cons substitutions (domain.sound.defeq.mono below) (guard.path.cast guard.anchor.1)

theorem _root_.Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource.OriginalPiSide.displayBodyFrame_environment
    {context : ContextDerivation sourceEnv U source}
    (henv : env.Ordered) (ordered : sourceEnv.Ordered)
    (location : Located root (.pi hu hv (.ref domain) body))
    (initial : ContextDerivation sourceEnv U rootSource)
    (lineage : location.contextDerivation initial = context)
    (insertion : Ctx.Lift' map source displayed)
    (annotationEq : annotation = A.lift' map)
    (bodyEq : displayedBody = B.lift' map.cons)
    (side : OriginalPiSide root initial env registry target context domain locals
      (Subst.lift_l map common) available (ambient : Profile n))
    (guard : LambdaGuard env U registry target (Subst.lift_l map common) A (key : Key n) ambient)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms) :
    (side.displayBodyFrame henv location initial lineage insertion annotationEq bodyEq guard needs bounded covered).dependencyEnvironment ordered =
      (side.atAnchor henv guard needs bounded covered).dependencyEnvironment ordered := by
  unfold OriginalPiSide.displayBodyFrame
  apply castFrame_environment

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
