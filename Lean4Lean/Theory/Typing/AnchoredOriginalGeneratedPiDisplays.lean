import Lean4Lean.Theory.Typing.AnchoredOriginalScopedCaptureRealization
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiDisplays

/-! Native Pi displays after recursive original captures. The common binder
context is raw syntax; each side retains its own original domain and frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private LambdaGuard.anchorRelated from Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiReindex
set_option backward.isDefEq.respectTransparency false

structure OriginalGeneratedDisplayFrame
    (base : OriginalCaptureBase env U registry target)
    (display : OriginalNestedDisplay U common expression assigned)
    (realization : Subst) (locals : List Nat) (available : Valuation) where
  capture : OriginalCaptureRealization display.graph env registry target locals realization realization available
  generated : ScopedCaptureGenerated base realization realization display.graph capture.frame.raw

noncomputable def OriginalGeneratedDisplayFrame.cost
    {display : OriginalNestedDisplay U common expression assigned}
    (frame : OriginalGeneratedDisplayFrame base display realization locals available)
    (ordered : display.sourceEnv.Ordered) : Nat :=
  (Closure.close (display.node.dependencyOrigin ordered)
    (frame.capture.frame.dependencyEnvironment ordered)).cost

/-- A local recursive answer at actual generated frames. Both endpoints
retain the same raw displayed expression before target substitution. -/
def OriginalGeneratedDisplayReindex
    {base : OriginalCaptureBase env U registry target}
    {left : OriginalNestedDisplay U common expression leftAssigned}
    {right : OriginalNestedDisplay U common expression rightAssigned}
    (_leftFrame : OriginalGeneratedDisplayFrame base left realization leftLocals leftAvailable)
    (_rightFrame : OriginalGeneratedDisplayFrame base right realization rightLocals rightAvailable) : Prop :=
  ∀ {leftLevel rightLevel : VLevel}
    (leftSort : left.sourceType = .sort leftLevel) (rightSort : right.sourceType = .sort rightLevel),
    RichCodeTransfer env U registry target (left.node.cast rfl leftSort) (right.node.cast rfl rightSort)
      leftLocals rightLocals (left.raw.comp realization) (right.raw.comp realization)
      leftAvailable rightAvailable

section
variable {sourceEnv : VEnv} {source : List VExpr} {raw : Subst}
  {base : OriginalCaptureBase env U registry target}
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  {domain : EndpointRef sourceEnv U source A (.sort u)}
  {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
  {hu : u.WF U} {hv : v.WF U}
  (location : Located root (.pi hu hv (.ref domain) body))
  (initial : ContextDerivation sourceEnv U rootSource)
  (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
  (annotationEq : annotation = A.subst raw)
  (bodyEq : displayedBody = B.subst raw.lift)

noncomputable def OriginalNestedDisplay.pi :
    OriginalNestedDisplay U common (.forallE annotation displayedBody) (.sort (.imax u v)) where
  sourceEnv := sourceEnv
  source := source
  sourceExpression := .forallE A B
  sourceType := .sort (.imax u v)
  context := location.contextDerivation initial
  node := .pi hu hv (.ref domain) body
  provenance := .ofLocation location initial
  raw := raw
  graph := graph
  expression_eq := by simp only [subst, ← annotationEq, ← bodyEq]
  type_eq := rfl

noncomputable def OriginalNestedDisplay.piDomain :
    OriginalNestedDisplay U common annotation (.sort u) where
  sourceEnv := sourceEnv
  source := source
  sourceExpression := A
  sourceType := .sort u
  context := location.contextDerivation initial
  node := .ref domain
  provenance := .ofLocation (.piDomain location) initial
  raw := raw
  graph := graph
  expression_eq := annotationEq
  type_eq := rfl

noncomputable def OriginalNestedDisplay.piBody :
    OriginalNestedDisplay U (annotation :: common) displayedBody (.sort v) where
  sourceEnv := sourceEnv
  source := A :: source
  sourceExpression := B
  sourceType := .sort v
  context := .cons (location.contextDerivation initial) domain
  node := body
  provenance := {
    rootSource := rootSource
    rootExpression := rootExpression
    rootType := rootType
    root := root
    initial := initial
    location := .piBody location
    context_eq := (location.piBody_originalContext initial).symm }
  raw := raw.lift
  graph := .bind graph domain annotation annotationEq.symm
  expression_eq := bodyEq
  type_eq := rfl

noncomputable def OriginalGeneratedDisplayFrame.piDomain
    (frame : OriginalGeneratedDisplayFrame base
      (OriginalNestedDisplay.pi location initial graph annotationEq bodyEq) realization locals available) :
    OriginalGeneratedDisplayFrame base
      (OriginalNestedDisplay.piDomain location initial graph annotationEq) realization locals available :=
  ⟨frame.capture, frame.generated⟩

private theorem generatedBody
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (frame : OriginalGeneratedDisplayFrame base
      (OriginalNestedDisplay.pi location initial graph annotationEq bodyEq) realization locals available)
    (code : RichCert sourceEnv env U registry target (.ref domain) locals (raw.comp realization)
      true (ambient : Profile n) footprint)
    (resources : footprint.Available available)
    (guard : LambdaGuard env U registry target (raw.comp realization) A (key : Key n) ambient)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms) :
    ∃ next : OriginalGeneratedDisplayFrame base
        (OriginalNestedDisplay.piBody location initial graph annotationEq bodyEq)
        (realization.cons key.anchor) (Locals.push locals) (available.push needs),
      ∀ ordered : sourceEnv.Ordered,
        next.capture.frame.dependencyEnvironment ordered =
          .close (domain.dependencyOrigin ordered) (frame.capture.frame.dependencyEnvironment ordered) ::
            frame.capture.frame.dependencyEnvironment ordered := by
  obtain ⟨next, generated, environment⟩ := frame.capture.bindGenerated frame.generated domain
    annotation annotationEq.symm below code resources guard.inputTyped
    (LambdaGuard.anchorRelated henv guard) (guard.path.cast guard.anchor.1) needs bounded covered
  exact ⟨⟨next, generated⟩, environment⟩

noncomputable def OriginalGeneratedDisplayFrame.piBody
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (frame : OriginalGeneratedDisplayFrame base
      (OriginalNestedDisplay.pi location initial graph annotationEq bodyEq) realization locals available)
    (code : RichCert sourceEnv env U registry target (.ref domain) locals (raw.comp realization)
      true (ambient : Profile n) footprint)
    (resources : footprint.Available available)
    (guard : LambdaGuard env U registry target (raw.comp realization) A (key : Key n) ambient)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms) :
    OriginalGeneratedDisplayFrame base
      (OriginalNestedDisplay.piBody location initial graph annotationEq bodyEq)
      (realization.cons key.anchor) (Locals.push locals) (available.push needs) :=
  Classical.choose (generatedBody location initial graph annotationEq bodyEq henv below frame
    code resources guard needs bounded covered)

theorem OriginalGeneratedDisplayFrame.piBody_environment
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (frame : OriginalGeneratedDisplayFrame base
      (OriginalNestedDisplay.pi location initial graph annotationEq bodyEq) realization locals available)
    (code : RichCert sourceEnv env U registry target (.ref domain) locals (raw.comp realization)
      true (ambient : Profile n) footprint)
    (resources : footprint.Available available)
    (guard : LambdaGuard env U registry target (raw.comp realization) A (key : Key n) ambient)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms)
    (ordered : sourceEnv.Ordered) :
    (frame.piBody location initial graph annotationEq bodyEq henv below code resources guard
      needs bounded covered).capture.frame.dependencyEnvironment ordered =
      .close (domain.dependencyOrigin ordered) (frame.capture.frame.dependencyEnvironment ordered) ::
        frame.capture.frame.dependencyEnvironment ordered :=
  Classical.choose_spec (generatedBody location initial graph annotationEq bodyEq henv below frame
    code resources guard needs bounded covered) ordered
end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
