import Lean4Lean.Theory.Typing.AnchoredOriginalDisplay
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionCaptureBudget

/-! A finite original endpoint display with one actual captured argument.
No endpoint for the substituted term is constructed. Original template,
argument, domain, and formation spines remain separate witnesses. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

structure CapturedEndpointDisplay (env : VEnv) (U : Nat)
    (displayedContext : List VExpr) (expression assigned : VExpr) where
  source : List VExpr
  domainExpression : VExpr
  domainLevel : VLevel
  argumentExpression : VExpr
  templateExpression : VExpr
  templateType : VExpr
  context : ContextDerivation env U source
  domain : EndpointRef env U source domainExpression (.sort domainLevel)
  argument : EndpointRef env U source argumentExpression domainExpression
  node : EndpointState env U (domainExpression :: source) templateExpression templateType
  provenance : EndpointProvenance (.cons context domain) node
  map : Lift
  insertion : Ctx.Lift' map source displayedContext
  expression_eq : expression = (templateExpression.inst argumentExpression).lift' map
  type_eq : assigned = (templateType.inst argumentExpression).lift' map

def CapturedEndpointDisplay.environment (display : CapturedEndpointDisplay env U Γ e A) : List Closure :=
  .bundle (.close display.argument.origin display.context.closures)
    (.close display.domain.origin display.context.closures) :: display.context.closures

def CapturedEndpointDisplay.closure (display : CapturedEndpointDisplay env U Γ e A) : Closure :=
  .close display.node.origin display.environment

def CapturedEndpointDisplay.cost (display : CapturedEndpointDisplay env U Γ e A) : Nat := display.closure.cost

/-- The only raw source substitution is justified by the actual original
argument endpoint. Its conclusion is never reified as an original endpoint. -/
theorem CapturedEndpointDisplay.sound (henv : env.Ordered)
    (display : CapturedEndpointDisplay env U Γ e A) : env.HasType U Γ e A := by
  have instantiated := IsDefEq.instDF henv display.context.forget.defeq display.node.sound.defeq display.argument.sound.defeq
  simpa only [HasType, ← display.expression_eq, ← display.type_eq] using
    instantiated.weak' henv display.insertion

def CapturedEndpointDisplay.one {source : List VExpr}
    (context : ContextDerivation env U source)
    (domain : EndpointRef env U source A (.sort u))
    (argument : EndpointRef env U source a A)
    (node : EndpointState env U (A :: source) e B)
    (provenance : EndpointProvenance (.cons context domain) node) :
    CapturedEndpointDisplay env U source (e.inst a) (B.inst a) :=
  ⟨source, A, u, a, e, B, context, domain, argument, node, provenance,
    .refl, .refl, by simp, by simp⟩

def CapturedEndpointDisplay.weaken (display : CapturedEndpointDisplay env U Γ e A)
    (insertion : Ctx.Lift' ρ Γ Δ) :
    CapturedEndpointDisplay env U Δ (e.lift' ρ) (A.lift' ρ) :=
  { display with
    map := .comp display.map ρ
    insertion := display.insertion.comp insertion
    expression_eq := by simpa only [lift'_comp] using congrArg (·.lift' ρ) display.expression_eq
    type_eq := by simpa only [lift'_comp] using congrArg (·.lift' ρ) display.type_eq }

theorem CapturedEndpointDisplay.weaken_cost
    (display : CapturedEndpointDisplay env U Γ e A) (insertion : Ctx.Lift' ρ Γ Δ) :
    (display.weaken insertion).cost = display.cost := rfl

def CapturedEndpointDisplay.baseSubst
    (display : CapturedEndpointDisplay env U Γ e A) (common : Subst) : Subst :=
  Subst.lift_l display.map common

def CapturedEndpointDisplay.sourceSubst
    (display : CapturedEndpointDisplay env U Γ e A) (common : Subst) : Subst :=
  (display.baseSubst common).cons (display.argumentExpression.subst (display.baseSubst common))

theorem CapturedEndpointDisplay.realizedExpression
    (display : CapturedEndpointDisplay env U Γ e A) (common : Subst) :
    display.templateExpression.subst (display.sourceSubst common) = e.subst common := by
  have eq := congrArg (fun e => e.subst common) display.expression_eq
  simpa only [subst_lift', subst_inst, inst_lift_cons, sourceSubst, baseSubst] using eq.symm

theorem CapturedEndpointDisplay.realizedType
    (display : CapturedEndpointDisplay env U Γ e A) (common : Subst) :
    display.templateType.subst (display.sourceSubst common) = A.subst common := by
  have eq := congrArg (fun e => e.subst common) display.type_eq
  simpa only [subst_lift', subst_inst, inst_lift_cons, sourceSubst, baseSubst] using eq.symm

/-- The displayed ordinary and captured endpoints can have exactly the same
raw expression while retaining distinct original nodes and source types. -/
inductive OriginalClosureDisplay (env : VEnv) (U : Nat)
    (context : List VExpr) (expression assigned : VExpr) where
  | ordinary (display : EndpointDisplay env U context expression assigned)
  | captured (display : CapturedEndpointDisplay env U context expression assigned)

def OriginalClosureDisplay.cost : OriginalClosureDisplay env U Γ e A → Nat
  | .ordinary display => display.cost
  | .captured display => display.cost

def OriginalClosureDisplay.source : OriginalClosureDisplay env U Γ e A → List VExpr
  | .ordinary display => display.source
  | .captured display => display.domainExpression :: display.source

def OriginalClosureDisplay.sourceExpression : OriginalClosureDisplay env U Γ e A → VExpr
  | .ordinary display => display.sourceExpression
  | .captured display => display.templateExpression

def OriginalClosureDisplay.sourceType : OriginalClosureDisplay env U Γ e A → VExpr
  | .ordinary display => display.sourceType
  | .captured display => display.templateType

def OriginalClosureDisplay.context (display : OriginalClosureDisplay env U Γ e A) :
    ContextDerivation env U display.source :=
  match display with
  | .ordinary display => display.context
  | .captured display => .cons display.context display.domain

def OriginalClosureDisplay.node (display : OriginalClosureDisplay env U Γ e A) :
    EndpointState env U display.source display.sourceExpression display.sourceType :=
  match display with
  | .ordinary display => display.node
  | .captured display => display.node

def OriginalClosureDisplay.provenance (display : OriginalClosureDisplay env U Γ e A) :
    EndpointProvenance display.context display.node :=
  match display with
  | .ordinary display => display.provenance
  | .captured display => display.provenance

def OriginalClosureDisplay.sourceSubst (display : OriginalClosureDisplay env U Γ e A)
    (common : Subst) : Subst :=
  match display with
  | .ordinary display => Subst.lift_l display.map common
  | .captured display => display.sourceSubst common

/-- This environment records actual values in addition to original source
formations. It intentionally differs from `context.closures` for a capture. -/
def OriginalClosureDisplay.environment : OriginalClosureDisplay env U Γ e A → List Closure
  | .ordinary display => display.context.closures
  | .captured display => display.environment

theorem OriginalClosureDisplay.cost_eq (display : OriginalClosureDisplay env U Γ e A) :
    display.cost = (Closure.close display.node.origin display.environment).cost := by
  cases display <;> rfl

theorem OriginalClosureDisplay.realizedExpression
    (display : OriginalClosureDisplay env U Γ e A) (common : Subst) :
    display.sourceExpression.subst (display.sourceSubst common) = e.subst common := by
  cases display with
  | ordinary display =>
    have eq := congrArg (fun e => e.subst common) display.expression_eq
    simpa only [subst_lift', sourceExpression, sourceSubst] using eq.symm
  | captured display => exact display.realizedExpression common

theorem OriginalClosureDisplay.realizedType
    (display : OriginalClosureDisplay env U Γ e A) (common : Subst) :
    display.sourceType.subst (display.sourceSubst common) = A.subst common := by
  cases display with
  | ordinary display =>
    have eq := congrArg (fun e => e.subst common) display.type_eq
    simpa only [subst_lift', sourceType, sourceSubst] using eq.symm
  | captured display => exact display.realizedType common

/-- At an original application, the actual result and captured original
codomain fit the proposed reserve. Both displays are constructed here; no
caller supplies a numerical bound or a synthesized endpoint. -/
theorem captured_application_display_schedule
    (context : ContextDerivation env U source)
    (domain : EndpointRef env U source A (.sort u))
    (codomain : EndpointRef env U (A :: source) B (.sort v))
    (function : EndpointRef env U source f (.forallE A B))
    (argument : EndpointRef env U source a A)
    (result : EndpointRef env U source (B.inst a) (.sort v)) :
    let left := EndpointDisplay.identity context (.ref result) (.ofLocation .here context)
    let right := CapturedEndpointDisplay.one context domain argument (.ref codomain)
      (.ofLocation .here (.cons context domain))
    schedule .coherence (left.cost + right.cost) <
      schedule .fundamental (Closure.close
        (capturedApplicationOrigin domain.origin codomain.origin function.origin argument.origin result.origin)
        context.closures).cost := by
  apply schedule_strict
  exact capturedApplication_comparison domain.origin codomain.origin function.origin argument.origin
    result.origin context.closures

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
