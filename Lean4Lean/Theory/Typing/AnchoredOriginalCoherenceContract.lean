import Lean4Lean.Theory.Typing.AnchoredOriginalDisplay
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedFundamental

/-! The two-original-endpoint coherence obligation. Source weakening is
delayed in each endpoint display, and each fitted context must retain that
endpoint's exact original formation spine. Raw type conversion is required
independently of finite queries. These are internal induction contracts;
this file does not assert the general coherence theorem. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

def EndpointDisplay.sourceSubst (display : EndpointDisplay sourceEnv U Γ e A)
    (common : Subst) : Subst := Subst.lift_l display.map common

def EndpointDisplay.sourceValuation (display : EndpointDisplay sourceEnv U Γ e A)
    (common : Valuation) : Valuation := fun index => common (display.map.liftVar index)

theorem EndpointDisplay.sourceValuation_closed
    (display : EndpointDisplay sourceEnv U Γ e A)
    (closed : common.AtomClosed) : (display.sourceValuation common).AtomClosed := by
  intro index need member atom present
  exact closed (display.map.liftVar index) need member atom present

theorem EndpointDisplay.realizedType
    (display : EndpointDisplay sourceEnv U Γ e A) (common : Subst) :
    display.sourceType.subst (display.sourceSubst common) = A.subst common := by
  have equal := congrArg (fun expression => expression.subst common) display.type_eq
  simpa only [subst_lift', sourceSubst] using equal.symm

/-- The semantic entries and the original captured source spine are paired
at the same source tail. Equality of the raw context list alone is insufficient
to identify the source-closure cost used by recursive calls. -/
structure DisplayFits (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    {sourceEnv : VEnv} {U : Nat} {Γ : List VExpr} {e A : VExpr}
    (display : EndpointDisplay sourceEnv U Γ e A)
    (common : Subst) (commonAvailable : Valuation) (locals : List Nat) where
  fits : TailFits sourceEnv env U registry target display.source locals
    (display.sourceSubst common) (display.sourceSubst common)
    (display.sourceValuation commonAvailable)
  original : fits.contextDerivation = display.context
  substitutions : Ctx.SubstEq env U target
    (display.sourceSubst common) (display.sourceSubst common) display.source

theorem DisplayFits.paired
    {display : EndpointDisplay sourceEnv U Γ e A}
    (frame : DisplayFits env registry target display common available locals)
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U)) :
    PairedFits env U registry display.source target locals
      (display.sourceSubst common) (display.sourceSubst common)
      (display.sourceValuation available) :=
  PairedFits.diagonal (frame.fits.toFits henv hTarget)

/-- Both clauses must be produced by the original pair recursion. The raw
clause has no profile argument, so an empty query cannot discard the evidence
needed by an enclosing Pi's frozen prototype. -/
structure DisplayCoherenceAnswer (env : VEnv) (registry : CanonicalHead.Registry)
    (target : List VExpr)
    {leftEnv rightEnv : VEnv} {U : Nat} {Γ : List VExpr} {e A B : VExpr}
    (left : EndpointDisplay leftEnv U Γ e A) (right : EndpointDisplay rightEnv U Γ e B)
    (common : Subst) (available : Valuation) (leftLocals rightLocals : List Nat) : Prop where
  path : TypeConversion env U target (A.subst common) (B.subst common)
  queries : ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
    CodeCert env U registry target leftLocals (left.sourceSubst common)
      left.sourceType profile footprint →
    footprint.Available (left.sourceValuation available) →
    Nonempty (CodeTransferResult env U registry target rightLocals
      (left.sourceSubst common) (right.sourceSubst common) (right.sourceValuation available)
      left.sourceType right.sourceType profile)

/-- The semantic induction hypothesis for a fixed pair of original endpoint
closures. Varying target worlds, anchors, or query sizes does not change either
closure's source cost. The final mutual theorem must construct this contract;
it is not an extra premise of final checker correctness. -/
def DisplayCoherence (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    {leftEnv rightEnv : VEnv} {Γ : List VExpr} {e A B : VExpr}
    (left : EndpointDisplay leftEnv U Γ e A) (right : EndpointDisplay rightEnv U Γ e B) : Prop :=
  ∀ (target : List VExpr) (common : Subst) (available : Valuation)
    (leftLocals rightLocals : List Nat), available.AtomClosed → OnCtx target (env.IsType U) →
    DisplayFits env registry target left common available leftLocals →
    DisplayFits env registry target right common available rightLocals →
    DisplayCoherenceAnswer env registry target left right common available leftLocals rightLocals

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
