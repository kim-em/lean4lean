import Lean4Lean.Theory.Typing.AnchoredOriginalRichDirectPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalRichComputationalValue

/-! Paired value restoration through the finite original head route. Both
channels are retained: the assigned support follows exact original equality
calls, and the right computational query follows the same syntactic route. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

variable {header : EndpointRef headerEnv U [] headerExpression headerType}
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}

def RichGradedResult.restoreRoute
    (route : PrefixRoute sourceEnv U source expression first last)
    (answer : RichGradedResult sourceEnv env U registry target last locals τ available profile) :
    RichGradedResult sourceEnv env U registry target first locals τ available profile :=
  { answer with observation := .route route answer.observation }

/-- One exact same-expression R request from a retained formation occurrence.
The strict bound is supplied to the induction hypothesis, not assumed. -/
def FormationRestoreCall (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    (hf : headerEnv.Ordered) (captured : List Closure)
    (caller : Origin)
    {headerSource : List VExpr} {assigned : VExpr} {u v : VLevel}
    (first : EndpointState headerEnv U headerSource assigned (.sort u))
    (last : EndpointState headerEnv U headerSource assigned (.sort v))
    (locals : List Nat) (σ : Subst) (available : Valuation) : Prop :=
  richSchedule .expressionReindex
      ((Closure.close (first.dependencyOrigin hf) captured).cost +
       (Closure.close (last.dependencyOrigin hf) captured).cost) <
    richSchedule .fundamental (Closure.close caller captured).cost →
  RichCodeTransfer env U registry target first last locals locals σ σ available available

/-- An actual original equality child, retaining its direction and finite
budget. It is not a supplier for arbitrary equal source types. -/
def EqualityRestoreCall (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    (hf : headerEnv.Ordered) (captured : List Closure) (caller : Origin)
    {headerSource : List VExpr} {A B : VExpr} {level : VLevel}
    (original : Derivation headerEnv U headerSource A B (.sort level))
    (forward : Bool) (locals : List Nat) (σ : Subst) (available : Valuation) : Prop :=
  richSchedule .fundamental (Closure.close (original.dependencyOrigin hf) captured).cost <
    richSchedule .fundamental (Closure.close caller captured).cost →
  if forward then
    RichCodeTransfer env U registry target (.ref (.left original)) (.ref (.right original))
      locals locals σ σ available available
  else
    RichCodeTransfer env U registry target (.ref (.right original)) (.ref (.left original))
      locals locals σ σ available available

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource

namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.DirectPrefixRoute
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalRecordSource OriginalTail
set_option backward.isDefEq.respectTransparency false

variable {header : EndpointRef headerEnv U [] headerExpression headerType}
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}

/-- The finite induction ledger contains only formations and original
equalities literally encountered on this concrete route. -/
def RestoreCalls
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (hf : headerEnv.Ordered) (captured : List Closure)
    {headerSource : List VExpr} {expression assigned natural : VExpr}
    {first : EndpointState headerEnv U headerSource expression assigned}
    {last : EndpointState headerEnv U headerSource expression natural}
    (route : DirectPrefixRoute headerEnv U headerSource expression first last)
    (locals : List Nat) (σ : Subst) (available : Valuation) : Prop :=
  match route with
  | .done _ => True
  | .expose reference rest =>
    FormationRestoreCall env U registry target hf captured (reference.dependencyOrigin hf)
      reference.expose.typeFormation.node reference.typeFormation.node locals σ available ∧
    RestoreCalls env registry target hf captured rest locals σ available
  | .forward levelWF original term rest =>
    FormationRestoreCall env U registry target hf captured
      ((EndpointState.convert (.forward levelWF original) term).dependencyOrigin hf)
      term.typeFormation.node (.ref (.left original)) locals σ available ∧
    EqualityRestoreCall env U registry target hf captured
      ((EndpointState.convert (.forward levelWF original) term).dependencyOrigin hf)
      original true locals σ available ∧
    RestoreCalls env registry target hf captured rest locals σ available
  | .backward levelWF original term rest =>
    FormationRestoreCall env U registry target hf captured
      ((EndpointState.convert (.backward levelWF original) term).dependencyOrigin hf)
      term.typeFormation.node (.ref (.right original)) locals σ available ∧
    EqualityRestoreCall env U registry target hf captured
      ((EndpointState.convert (.backward levelWF original) term).dependencyOrigin hf)
      original false locals σ available ∧
    RestoreCalls env registry target hf captured rest locals σ available

/-- Complete paired restoration for an actual non-lambda original prefix.
The actual frame fixes every call's closure environment. -/
theorem restoreComputational
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) (initial : List Closure)
    (frame : HeaderBinderFrame header field major env registry target context locals σ τ available)
    {first : EndpointState headerEnv U headerSource expression assigned}
    {last : EndpointState headerEnv U headerSource expression natural}
    (route : DirectPrefixRoute headerEnv U headerSource expression first last)
    (calls : route.RestoreCalls env registry target hf
      (frame.dependencyEnvironment hf sf initial) locals σ available)
    (answer : RichComputationalValue headerEnv env U registry target last locals σ τ available profile) :
    Nonempty (RichComputationalValue headerEnv env U registry target first locals σ τ available profile) := by
  induction route with
  | done node => exact ⟨answer⟩
  | expose reference rest ih =>
    obtain ⟨tail⟩ := ih calls.2 answer
    obtain ⟨value⟩ := frame.restoreExposure hf sf initial reference tail.toRichSupportedValue calls.1
    exact ⟨{ value with rightQuery := tail.rightQuery.restoreRoute (.expose reference (.done _)) }⟩
  | forward levelWF original term rest ih =>
    obtain ⟨tail⟩ := ih calls.2.2 answer
    obtain ⟨value⟩ := tail.toRichSupportedValue.convertForward henv hf
      (frame.dependencyEnvironment hf sf initial) levelWF original calls.1 calls.2.1
    exact ⟨{ value with rightQuery := (tail.rightQuery.restoreRoute
      (.convert (.forward levelWF original) term (.done _))) }⟩
  | backward levelWF original term rest ih =>
    obtain ⟨tail⟩ := ih calls.2.2 answer
    obtain ⟨value⟩ := tail.toRichSupportedValue.convertBackward henv hf
      (frame.dependencyEnvironment hf sf initial) levelWF original calls.1 calls.2.1
    exact ⟨{ value with rightQuery := (tail.rightQuery.restoreRoute
      (.convert (.backward levelWF original) term (.done _))) }⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.DirectPrefixRoute
