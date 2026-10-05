import Lean4Lean.Theory.Typing.AnchoredOriginalPrefixReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalTailFundamental
import Lean4Lean.Theory.Typing.AnchoredOriginalTailPi

/-! Conversion replay retains the exact original context of every equality
child. In the Pi-domain plan the two bodies use the left and right domain
endpoints respectively; their equal closure weights do not identify contexts. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

def ConversionCall.contextDerivation
    {sourceEnv : VEnv} {U : Nat} {source : List VExpr} {A B : VExpr}
    {plan : EndpointConversion sourceEnv U source A B}
    {context : List VExpr} {left right type : VExpr}
    {original : Derivation sourceEnv U context left right type}
    (call : ConversionCall plan original) (initial : ContextDerivation sourceEnv U source) :
    ContextDerivation sourceEnv U context := by
  cases call with
  | forward | backward | piDomain => exact initial
  | @piBody u hu v hv A A' domain B body otherBody => exact .cons initial (.left domain)
  | @piOtherBody u hu v hv A A' domain B body otherBody => exact .cons initial (.right domain)

theorem ConversionCall.contextDerivation_closures
    {plan : EndpointConversion sourceEnv U source A B}
    (call : ConversionCall plan original) (initial : ContextDerivation sourceEnv U source) :
    (call.contextDerivation initial).closures = call.environment initial.closures := by
  cases call <;> rfl

def PrefixCall.contextDerivation
    {sourceEnv : VEnv} {U : Nat} {source : List VExpr} {expression A B : VExpr}
    {first : EndpointState sourceEnv U source expression A}
    {last : EndpointState sourceEnv U source expression B}
    {route : PrefixRoute sourceEnv U source expression first last}
    {context : List VExpr} {left right type : VExpr}
    {original : Derivation sourceEnv U context left right type}
    (call : PrefixCall route original) (initial : ContextDerivation sourceEnv U source) :
    ContextDerivation sourceEnv U context :=
  match call with
  | .expose call | .tail call => call.contextDerivation initial
  | .conversion call => call.contextDerivation initial

theorem PrefixCall.contextDerivation_closures
    {first : EndpointState sourceEnv U source expression A}
    {last : EndpointState sourceEnv U source expression B}
    {route : PrefixRoute sourceEnv U source expression first last}
    (call : PrefixCall route original) (initial : ContextDerivation sourceEnv U source) :
    (call.contextDerivation initial).closures = call.environment initial.closures := by
  induction call with
  | expose call ih | tail call ih => exact ih
  | conversion call => exact call.contextDerivation_closures initial

def ConversionCall.Fundamentals (env : VEnv) (registry : CanonicalHead.Registry)
    (plan : EndpointConversion sourceEnv U source A B)
    (initial : ContextDerivation sourceEnv U source) : Prop :=
  ∀ {context left right type} {original : Derivation sourceEnv U context left right type}
    (call : ConversionCall plan original),
    DerivationFundamental env registry (call.contextDerivation initial) original

def PrefixCall.Fundamentals (env : VEnv) (registry : CanonicalHead.Registry)
    (route : PrefixRoute sourceEnv U source expression first last)
    (initial : ContextDerivation sourceEnv U source) : Prop :=
  ∀ {context left right type} {original : Derivation sourceEnv U context left right type}
    (call : PrefixCall route original),
    DerivationFundamental env registry (call.contextDerivation initial) original

/-- Both directions of a conversion plan, using only its retained original
equality children in the exact contexts computed above. -/
theorem conversionTailTransfers
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    (plan : EndpointConversion sourceEnv U source A B)
    (initial : ContextDerivation sourceEnv U source)
    (calls : ConversionCall.Fundamentals env registry plan initial)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : TailPairedFits env registry target initial locals σ τ available) :
    ∃ level, GradedTransfer env U registry target locals σ τ available B A (.sort level) ∧
      GradedTransfer env U registry target locals σ τ available A B (.sort level) := by
  cases plan with
  | forward levelWF original =>
    have answer := calls .forward target locals σ τ available closed hTarget substitutions fits
    exact ⟨_, answer.2.1, answer.1⟩
  | backward levelWF original =>
    have answer := calls .backward target locals σ τ available closed hTarget substitutions fits
    exact ⟨_, answer.1, answer.2.1⟩
  | piDomain hu hv domain body otherBody =>
    have fundamental := DerivationFundamental.forallEDF henv hscoped below initial
      hu hv domain body otherBody (calls .piDomain) (calls .piBody) (calls .piOtherBody)
    have answer := fundamental target locals σ τ available closed hTarget substitutions fits
    exact ⟨_, answer.1, answer.2.1⟩

theorem PrefixRoute.replayAcrossOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals outputLocals : List Nat} {σ outputSubst : Subst}
    {available outputAvailable : Valuation}
    (initial : ContextDerivation sourceEnv U source)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : TailFits sourceEnv env U registry target source locals σ σ available)
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (route : PrefixRoute sourceEnv U source expression first last)
    (calls : PrefixCall.Fundamentals env registry route initial)
    {profile : Profile n} {outputType : VExpr}
    (finish : ∀ {footprint}, CodeCert env U registry target locals σ natural profile footprint →
      footprint.Available available → Nonempty
        (CodeTransferResult env U registry target outputLocals σ outputSubst
          outputAvailable natural outputType profile))
    {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) :
    Nonempty (CodeTransferResult env U registry target outputLocals σ outputSubst
      outputAvailable assigned outputType profile) := by
  induction route generalizing footprint with
  | done => exact finish certificate resources
  | expose reference rest ih => exact ih (fun call => calls (.expose call)) finish certificate resources
  | convert plan term rest ih =>
    obtain ⟨level, backwards, _⟩ := conversionTailTransfers henv hscoped below plan initial
      (fun call => calls (.conversion call)) closed hTarget substitutions
      (TailPairedFits.diagonal initial fits)
    obtain ⟨changed⟩ := certificate.transfer_graded henv hscoped hTarget closed backwards resources
    obtain ⟨result⟩ := ih (fun call => calls (.tail call)) finish changed.certificate changed.available
    exact ⟨{ result with related := changed.related.trans henv result.related }⟩

theorem PrefixRoute.restoreOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {leftSubst σ : Subst}
    {available : Valuation}
    (initial : ContextDerivation sourceEnv U source)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : TailFits sourceEnv env U registry target source locals σ σ available)
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (route : PrefixRoute sourceEnv U source expression first last)
    (calls : PrefixCall.Fundamentals env registry route initial)
    {profile : Profile n} {inputType : VExpr}
    (incoming : CodeTransferResult env U registry target locals leftSubst σ available
      inputType natural profile) :
    Nonempty (CodeTransferResult env U registry target locals leftSubst σ available
      inputType assigned profile) := by
  induction route with
  | done => exact ⟨incoming⟩
  | expose reference rest ih => exact ih (fun call => calls (.expose call)) incoming
  | convert plan term rest ih =>
    obtain ⟨inner⟩ := ih (fun call => calls (.tail call)) incoming
    obtain ⟨level, _, forward⟩ := conversionTailTransfers henv hscoped below plan initial
      (fun call => calls (.conversion call)) closed hTarget substitutions
      (TailPairedFits.diagonal initial fits)
    obtain ⟨outer⟩ := inner.certificate.transfer_graded henv hscoped hTarget closed forward inner.available
    exact ⟨⟨outer.footprint, outer.certificate, outer.available,
      inner.related.trans henv outer.related⟩⟩

theorem PrefixRoute.compareHeadsOriginal
    {leftEnv rightEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    {leftSource rightSource target : List VExpr} {leftLocals rightLocals : List Nat}
    {σ τ : Subst} {leftAvailable rightAvailable : Valuation}
    (leftInitial : ContextDerivation leftEnv U leftSource)
    (rightInitial : ContextDerivation rightEnv U rightSource)
    (leftClosed : leftAvailable.AtomClosed) (rightClosed : rightAvailable.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (leftSubstitutions : Ctx.SubstEq env U target σ σ leftSource)
    (rightSubstitutions : Ctx.SubstEq env U target τ τ rightSource)
    (leftFits : TailFits leftEnv env U registry target leftSource leftLocals σ σ leftAvailable)
    (rightFits : TailFits rightEnv env U registry target rightSource rightLocals τ τ rightAvailable)
    {left : EndpointState leftEnv U leftSource leftExpression leftAssigned}
    {leftHead : EndpointState leftEnv U leftSource leftExpression leftNatural}
    {right : EndpointState rightEnv U rightSource rightExpression rightAssigned}
    {rightHead : EndpointState rightEnv U rightSource rightExpression rightNatural}
    (leftRoute : PrefixRoute leftEnv U leftSource leftExpression left leftHead)
    (rightRoute : PrefixRoute rightEnv U rightSource rightExpression right rightHead)
    (leftCalls : PrefixCall.Fundamentals env registry leftRoute leftInitial)
    (rightCalls : PrefixCall.Fundamentals env registry rightRoute rightInitial)
    {profile : Profile n}
    (natural : ∀ {footprint}, CodeCert env U registry target leftLocals σ leftNatural profile footprint →
      footprint.Available leftAvailable → Nonempty
        (CodeTransferResult env U registry target rightLocals σ τ rightAvailable
          leftNatural rightNatural profile))
    {footprint : Footprint}
    (certificate : CodeCert env U registry target leftLocals σ leftAssigned profile footprint)
    (resources : footprint.Available leftAvailable) :
    Nonempty (CodeTransferResult env U registry target rightLocals σ τ rightAvailable
      leftAssigned rightAssigned profile) := by
  obtain ⟨compared⟩ := leftRoute.replayAcrossOriginal henv hscoped leftBelow leftInitial leftClosed hTarget
    leftSubstitutions leftFits leftCalls natural certificate resources
  exact rightRoute.restoreOriginal henv hscoped rightBelow rightInitial rightClosed hTarget
    rightSubstitutions rightFits rightCalls compared

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
