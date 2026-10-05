import Lean4Lean.Theory.Typing.AnchoredOriginalTailPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalSortablePiRule

/-! Replay actual original conversion prefixes with hereditary queries and
exact rich source tails. Each retained equality child is its own F call. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

def ConversionCall.HereditaryFundamentals (env : VEnv) (registry : CanonicalHead.Registry)
    (plan : EndpointConversion sourceEnv U source A B)
    (initial : ContextDerivation sourceEnv U source) : Prop :=
  ∀ {context left right type} {original : Derivation sourceEnv U context left right type}
    (call : ConversionCall plan original),
    DerivationHereditaryFundamental env registry (call.contextDerivation initial) original

def PrefixCall.HereditaryFundamentals (env : VEnv) (registry : CanonicalHead.Registry)
    (route : PrefixRoute sourceEnv U source expression first last)
    (initial : ContextDerivation sourceEnv U source) : Prop :=
  ∀ {context left right type} {original : Derivation sourceEnv U context left right type}
    (call : PrefixCall route original),
    DerivationHereditaryFundamental env registry (call.contextDerivation initial) original

/-- Both directions of a conversion plan, using only its retained original
equality children in the exact contexts computed above. -/
theorem conversionSortableTailTransfers
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    (plan : EndpointConversion sourceEnv U source A B)
    (initial : ContextDerivation sourceEnv U source)
    (calls : ConversionCall.HereditaryFundamentals env registry plan initial)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target initial locals σ τ available) :
    ∃ level, SortableComputationalTransfer env U registry target locals σ τ available B A (.sort level) ∧
      SortableComputationalTransfer env U registry target locals σ τ available A B (.sort level) := by
  cases plan with
  | forward levelWF original =>
    have answer := calls .forward target locals σ τ available closed hTarget substitutions fits
    exact ⟨_, answer.2, answer.1⟩
  | backward levelWF original =>
    have answer := calls .backward target locals σ τ available closed hTarget substitutions fits
    exact ⟨_, answer.1, answer.2⟩
  | piDomain hu hv domain body otherBody =>
    have fundamental := DerivationHereditaryFundamental.forallEDF henv hscoped below initial
      hu hv domain body otherBody (calls .piDomain) (calls .piBody) (calls .piOtherBody)
    have answer := fundamental target locals σ τ available closed hTarget substitutions fits
    exact ⟨_, answer.1, answer.2⟩

theorem PrefixRoute.replayAcrossSortableOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals outputLocals : List Nat} {σ outputSubst : Subst}
    {available outputAvailable : Valuation}
    (initial : ContextDerivation sourceEnv U source)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailFits sourceEnv env U registry target source locals σ σ available)
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (route : PrefixRoute sourceEnv U source expression first last)
    (calls : PrefixCall.HereditaryFundamentals env registry route initial)
    {profile : Profile n} {outputType : VExpr}
    (finish : ∀ {footprint}, SortableCert env U registry target locals σ natural relevant profile footprint →
      footprint.Available available → Nonempty
        (SortableTransferResult env U registry target outputLocals σ outputSubst
          outputAvailable natural outputType relevant profile))
    {footprint : Footprint}
    (certificate : SortableCert env U registry target locals σ assigned relevant profile footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableTransferResult env U registry target outputLocals σ outputSubst
      outputAvailable assigned outputType relevant profile) := by
  induction route generalizing footprint with
  | done => exact finish certificate resources
  | expose reference rest ih => exact ih (fun call => calls (.expose call)) finish certificate resources
  | convert plan term rest ih =>
    obtain ⟨level, backwards, _⟩ := conversionSortableTailTransfers henv hscoped below plan initial
      (fun call => calls (.conversion call)) closed hTarget substitutions
      (SortableTailPairedFits.diagonal initial fits)
    obtain ⟨changed⟩ := SortableComputationalTransfer.sortable henv hscoped closed hTarget
      backwards certificate resources
    obtain ⟨result⟩ := ih (fun call => calls (.tail call)) finish changed.certificate changed.available
    exact ⟨{ result with related := changed.related.trans henv result.related }⟩

theorem PrefixRoute.restoreSortableOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {leftSubst σ : Subst}
    {available : Valuation}
    (initial : ContextDerivation sourceEnv U source)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailFits sourceEnv env U registry target source locals σ σ available)
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (route : PrefixRoute sourceEnv U source expression first last)
    (calls : PrefixCall.HereditaryFundamentals env registry route initial)
    {profile : Profile n} {inputType : VExpr}
    (incoming : SortableTransferResult env U registry target locals leftSubst σ available
      inputType natural relevant profile) :
    Nonempty (SortableTransferResult env U registry target locals leftSubst σ available
      inputType assigned relevant profile) := by
  induction route with
  | done => exact ⟨incoming⟩
  | expose reference rest ih => exact ih (fun call => calls (.expose call)) incoming
  | convert plan term rest ih =>
    obtain ⟨inner⟩ := ih (fun call => calls (.tail call)) incoming
    obtain ⟨level, _, forward⟩ := conversionSortableTailTransfers henv hscoped below plan initial
      (fun call => calls (.conversion call)) closed hTarget substitutions
      (SortableTailPairedFits.diagonal initial fits)
    obtain ⟨outer⟩ := SortableComputationalTransfer.sortable henv hscoped closed hTarget
      forward inner.certificate inner.available
    exact ⟨⟨outer.footprint, outer.certificate, outer.available,
      inner.related.trans henv outer.related⟩⟩

theorem PrefixRoute.compareHeadsSortableOriginal
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
    (leftFits : SortableTailFits leftEnv env U registry target leftSource leftLocals σ σ leftAvailable)
    (rightFits : SortableTailFits rightEnv env U registry target rightSource rightLocals τ τ rightAvailable)
    {left : EndpointState leftEnv U leftSource leftExpression leftAssigned}
    {leftHead : EndpointState leftEnv U leftSource leftExpression leftNatural}
    {right : EndpointState rightEnv U rightSource rightExpression rightAssigned}
    {rightHead : EndpointState rightEnv U rightSource rightExpression rightNatural}
    (leftRoute : PrefixRoute leftEnv U leftSource leftExpression left leftHead)
    (rightRoute : PrefixRoute rightEnv U rightSource rightExpression right rightHead)
    (leftCalls : PrefixCall.HereditaryFundamentals env registry leftRoute leftInitial)
    (rightCalls : PrefixCall.HereditaryFundamentals env registry rightRoute rightInitial)
    {profile : Profile n}
    (natural : ∀ {footprint}, SortableCert env U registry target leftLocals σ leftNatural relevant profile footprint →
      footprint.Available leftAvailable → Nonempty
        (SortableTransferResult env U registry target rightLocals σ τ rightAvailable
          leftNatural rightNatural relevant profile))
    {footprint : Footprint}
    (certificate : SortableCert env U registry target leftLocals σ leftAssigned relevant profile footprint)
    (resources : footprint.Available leftAvailable) :
    Nonempty (SortableTransferResult env U registry target rightLocals σ τ rightAvailable
      leftAssigned rightAssigned relevant profile) := by
  obtain ⟨compared⟩ := leftRoute.replayAcrossSortableOriginal henv hscoped leftBelow leftInitial leftClosed hTarget
    leftSubstitutions leftFits leftCalls natural certificate resources
  exact rightRoute.restoreSortableOriginal henv hscoped rightBelow rightInitial rightClosed hTarget
    rightSubstitutions rightFits rightCalls compared

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
