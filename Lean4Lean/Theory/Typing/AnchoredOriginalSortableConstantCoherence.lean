import Lean4Lean.Theory.Typing.AnchoredOriginalSortableConstantReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableDisplayTransport

/-! Constant comparison for either formation flag, retaining the exact
original ambient equality and finite conversion-call contexts on each side. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Restore a primitive constant endpoint from its displayed header. The
left endpoint consumes the incoming answer unchanged; the right endpoint
uses the original ambient header equality in the reverse direction. -/
theorem EndpointRef.restoreConstantSortableOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {leftSubst σ : Subst}
    {available : Valuation}
    (initial : ContextDerivation sourceEnv U source)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailFits sourceEnv env U registry target source locals σ σ available)
    {name : Name} {levels : List VLevel} {assigned : VExpr} {info : VConstant}
    (lookup : env.constants name = some info)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expressionEq : expression = .const name levels)
    (primitive : reference.Primitive) (calls : ConstantCall.HereditaryFundamentals env registry reference initial)
    {profile : Profile n} {inputType : VExpr}
    (incoming : SortableTransferResult env U registry target locals leftSubst σ available
      inputType (info.type.instL levels) relevant profile) :
    Nonempty (SortableTransferResult env U registry target locals leftSubst σ available
      inputType assigned relevant profile) := by
  cases reference with
  | left original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    case constDF actualLookup levelsWF otherLevelsWF levelCount levelEquality levelWF headerClosed ambient =>
      cases expressionEq
      have same := Option.some.inj (lookup.symm.trans (below.constants actualLookup))
      cases same
      exact ⟨incoming⟩
    all_goals cases expressionEq
  | right original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    case constDF actualLookup levelsWF otherLevelsWF levelCount levelEquality levelWF headerClosed ambient =>
      cases expressionEq
      have same := Option.some.inj (lookup.symm.trans (below.constants actualLookup))
      cases same
      have answerPair := calls .right target locals σ σ available closed hTarget substitutions
        (SortableTailPairedFits.diagonal initial fits)
      obtain ⟨answer⟩ := SortableComputationalTransfer.sortable henv hscoped closed hTarget
        answerPair.2 incoming.certificate incoming.available
      exact ⟨⟨answer.footprint, answer.certificate, answer.available,
        incoming.related.trans henv answer.related⟩⟩
    all_goals cases expressionEq

/-- The primitive constant restoration is followed by the actual finite
outward conversion route to the caller's assigned source type. -/
theorem ConstantPrefix.restoreSortableOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {leftSubst σ : Subst}
    {available : Valuation}
    (initial : ContextDerivation sourceEnv U source)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailFits sourceEnv env U registry target source locals σ σ available)
    {name : Name} {levels : List VLevel} {info : VConstant}
    {first : EndpointState sourceEnv U source (.const name levels) assigned}
    (packet : ConstantPrefix first) (lookup : env.constants name = some info)
    (calls : ConstantPrefixCall.HereditaryFundamentals env registry packet initial)
    {profile : Profile n} {inputType : VExpr}
    (incoming : SortableTransferResult env U registry target locals leftSubst σ available
      inputType (info.type.instL levels) relevant profile) :
    Nonempty (SortableTransferResult env U registry target locals leftSubst σ available
      inputType assigned relevant profile) := by
  obtain ⟨natural⟩ := EndpointRef.restoreConstantSortableOriginal henv hscoped below initial closed hTarget
    substitutions fits lookup packet.reference rfl packet.primitive
    (fun call => calls (.ambient call)) incoming
  exact packet.route.restoreSortableOriginal henv hscoped below initial closed hTarget substitutions fits
    (fun call => calls (.conversion call)) natural


/-- Compare two actual constant endpoints through their common declaration
header. Source certificate transport uses only the existing common display;
its header is closed by the actual declaration's formation theorem. -/
theorem ConstantPrefix.compareSortableOriginal
    {leftEnv rightEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    {leftSource rightSource target : List VExpr} {leftLocals rightLocals : List Nat}
    {σ τ : Subst} {leftAvailable rightAvailable commonAvailable : Valuation}
    (leftInitial : ContextDerivation leftEnv U leftSource)
    (rightInitial : ContextDerivation rightEnv U rightSource)
    (leftClosed : leftAvailable.AtomClosed) (rightClosed : rightAvailable.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (leftSubstitutions : Ctx.SubstEq env U target σ σ leftSource)
    (rightSubstitutions : Ctx.SubstEq env U target τ τ rightSource)
    (leftFits : SortableTailFits leftEnv env U registry target leftSource leftLocals σ σ leftAvailable)
    (rightFits : SortableTailFits rightEnv env U registry target rightSource rightLocals τ τ rightAvailable)
    {name : Name} {levels : List VLevel}
    {left : EndpointState leftEnv U leftSource (.const name levels) leftAssigned}
    {right : EndpointState rightEnv U rightSource (.const name levels) rightAssigned}
    (leftPacket : ConstantPrefix left) (rightPacket : ConstantPrefix right)
    (leftCalls : ConstantPrefixCall.HereditaryFundamentals env registry leftPacket leftInitial)
    (rightCalls : ConstantPrefixCall.HereditaryFundamentals env registry rightPacket rightInitial)
    (leftMap rightMap : Lift) (common : Subst) (commonLocals : List Nat)
    (leftRealization : Subst.lift_l leftMap common = σ)
    (rightRealization : Subst.lift_l rightMap common = τ)
    (leftAvailableEq : ∀ index, leftAvailable index = commonAvailable (leftMap.liftVar index))
    (rightAvailableEq : ∀ index, rightAvailable index = commonAvailable (rightMap.liftVar index))
    {profile : Profile n} {footprint : Footprint}
    (certificate : SortableCert env U registry target leftLocals σ leftAssigned relevant profile footprint)
    (resources : footprint.Available leftAvailable) :
    Nonempty (SortableTransferResult env U registry target rightLocals σ τ rightAvailable
      leftAssigned rightAssigned relevant profile) := by
  obtain ⟨header⟩ := leftPacket.replaySortableOriginal henv hscoped leftBelow leftInitial leftClosed hTarget
    leftSubstitutions leftFits leftCalls certificate resources
  have lookup := leftBelow.constants header.lookup
  have headerClosed : (header.info.type.instL levels).Closed := by
    obtain ⟨level, formation⟩ := henv.constWF lookup
    exact (VExpr.WF.closedN henv ⟨_, formation⟩ trivial).instL
  obtain ⟨required, ⟨transported⟩, available⟩ := OriginalFactorCut.SortableCert.betweenDisplays
    header.transfer.certificate leftMap rightMap common leftRealization rightRealization
    (show (header.info.type.instL levels).lift' leftMap =
      (header.info.type.instL levels).lift' rightMap from by
        rw [headerClosed.lift'_eq .zero, headerClosed.lift'_eq .zero])
    commonLocals rightLocals header.transfer.available leftAvailableEq rightAvailableEq
  have incoming : SortableTransferResult env U registry target rightLocals σ τ rightAvailable
      leftAssigned (header.info.type.instL levels) relevant profile := {
    footprint := required, certificate := transported, available := available
    related := by
      simpa only [headerClosed.subst_eq (σ := σ) .zero,
        headerClosed.subst_eq (σ := τ) .zero] using header.transfer.related }
  exact rightPacket.restoreSortableOriginal henv hscoped rightBelow rightInitial rightClosed hTarget
    rightSubstitutions rightFits lookup rightCalls incoming



end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
