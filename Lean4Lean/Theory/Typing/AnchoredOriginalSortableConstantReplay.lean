import Lean4Lean.Theory.Typing.AnchoredOriginalSortablePrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalTailConstant

/-! Hereditary constant-header replay retains its actual finite original
ambient and conversion calls, including the displayed universe packet. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

structure SortableConstantReplayResult
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (name : Name) (levels : List VLevel) (assigned : VExpr) (relevant : Bool) (profile : Profile n) where
  info : VConstant
  lookup : sourceEnv.constants name = some info
  transfer : SortableTransferResult env U registry target locals σ σ available assigned
    (info.type.instL levels) relevant profile
  targetPath : TypeConversion env U target (assigned.subst σ)
    ((info.type.instL levels).subst σ)

def ConstantCall.HereditaryFundamentals (env : VEnv) (registry : CanonicalHead.Registry)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (initial : ContextDerivation sourceEnv U source) : Prop :=
  ∀ {context left right type} {original : Derivation sourceEnv U context left right type}
    (call : ConstantCall reference original),
    DerivationHereditaryFundamental env registry (call.contextDerivation initial) original

def ConstantPrefixCall.HereditaryFundamentals (env : VEnv) (registry : CanonicalHead.Registry)
    {name : Name} {levels : List VLevel}
    {first : EndpointState sourceEnv U source (.const name levels) assigned}
    (packet : ConstantPrefix first) (initial : ContextDerivation sourceEnv U source) : Prop :=
  ∀ {context left right type} {original : Derivation sourceEnv U context left right type}
    (call : ConstantPrefixCall packet original),
    DerivationHereditaryFundamental env registry (call.contextDerivation initial) original

theorem EndpointRef.replayConstantSortableOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (initial : ContextDerivation sourceEnv U source)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailFits sourceEnv env U registry target source locals σ σ available)
    {name : Name} {levels : List VLevel} {assigned : VExpr}
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expressionEq : expression = .const name levels)
    (primitive : reference.Primitive) (calls : ConstantCall.HereditaryFundamentals env registry reference initial)
    {profile : Profile n} {footprint : Footprint}
    (certificate : SortableCert env U registry target locals σ assigned relevant profile footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableConstantReplayResult sourceEnv env U registry target locals σ available
      name levels assigned relevant profile) := by
  cases reference with
  | left original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl lookup levelsWF otherLevelsWF levelCount levelEquality levelWF headerClosed ambient =>
      obtain ⟨answer⟩ := SortableComputationalTransfer.sortable henv hscoped closed hTarget
        (calls .left target locals σ σ available closed hTarget substitutions
          (SortableTailPairedFits.diagonal initial fits)).1 certificate resources
      exact ⟨⟨_, by assumption, ⟨footprint, certificate, resources, answer.related.left_diagonal⟩, .refl⟩⟩
  | right original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl lookup levelsWF otherLevelsWF levelCount levelEquality levelWF headerClosed ambient =>
      obtain ⟨answer⟩ := SortableComputationalTransfer.sortable henv hscoped closed hTarget
        (calls .right target locals σ σ available closed hTarget substitutions
          (SortableTailPairedFits.diagonal initial fits)).1 certificate resources
      exact ⟨⟨_, by assumption, answer.toSortableTransferResult,
        .single ((ambient.forget.defeq.mono below).substDF henv
          substitutions.wf hTarget substitutions)⟩⟩

private theorem PrefixRoute.replayHeaderSortableOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (initial : ContextDerivation sourceEnv U source)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailFits sourceEnv env U registry target source locals σ σ available)
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (route : PrefixRoute sourceEnv U source expression first last)
    (calls : PrefixCall.HereditaryFundamentals env registry route initial)
    {name : Name} {levels : List VLevel} {profile : Profile n}
    (finish : ∀ {footprint}, SortableCert env U registry target locals σ natural relevant profile footprint →
      footprint.Available available → Nonempty
        (SortableConstantReplayResult sourceEnv env U registry target locals σ available name levels natural relevant profile))
    {footprint : Footprint}
    (certificate : SortableCert env U registry target locals σ assigned relevant profile footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableConstantReplayResult sourceEnv env U registry target locals σ available
      name levels assigned relevant profile) := by
  induction route generalizing footprint with
  | done => exact finish certificate resources
  | expose reference rest ih => exact ih (fun call => calls (.expose call)) finish certificate resources
  | convert plan term rest ih =>
    obtain ⟨level, backward, _⟩ := conversionSortableTailTransfers henv hscoped below plan initial
      (fun call => calls (.conversion call)) closed hTarget substitutions
      (SortableTailPairedFits.diagonal initial fits)
    obtain ⟨changed⟩ := SortableComputationalTransfer.sortable henv hscoped closed hTarget
      backward certificate resources
    obtain ⟨result⟩ := ih (fun call => calls (.tail call)) finish changed.certificate changed.available
    obtain ⟨rawLevel, _, equal⟩ := plan.sound
    have path := TypeConversion.single ((equal.symm.defeq.mono below).substDF henv
      substitutions.wf hTarget substitutions)
    exact ⟨{ result with
      transfer := { result.transfer with related := changed.related.trans henv result.transfer.related }
      targetPath := path.trans result.targetPath }⟩

/-- Complete backward transport from an actual syntactic constant endpoint
to its displayed declaration header. All semantic calls are the packet's
finite, strictly smaller original children. -/
theorem ConstantPrefix.replaySortableOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (initial : ContextDerivation sourceEnv U source)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailFits sourceEnv env U registry target source locals σ σ available)
    {name : Name} {levels : List VLevel}
    {first : EndpointState sourceEnv U source (.const name levels) assigned}
    (packet : ConstantPrefix first)
    (calls : ConstantPrefixCall.HereditaryFundamentals env registry packet initial)
    {profile : Profile n} {footprint : Footprint}
    (certificate : SortableCert env U registry target locals σ assigned relevant profile footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableConstantReplayResult sourceEnv env U registry target locals σ available
      name levels assigned relevant profile) := by
  exact packet.route.replayHeaderSortableOriginal henv hscoped below initial closed hTarget substitutions fits
    (fun call => calls (.conversion call))
    (fun current present => EndpointRef.replayConstantSortableOriginal henv hscoped below initial closed hTarget
      substitutions fits packet.reference rfl packet.primitive (fun call => calls (.ambient call)) current present)
    certificate resources


end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
