import Lean4Lean.Theory.Typing.AnchoredSortableTailDepth
import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepthProvenance
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableFundamental
import Lean4Lean.Theory.Typing.AnchoredStageBudgets

/-! The hereditary declaration motive retains all caller controls on the
same observer, assigned-type certificate, and original context stack. Its
original endpoint is fixed; no clause quantifies over arbitrary derivations.
This strengthens the induction contract, not a proof of its general case. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

def OriginalTail.SortableTailPairedFits.nativeDepth (current : Name → Bool)
    (frame : SortableTailPairedFits env registry target context locals σ τ available) : Nat :=
  max (frame.forward.nativeDepth current) (frame.backward.nativeDepth current)

namespace HereditaryBudgeted
abbrev Budgets := Budgeted.Budgets
abbrev Within := Budgeted.Within

structure Result (budgets : Budgets) (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat)
    (σ τ : Subst) (available : Valuation) (left right assigned : VExpr) (demand : Profile n)
    extends SortableComputationalTransferResult env U registry target locals σ τ available
      left right assigned demand where
  observationBound : Within budgets observation.nativeDepth
  certificateBound : Within budgets typeCertificate.nativeDepth

def Transfer (budgets : Budgets) (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat)
    (σ τ : Subst) (available : Valuation) (left right assigned : VExpr) : Prop :=
  ∀ {n : Nat} {demand : Profile n} {footprint : Footprint},
    (observation : SortableObs env U registry target locals σ left demand footprint) →
    Within budgets observation.nativeDepth → footprint.Available available →
    Nonempty (Result budgets env U registry target locals σ τ available left right assigned demand)

/- The phase supplies exactly one fixed list, shared by every original child. -/
def StateFundamentalAt (budgets : Budgets) (env : VEnv) (registry : CanonicalHead.Registry)
    (context : ContextDerivation sourceEnv U source)
    (node : EndpointState sourceEnv U source expression assigned) : Prop :=
  ∀ (target : List VExpr) (locals : List Nat)
    (σ τ : Subst) (available : Valuation),
    available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ source →
    ∀ frame : SortableTailPairedFits env registry target context locals σ τ available,
      Within budgets frame.nativeDepth →
      Transfer budgets env U registry target locals σ τ available expression expression assigned

/-- The pointwise original motive. In a header induction only phase-valid
budget lists may be used, unlike `DerivationFundamental`'s unrestricted list. -/
def FundamentalAt (budgets : Budgets) (env : VEnv) (registry : CanonicalHead.Registry)
    (context : ContextDerivation sourceEnv U source)
    (_original : Derivation sourceEnv U source left right assigned) : Prop :=
  ∀ (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation),
    available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ source →
    ∀ frame : SortableTailPairedFits env registry target context locals σ τ available,
      Within budgets frame.nativeDepth →
      Transfer budgets env U registry target locals σ τ available left right assigned ∧
      Transfer budgets env U registry target locals σ τ available right left assigned

def StateFundamental (env : VEnv) (registry : CanonicalHead.Registry)
    (context : ContextDerivation sourceEnv U source)
    (node : EndpointState sourceEnv U source expression assigned) : Prop :=
  ∀ (budgets : Budgets) (target : List VExpr) (locals : List Nat)
    (σ τ : Subst) (available : Valuation),
    available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ source →
    ∀ frame : SortableTailPairedFits env registry target context locals σ τ available,
      Within budgets frame.nativeDepth →
      Transfer budgets env U registry target locals σ τ available expression expression assigned

def DerivationFundamental (env : VEnv) (registry : CanonicalHead.Registry)
    (context : ContextDerivation sourceEnv U source)
    (original : Derivation sourceEnv U source left right assigned) : Prop :=
  ∀ (budgets : Budgets) (target : List VExpr) (locals : List Nat)
    (σ τ : Subst) (available : Valuation),
    available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ source →
    ∀ frame : SortableTailPairedFits env registry target context locals σ τ available,
      Within budgets frame.nativeDepth →
      Transfer budgets env U registry target locals σ τ available left right assigned ∧
      Transfer budgets env U registry target locals σ τ available right left assigned

/-- A new control chooses its fuel from the actual paired finite stack.
Neither source witnesses nor context origins are replaced. -/
theorem finiteControl (current : Name → Bool)
    (frame : SortableTailPairedFits env registry target context locals σ τ available)
    (bounded : Within budgets frame.nativeDepth) :
    ∃ fuel, Within ((current, fuel) :: budgets) frame.nativeDepth := by
  refine ⟨frame.nativeDepth current, ?_⟩
  intro filter limit member
  rcases List.mem_cons.mp member with equal | member
  · cases equal; exact Nat.le_refl _
  · exact bounded filter limit member

theorem StateFundamental.forget
    (original : StateFundamental env registry context node) :
    StateHereditaryFundamental env registry context node := by
  intro target locals σ τ available closed formed substitutions frame n demand footprint observation resources
  obtain ⟨answer⟩ := original [] target locals σ τ available closed formed substitutions frame
    (fun _ _ member => nomatch member) observation (fun _ _ member => nomatch member) resources
  exact ⟨answer.toSortableComputationalTransferResult⟩

theorem DerivationFundamental.forget
    (original : DerivationFundamental env registry context derivation) :
    DerivationHereditaryFundamental env registry context derivation := by
  intro target locals σ τ available closed formed substitutions frame
  have pair := original [] target locals σ τ available closed formed substitutions frame
    (fun _ _ member => nomatch member)
  constructor
  · intro n demand footprint observation resources
    obtain ⟨answer⟩ := pair.1 observation (fun _ _ member => nomatch member) resources
    exact ⟨answer.toSortableComputationalTransferResult⟩
  · intro n demand footprint observation resources
    obtain ⟨answer⟩ := pair.2 observation (fun _ _ member => nomatch member) resources
    exact ⟨answer.toSortableComputationalTransferResult⟩

/-- Reconstructed earlier-stage results satisfy a newer control at zero,
even when their rich queries were freshly built during semantic replay. -/
def Result.addQuietControl
    {base env : VEnv} {before declarations : List VDecl}
    {old : Name → Option InductiveSignature.NativeRecursorData}
    {first : NativeRegistryHistory base before old}
    {last : NativeRegistryHistory env declarations registry.natives}
    (continuation : NativeRegistryHistory.Prefix first last)
    (current : Name → Bool)
    (quiet : ∀ name value, base.constants name = some value → current name = false)
    (rightKnown : right.ConstantsIn base) (typeKnown : assigned.ConstantsIn base)
    (result : Result budgets env U registry target locals σ τ available left right assigned demand) :
    Result ((current, fuel) :: budgets) env U registry target locals σ τ available
      left right assigned demand where
  toSortableComputationalTransferResult := result.toSortableComputationalTransferResult
  observationBound := by
    intro filter limit member
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      change result.observation.nativeDepth current ≤ fuel
      rw [result.observation.nativeDepth_of_constants continuation current quiet rightKnown]
      exact Nat.zero_le _
    · exact result.observationBound filter limit member
  certificateBound := by
    intro filter limit member
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      change result.typeCertificate.nativeDepth current ≤ fuel
      rw [result.typeCertificate.nativeDepth_of_constants continuation current quiet typeKnown]
      exact Nat.zero_le _
    · exact result.certificateBound filter limit member

end HereditaryBudgeted
end Lean4Lean.AnchoredSource.Adapted
