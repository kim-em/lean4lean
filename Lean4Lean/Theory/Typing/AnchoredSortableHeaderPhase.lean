import Lean4Lean.Theory.Typing.AnchoredSortableStageBudgets
import Lean4Lean.Theory.Typing.DefinitionDeclarationProvenance

/-! Declaration fuel is local to a header phase. Caller controls are quiet
on a genuine completed prefix containing the original source syntax. The
single active control need not be quiet there. Recontrol below selects fuel
from the actual query and retained context; it never reinterprets a returned
observer or claims an all-budget theorem after equations are installed. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

namespace HereditaryBudgeted

/-- Every caller control ignores the constants of this completed prefix. -/
def Quiet (base : VEnv) (budgets : Budgets) : Prop :=
  ∀ current fuel, (current, fuel) ∈ budgets →
    ∀ name value, base.constants name = some value → current name = false

/-- This is the fuel-indexed theorem proved before the current equations
are installed. It does not assert arbitrary-control preservation. -/
def HeaderControlled (current : Name → Bool) (env : VEnv)
    (registry : CanonicalHead.Registry) (context : ContextDerivation sourceEnv U source)
    (original : Derivation sourceEnv U source left right assigned) : Prop :=
  ∀ fuel, FundamentalAt [(current, fuel)] env registry context original

/-- The completed-prefix theorem admits only quiet caller controls. -/
def Completed (base env : VEnv) (registry : CanonicalHead.Registry)
    (context : ContextDerivation sourceEnv U source)
    (original : Derivation sourceEnv U source left right assigned) : Prop :=
  ∀ budgets, Quiet base budgets → FundamentalAt budgets env registry context original

/-- The header carries exactly one active control in addition to the quiet
caller controls. The completed provenance envelope may contain its equations;
only the *source* environment of the controlled theorem is the header. -/
def HeaderPhase (base : VEnv) (current : Name → Bool) (env : VEnv)
    (registry : CanonicalHead.Registry) (context : ContextDerivation sourceEnv U source)
    (original : Derivation sourceEnv U source left right assigned) : Prop :=
  ∀ budgets, Quiet base budgets → ∀ fuel,
    FundamentalAt ((current, fuel) :: budgets) env registry context original

variable {base env sourceEnv : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {before declarations : List VDecl} {old : Name → Option InductiveSignature.NativeRecursorData}
  {first : NativeRegistryHistory base before old}
  {last : NativeRegistryHistory env declarations registry.natives}
  {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
  {left right assigned : VExpr} {demand : Profile n} {budgets : Budgets}

/-- Change only the budget proofs on an actual computed rich answer. -/
def Result.quietBudgets
    (continuation : NativeRegistryHistory.Prefix first last)
    (quiet : Quiet base budgets)
    (rightKnown : right.ConstantsIn base) (typeKnown : assigned.ConstantsIn base)
    (result : SortableComputationalTransferResult env U registry target locals σ τ available
      left right assigned demand) :
    Result budgets env U registry target locals σ τ available left right assigned demand where
  toSortableComputationalTransferResult := result
  observationBound := by
    intro current fuel member
    change result.observation.nativeDepth current ≤ fuel
    rw [result.observation.nativeDepth_of_constants continuation current
      (quiet current fuel member) rightKnown]
    exact Nat.zero_le _
  certificateBound := by
    intro current fuel member
    change result.typeCertificate.nativeDepth current ≤ fuel
    rw [result.typeCertificate.nativeDepth_of_constants continuation current
      (quiet current fuel member) typeKnown]
    exact Nat.zero_le _

/-- Restore quiet caller bounds without changing the active-control answer. -/
def Result.addQuietBudgets
    (continuation : NativeRegistryHistory.Prefix first last)
    (quiet : Quiet base budgets)
    (rightKnown : right.ConstantsIn base) (typeKnown : assigned.ConstantsIn base)
    (result : Result [(current, fuel)] env U registry target locals σ τ available
      left right assigned demand) :
    Result ((current, fuel) :: budgets) env U registry target locals σ τ available
      left right assigned demand where
  toSortableComputationalTransferResult := result.toSortableComputationalTransferResult
  observationBound := by
    intro filter limit member
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact result.observationBound _ _ List.mem_cons_self
    · exact (Result.quietBudgets continuation quiet rightKnown typeKnown
        result.toSortableComputationalTransferResult).observationBound _ _ member
  certificateBound := by
    intro filter limit member
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact result.certificateBound _ _ List.mem_cons_self
    · exact (Result.quietBudgets continuation quiet rightKnown typeKnown
        result.toSortableComputationalTransferResult).certificateBound _ _ member

/-- The same actual stack and input observer have one finite active fuel.
The theorem is pointwise in the request, so no maximum over future queries is
needed and no new context certificate is selected. -/
theorem HeaderControlled.complete
    {context : ContextDerivation sourceEnv U source}
    {original : Derivation sourceEnv U source left right assigned}
    (continuation : NativeRegistryHistory.Prefix first last)
    (sourceBelow : sourceEnv ≤ base)
    (controlled : HeaderControlled current env registry context original) :
    Completed base env registry context original := by
  intro budgets quiet target locals σ τ available closed formed substitutions frame frameBound
  have leftKnown := original.forget.constantsIn.1.mono sourceBelow
  have rightKnown := original.forget.constantsIn.2.mono sourceBelow
  have typeKnown := original.forget.typeConstantsIn.mono sourceBelow
  constructor
  · intro n demand footprint observation bounded resources
    let fuel := max (frame.nativeDepth current) (observation.nativeDepth current)
    have fitted : Within [(current, fuel)] frame.nativeDepth := by
      intro filter limit member
      cases List.mem_singleton.mp member
      exact Nat.le_max_left _ _
    have inputBound : Within [(current, fuel)] observation.nativeDepth := by
      intro filter limit member
      cases List.mem_singleton.mp member
      exact Nat.le_max_right _ _
    obtain ⟨result⟩ := (controlled fuel target locals σ τ available closed formed substitutions
      frame fitted).1 observation inputBound resources
    exact ⟨Result.quietBudgets continuation quiet rightKnown typeKnown
      result.toSortableComputationalTransferResult⟩
  · intro n demand footprint observation bounded resources
    let fuel := max (frame.nativeDepth current) (observation.nativeDepth current)
    have fitted : Within [(current, fuel)] frame.nativeDepth := by
      intro filter limit member
      cases List.mem_singleton.mp member
      exact Nat.le_max_left _ _
    have inputBound : Within [(current, fuel)] observation.nativeDepth := by
      intro filter limit member
      cases List.mem_singleton.mp member
      exact Nat.le_max_right _ _
    obtain ⟨result⟩ := (controlled fuel target locals σ τ available closed formed substitutions
      frame fitted).2 observation inputBound resources
    exact ⟨Result.quietBudgets continuation quiet leftKnown typeKnown
      result.toSortableComputationalTransferResult⟩

/-- The caller-budget portion of the header induction follows from source
provenance. Only the single-control theorem contains a fuel recursion. -/
theorem HeaderControlled.phase
    {context : ContextDerivation sourceEnv U source}
    {original : Derivation sourceEnv U source left right assigned}
    (continuation : NativeRegistryHistory.Prefix first last)
    (sourceBelow : sourceEnv ≤ base)
    (controlled : HeaderControlled current env registry context original) :
    HeaderPhase base current env registry context original := by
  intro budgets quiet fuel target locals σ τ available closed formed substitutions frame frameBound
  have fitted : Within [(current, fuel)] frame.nativeDepth := by
    intro filter limit member
    cases List.mem_singleton.mp member
    exact frameBound _ _ List.mem_cons_self
  have pair := controlled fuel target locals σ τ available closed formed substitutions frame fitted
  constructor
  · intro n demand footprint observation bounded resources
    obtain ⟨result⟩ := pair.1 observation (by
      intro filter limit member
      cases List.mem_singleton.mp member
      exact bounded _ _ List.mem_cons_self) resources
    exact ⟨result.addQuietBudgets continuation quiet
      (original.forget.constantsIn.2.mono sourceBelow)
      (original.forget.typeConstantsIn.mono sourceBelow)⟩
  · intro n demand footprint observation bounded resources
    obtain ⟨result⟩ := pair.2 observation (by
      intro filter limit member
      cases List.mem_singleton.mp member
      exact bounded _ _ List.mem_cons_self) resources
    exact ⟨result.addQuietBudgets continuation quiet
      (original.forget.constantsIn.1.mono sourceBelow)
      (original.forget.typeConstantsIn.mono sourceBelow)⟩

/-- An earlier completed header is usable under a newer active control.
The original proof stays in its actual earlier environment, and the new
control is justified by freshness rather than a same-fuel recursive call. -/
theorem HeaderControlled.recontrol
    {context : ContextDerivation sourceEnv U source}
    {original : Derivation sourceEnv U source left right assigned}
    (continuation : NativeRegistryHistory.Prefix first last)
    (sourceBelow : sourceEnv ≤ base)
    (quiet : ∀ name value, base.constants name = some value → current name = false)
    (controlled : HeaderControlled oldControl env registry context original) :
    HeaderControlled current env registry context original := by
  intro fuel
  apply controlled.complete continuation sourceBelow [(current, fuel)]
  intro filter limit member
  cases List.mem_singleton.mp member
  exact quiet

/-- Definition freshness supplies the younger control in the exact earlier
base, irrespective of the size of its generated constant-header prefix. -/
theorem HeaderControlled.beforeDefinition
    {context : ContextDerivation base U source}
    {original : Derivation base U source left right assigned}
    {value : VDefVal}
    (continuation : NativeRegistryHistory.Prefix first last)
    (origin : DefinitionDeclarationOrigin env declarations value)
    (sameBase : origin.base = base)
    (controlled : HeaderControlled oldControl env registry context original) :
    HeaderControlled origin.current env registry context original := by
  apply controlled.recontrol continuation VEnv.LE.rfl ?_
  intro name constant present
  apply origin.current_old
  simpa only [sameBase] using present

end HereditaryBudgeted
end Lean4Lean.AnchoredSource.Adapted
