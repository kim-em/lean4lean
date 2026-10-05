import Lean4Lean.Theory.Inductive.SaturatedNativeProgram
import Lean4Lean.Theory.Inductive.CaseReductionData
import Lean4Lean.Theory.DeclarationData

/-! One concrete registry shared by legacy and ordinary-data head dispatch.
Only syntax and closure evidence occur in this low-level module. -/
namespace Lean4Lean.CanonicalDataHead
open InductiveSignature
structure CaseEntry where
  schema : CaseSchema
  owner : Fin schema.signature.families.size
end Lean4Lean.CanonicalDataHead

namespace Lean4Lean.CanonicalHead
open InductiveSignature
structure Registry where
  definitions : Name → Option VDefVal
  natives : Name → Option NativeRecursorData
  cases : Name → Nat → Option CanonicalDataHead.CaseEntry := fun _ _ => none
  projections : Name → Option VProjectionInfo := fun _ => none
  structureConstructors : Name → Option VProjectionEntry := fun _ => none
  quotient : Bool := false

/-- Each closure field is produced from the corresponding registered original
header/equation. It does not certify a reduction's semantic guards. -/
structure Registry.Scoped (registry : Registry) : Prop where
  definition : ∀ name value, registry.definitions name = some value → value.value.Closed
  native : ∀ name data, registry.natives name = some data →
    ∀ equation, data.singletonEquation = some equation → equation.rhs.Closed
  nativeEquation : ∀ name data, registry.natives name = some data →
    ∀ index equation,
      data.schema.restoration.equation (data.nativeInstance.equation index) = some equation →
      equation.rhs.Closed
  caseEquation : ∀ block owner entry, registry.cases block owner = some entry →
    ∀ rule, entry.schema.Generates block entry.owner rule → rule.equation.rhs.Closed

abbrev Registry.toRegistry (registry : Registry) : Registry := registry
abbrev Registry.Scoped.base {registry : Registry} (scope : registry.Scoped) : registry.Scoped := scope
end Lean4Lean.CanonicalHead

namespace Lean4Lean.CanonicalDataHead
abbrev Registry := CanonicalHead.Registry
abbrev Registry.Scoped (registry : Registry) := CanonicalHead.Registry.Scoped registry

/-- A declaration head whose name cannot also select a computational rule.
Unlike one stopped argument spine, these concrete registry facts survive
substitution of proof inhabitants into its arguments. -/
structure HeadInert (registry : Registry) (name : Name) : Prop where
  definition : registry.definitions name = none
  native : registry.natives name = none
  quotient : registry.quotient = false ∨ name ≠ ``Quot.lift
end Lean4Lean.CanonicalDataHead
