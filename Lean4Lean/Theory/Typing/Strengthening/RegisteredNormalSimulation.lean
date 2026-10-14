import Lean4Lean.Theory.Typing.Strengthening.StructureLevelCompatibility
import Lean4Lean.Theory.Typing.Strengthening.NormalPrefixFactorization

/-! # Normal transport over the actual deterministic equations

Universe compatibility replaces exact saturation, so transport uses the same
stored and selected structure equations as exact computational confluence.
Checked prefixes still require the witnessed proposition-descent hypothesis.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

private abbrev actualD : Definitions :=
  RegisteredStructure.definitions (Definitions.ofEnv env univs henv)

/-- Normal comparison transports arbitrary finite pattern computation over the
actual deterministic equations. No canonical Eq or witnessed front is used. -/
theorem normal_registered_pattern_simulation
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEqF η Γ a b) (R : PatternCompute actualD b b') :
    ∃ a', PatternCompute actualD a a' ∧ NormalEq Γ a' b' :=
  normal_pattern_simulation_compatible
    (RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv))
    (RegisteredStructure.definitions_ofEnv_levelCompatible hcon) hcon hΓ H R

/-- Conditional prefix transport now uses exactly the deterministic equation
collection, without enlarging it by universe saturation. The witnessed front
is still required for fresh-binder prefix reflection. -/
theorem normal_registered_prefix_simulation (heq : env.HasCanonicalEq)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEqF η Γ a b) (R : PrefixCompute actualD Γ b b') :
    ∃ a', PrefixCompute actualD Γ a a' ∧ NormalEq Γ a' b' :=
  normal_prefix_simulation_compatible heq
    (RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv))
    (RegisteredStructure.definitions_ofEnv_levelCompatible hcon) hfront hcon hΓ H R

/-- The pattern/prefix/function-eta fragment factors using the actual stored and
selected structure equations. Structure eta in the input and descent of opaque
normal domains remain outside this theorem. -/
theorem TypedPrefixEta.factor_registered (heq : env.HasCanonicalEq)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (R : TypedPrefixEta actualD Γ a b) (ht : env.HasType univs Γ a T) :
    PrefixNormal actualD Γ a b :=
  R.factor_compatible heq hfront
    (RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv))
    (RegisteredStructure.definitions_ofEnv_levelCompatible hcon) hcon hΓ ht

end Lean4Lean.VEnv.Strengthening.PureObservation
