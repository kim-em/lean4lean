import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedNativeGuardMaterialization

/-! # Typed first-stage simulation from the two comparison cases

The remaining cases are asked only at actual typed sources in their actual
contexts. Source descent realizes intermediates, and native materialization
needs only typed lower-stage simulation. The singleton and Eq-prefix cases
remain explicit open hypotheses; even collapse would still leave confluence.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Root-stage simulation reduces to the two comparison-guarded rule families.
Each missing induction case receives simulation of all typed lower-stage paths
and a witness for its own source. No native-recovery stability, arbitrary type coverage, or confluence is assumed.
The two hypotheses remain open; this theorem does not establish stage collapse. -/
theorem first_stage_typed_root_simulation_of_comparison_rules
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HS : ∀ n,
      (∀ {Δ a b}, TypedSource Δ a → ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) Δ a b →
        ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b) →
      ∀ {Δ a b}, TypedSource Δ a → CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D n) Δ a b →
        ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b)
    (HP : ∀ n,
      (∀ {Δ a b}, TypedSource Δ a → ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) Δ a b →
        ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b) →
      ∀ {Δ a b}, TypedSource Δ a → ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D n) Δ a b →
        ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b) :
    ∀ n {Δ a b}, TypedSource Δ a → ErasedStaticStructureEtaExpansionStage D n Δ a b →
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b := by
  intro n
  induction n with
  | zero => exact fun _ H => .base (.inl H)
  | succ n ih =>
    have lower : ∀ {Δ a b}, TypedSource Δ a → ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) Δ a b →
        ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b :=
      fun HT R => scoped_compute_simulate_typed
        (erased_static_structure_eta_expansion_stage_descent heq hs n) ih R HT
    intro Δ a b HT H
    rcases H with H | H | H | H | H | H
    · exact ih HT H
    · exact HS n lower HT H
    · exact HP n lower HT H
    · exact first_stage_native_identity_simulation_typed
        (erased_static_structure_eta_expansion_stage_descent heq hs n) lower H HT
    · exact first_stage_native_eta_simulation_typed
        (erased_static_structure_eta_expansion_stage_descent heq hs n) lower H HT
    · exact first_stage_native_structure_simulation_typed
        (erased_static_structure_eta_expansion_stage_descent heq hs n) lower H HT

/-- Discharging the singleton and Eq-prefix induction cases would simulate
every typed full-union computation in stage one, at its exact raw endpoints. This
conditional consequence includes arbitrary paths and binder scopes, provided
the source has an actual typed realization. -/
theorem first_stage_typed_union_simulation_of_comparison_rules
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HS : ∀ n,
      (∀ {Δ a b}, TypedSource Δ a → ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) Δ a b →
        ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b) →
      ∀ {Δ a b}, TypedSource Δ a → CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D n) Δ a b →
        ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b)
    (HP : ∀ n,
      (∀ {Δ a b}, TypedSource Δ a → ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) Δ a b →
        ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b) →
      ∀ {Δ a b}, TypedSource Δ a → ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D n) Δ a b →
        ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ a b)
    (HT : TypedSource Δ a) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b :=
  scoped_compute_simulate_typed (erased_static_structure_eta_expansion_union_descent heq hs)
    (fun HT ⟨n, H⟩ => first_stage_typed_root_simulation_of_comparison_rules heq hs HS HP n HT H) R HT

end Lean4Lean.VEnv.Strengthening
