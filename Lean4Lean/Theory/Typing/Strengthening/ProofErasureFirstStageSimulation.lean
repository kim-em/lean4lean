import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeGuardMaterialization

/-! # Two remaining rule families for a first-stage simulation

Native identity and both native eta rules can materialize their guards in
written annotations. Consequently stage collapse needs induction cases only
for the singleton and Eq-prefix rules, which use comparison certificates.
Those two cases are explicit hypotheses below and are not proved here.
Even a completed simulation would still leave first-stage confluence to prove.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape PureObservation
variable [Params] {D : Definitions}

omit [Params] in
/-- Compatible computation lifts a root-step simulation to complete paths. -/
theorem scoped_compute_simulate
    (hstep : ∀ {Δ a b}, Source Δ a b → ScopedCompute Target Δ a b)
    (R : ScopedCompute Source Δ a b) : ScopedCompute Target Δ a b := by
  induction R with
  | base H => exact hstep H
  | beta H => exact .beta H
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | proj _ ih => exact .proj ih
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂

/-- Root-stage simulation reduces to the two comparison-guarded rule families.
Each missing induction case receives simulation of all lower-stage paths. No
native-recovery stability, arbitrary type coverage, or confluence is assumed.
The two hypotheses remain open; this theorem does not establish stage collapse. -/
theorem first_stage_root_simulation_of_comparison_rules
    (HS : ∀ n,
      (∀ {Δ a b}, ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) Δ a b →
        ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b) →
      ∀ {Δ a b}, CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D n) Δ a b →
        ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b)
    (HP : ∀ n,
      (∀ {Δ a b}, ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) Δ a b →
        ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b) →
      ∀ {Δ a b}, ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D n) Δ a b →
        ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b) :
    ∀ n {Δ a b}, ErasedStaticStructureEtaExpansionStage D n Δ a b →
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b := by
  intro n
  induction n with
  | zero => exact fun H => .base (.inl H)
  | succ n ih =>
    have lower : ∀ {Δ a b}, ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) Δ a b →
        ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b :=
      fun R => scoped_compute_simulate ih R
    intro Δ a b H
    rcases H with H | H | H | H | H | H
    · exact ih H
    · exact HS n lower H
    · exact HP n lower H
    · exact first_stage_native_identity_simulation lower H
    · exact first_stage_native_eta_simulation lower H
    · exact first_stage_native_structure_simulation lower H

/-- Discharging the singleton and Eq-prefix induction cases would simulate
every full-union computation in stage one, at its exact raw endpoints. This
conditional consequence includes arbitrary paths and binder scopes, rather
than only the retained-caller or contextual-eta examples. -/
theorem first_stage_union_simulation_of_comparison_rules
    (HS : ∀ n,
      (∀ {Δ a b}, ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) Δ a b →
        ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b) →
      ∀ {Δ a b}, CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D n) Δ a b →
        ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b)
    (HP : ∀ n,
      (∀ {Δ a b}, ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) Δ a b →
        ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b) →
      ∀ {Δ a b}, ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D n) Δ a b →
        ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ a b) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b :=
  scoped_compute_simulate (fun ⟨n, H⟩ => first_stage_root_simulation_of_comparison_rules HS HP n H) R

end Lean4Lean.VEnv.Strengthening
