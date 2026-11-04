import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedPureComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedRawBetaJoin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionStages

/-! # Pure contexts under controlled expansion

Native identity expansion inserts a recovered type. Purity of every context
entry ensures this annotation remains pure, by induction on the guard stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
namespace ProofShape

/-- Every declaration-scope annotation contains no constants or projections. -/
def PureContext (Δ : List ProofShape) : Prop := ∀ a ∈ Δ, PureLambda a

/-- A pure displayed domain extends a pure context. -/
theorem PureContext.cons (H : PureContext Δ) (HA : PureLambda A) : PureContext (A :: Δ) := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact HA
  · exact H a ha

/-- All context lookups are pure, including the default proof marker. -/
theorem PureContext.oracle (H : PureContext Δ) : PureLambda (contextOracle Δ i) := by
  induction Δ generalizing i with
  | nil => trivial
  | cons A Δ ih =>
    have HA := H A (by simp)
    have HΔ : PureContext Δ := fun a ha => H a (by simp [ha])
    cases i with
    | zero => exact HA.liftN
    | succ i => exact (ih HΔ).liftN

/-- Root purity lifts to contextual computation. Binder bodies use the pure
source annotation, as required by the contextual computation constructors. -/
theorem ScopedCompute.pure_context
    (hroot : ∀ {Δ a b}, Step Δ a b → PureContext Δ → PureLambda a → PureLambda b)
    (R : ScopedCompute Step Δ a b) (HΔ : PureContext Δ) (H : PureLambda a) : PureLambda b := by
  induction R with
  | base R => exact hroot R HΔ H
  | beta R => exact H.beta R
  | trans _ _ ihR ihS => exact ihS HΔ (ihR HΔ H)
  | app _ _ ihf ihx => exact ⟨ihf HΔ H.1, ihx HΔ H.2⟩
  | lam _ _ ihA ihB | forallE _ _ ihA ihB =>
    exact ⟨ihA HΔ H.1, ihB (HΔ.cons H.1) H.2⟩
  | proj => exact H.elim

variable [Params]
/-- Recovery cannot manufacture a constant or projection from a pure source
and pure context when its conversion roots preserve purity. -/
theorem ScopedTypeRecovery.pure_context
    (hroot : ∀ {Δ a b}, Step Δ a b → PureContext Δ → PureLambda a → PureLambda b)
    (R : ScopedTypeRecovery Step Δ a A) (HΔ : PureContext Δ) (H : PureLambda a) :
    PureLambda A := by
  induction R with
  | bvar => exact HΔ.oracle
  | sort => trivial
  | const | proj => exact H.elim
  | lam _ ih => exact ⟨H.1, ih (HΔ.cons H.1) H.2⟩
  | app _ ih => exact (ih HΔ H.1).2.inst H.2
  | forallE => trivial
  | convert _ R ih => exact R.pure_context hroot HΔ (ih HΔ H)

end ProofShape
variable [Params]

/-- All finite expanded stages preserve pure syntax in a pure context. In the
identity case the preceding-stage recovery supplies a pure binder annotation. -/
theorem erased_expansion_stage_pure_root : ∀ stage {Δ a b},
    ErasedExpansionStage D stage Δ a b → PureContext Δ → PureLambda a → PureLambda b := by
  intro stage
  induction stage with
  | zero =>
    intro Δ a b R HΔ H
    rcases R with (R | R) | R
    · exact (H.not_primitiveHead (erased_iota_primitive_head R)).elim
    · exact H.level R
    · cases R
      exact ⟨⟨trivial, H.liftN⟩, trivial⟩
  | succ stage ih =>
    intro Δ a b R HΔ H
    rcases R with R | R | R | R
    · exact ih R HΔ H
    · exact (H.not_primitiveHead R.2.head).elim
    · exact (H.not_primitiveHead R.head).elim
    · cases R with
      | intro R => exact ⟨⟨R.pure_context ih HΔ H, trivial⟩, H⟩

/-- Expanded finite computations preserve purity, despite reverse beta steps. -/
theorem erased_expansion_stage_pure_compute
    (R : ScopedCompute (ErasedExpansionStage D stage) Δ a b)
    (HΔ : PureContext Δ) (H : PureLambda a) : PureLambda b :=
  R.pure_context (erased_expansion_stage_pure_root stage) HΔ H

/-- Mixing finite expanded stages also preserves purity. -/
theorem erased_expansion_union_pure_compute
    (R : ScopedCompute (ErasedExpansionUnion D) Δ a b)
    (HΔ : PureContext Δ) (H : PureLambda a) : PureLambda b :=
  R.pure_context (fun ⟨stage, R⟩ => erased_expansion_stage_pure_root stage R) HΔ H

end Lean4Lean.VEnv.Strengthening
