import Lean4Lean.Theory.Typing.Strengthening.NeutralObservation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionObservations

/-! # Expanded computations preserve exact variable heads

Finite neutral demands survive all expanded stages. Interpreting a demand as
beta reduction to its originating variable gives exact variable readout, even
when the path uses guarded primitives inside arbitrary expansion wrappers.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open NeutralObservation
namespace ProofShape

/-- Neutral finite observations of the exact encoded proof shape. -/
def VariableObservation (S : PureObservation.Sets) (a : ProofShape) (o : PureObservation.Ob) : Prop :=
  Obs S a.toObservationExpr o

/-- Constant/projection-headed primitives cannot destroy a neutral demand. -/
theorem VariableObservation.not_primitiveHead (H : VariableObservation S a o) : ¬ PrimitiveHead a := by
  induction a generalizing S o with
  | const | proj => exact H.neutralHead.elim
  | app f x ihf _ =>
    obtain ⟨keys, hf, _⟩ := Obs.app_inv H
    exact ihf hf
  | proof | bvar | sort | lam | forallE => exact fun h => h

/-- An observation at a single designated variable returns that exact variable
by raw beta reduction; the proof-marker encoding is not used injectively. -/
theorem VariableObservation.variable_exposure
    (H : VariableObservation (fun k o => k = i ∧ o = .pi) a .pi) :
    ProofShape.BetaRed a (.bvar i) := by
  obtain ⟨b, RB, Eb⟩ := beta_of_toObservationExpr (Obs.variable_exposure H)
  cases b <;> cases Eb
  exact RB

/-- The finite identity demand reflects to an exact raw beta path for every
argument, including proof markers and actual anonymous constants. -/
theorem VariableObservation.identity_behavior
    (H : VariableObservation (fun _ _ => False) f (.app [.pi] .pi)) (a : ProofShape) :
    ProofShape.BetaRed (.app f a) a :=
  beta_toObservationExpr_iff.1 (Obs.identity_behavior H a.toObservationExpr)

/-- Compatible computation preserves neutral demands whenever its primitive
roots do. No well-formedness or interpretation of the raw context is required. -/
theorem ScopedCompute.variableObservation
    (hstep : ∀ {Δ a b S o}, Step Δ a b → VariableObservation S a o → VariableObservation S b o)
    (R : ScopedCompute Step Δ a b) (H : VariableObservation S a o) : VariableObservation S b o := by
  induction R generalizing S o with
  | base R => exact hstep R H
  | beta R => exact Obs.beta_compute_forward R.toObservationExpr H
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ H)
  | app _ _ ihf iha =>
    obtain ⟨keys, hf, ha⟩ := Obs.app_inv H
    exact Obs.app (ihf hf) (fun key hk => iha (ha key hk))
  | proj | forallE => exact H.neutralHead.elim
  | lam _ _ _ ihb =>
    obtain ⟨keys, result, hb, hle⟩ := Obs.lam_inv H
    exact Obs.sub (Obs.lam (ihb hb)) hle
end ProofShape

variable [Params]
/-- Root expansions preserve the existing neutral demand directly. All other
primitive roots are opaque to this observation relation. -/
theorem erased_expansion_stage_variableObservation : ∀ stage {Δ a b S o},
    ErasedExpansionStage D stage Δ a b → VariableObservation S a o → VariableObservation S b o := by
  intro stage
  induction stage with
  | zero =>
    intro Δ a b S o R H
    rcases R with (R | R) | R
    · exact (H.not_primitiveHead (erased_iota_primitive_head R)).elim
    · cases R <;> exact H.neutralHead.elim
    · cases R with
      | intro _ =>
        simpa only [VariableObservation, constantExpansion, toObservationExpr,
          toObservationExpr_liftN, VExpr.lift] using H.constant_expansion
  | succ stage ih =>
    intro Δ a b S o R H
    rcases R with R | R | R | R
    · exact ih R H
    · exact (H.not_primitiveHead R.2.head).elim
    · exact (H.not_primitiveHead R.head).elim
    · cases R with
      | intro _ => exact H.identity_expansion

/-- Every union primitive has some finite stage preserving the demand. -/
theorem erased_expansion_union_variableObservation
    (R : ErasedExpansionUnion D Δ a b) (H : VariableObservation S a o) : VariableObservation S b o := by
  obtain ⟨stage, R⟩ := R
  exact erased_expansion_stage_variableObservation stage R H

/-- Any finite expanded computation from a variable has a beta path back to
that same variable. Constants, projections and arbitrary guarded depth cannot
change the result; no purity restriction is placed on intermediate syntax. -/
theorem expansion_stage_variable_persistence
    (R : ScopedCompute (ErasedExpansionStage D stage) Δ (.bvar i) out) :
    ProofShape.BetaRed out (.bvar i) := by
  have H : VariableObservation (fun k o => k = i ∧ o = .pi) (.bvar i) .pi :=
    Obs.var ⟨rfl, rfl⟩
  exact (R.variableObservation (erased_expansion_stage_variableObservation stage) H).variable_exposure

/-- Exact variable readout also holds for paths with unbounded finite guard depth. -/
theorem expansion_union_variable_persistence
    (R : ScopedCompute (ErasedExpansionUnion D) Δ (.bvar i) out) :
    ProofShape.BetaRed out (.bvar i) := by
  have H : VariableObservation (fun k o => k = i ∧ o = .pi) (.bvar i) .pi :=
    Obs.var ⟨rfl, rfl⟩
  exact (R.variableObservation erased_expansion_union_variableObservation H).variable_exposure

/-- Computed variable outputs remain beta-identical after every raw substitution.
No native image recovery, source typing or primitive substitution law is needed. -/
theorem expansion_union_variable_subst_beta
    (R : ScopedCompute (ErasedExpansionUnion D) Δ (.bvar i) out) :
    ProofShape.BetaRed (out.subst σ) (σ i) :=
  (expansion_union_variable_persistence R).subst

/-- A computed identity function still beta-returns every supplied argument.
The computation may change its annotation, body and outer constructor, and may
use arbitrary guarded stages. No native certificate is needed for the argument. -/
theorem expansion_union_identity_behavior
    (R : ScopedCompute (ErasedExpansionUnion D) Δ (.lam A (.bvar 0)) out) (a : ProofShape) :
    ProofShape.BetaRed (.app out a) a := by
  have H : VariableObservation (fun _ _ => False) (.lam A (.bvar 0)) (.app [.pi] .pi) :=
    Obs.lam (Obs.var (by simp [PureObservation.Sets.cons]))
  exact (R.variableObservation erased_expansion_union_variableObservation H).identity_behavior a

/-- Finite-stage identity readout has the same exact beta target. -/
theorem expansion_stage_identity_behavior
    (R : ScopedCompute (ErasedExpansionStage D stage) Δ (.lam A (.bvar 0)) out) (a : ProofShape) :
    ProofShape.BetaRed (.app out a) a :=
  expansion_union_identity_behavior (R.mono (fun H => ⟨stage, H⟩)) a

/-- After independent computation of an entire identity function and its
argument, the application beta-reduces to the computed argument. This closes
the wrapper square without stage growth, even if argument recovery was lost. -/
theorem expansion_identity_function_argument_square
    (RF : ScopedCompute (ErasedExpansionStage D n) Δ (.lam A (.bvar 0)) outF)
    (RX : ScopedCompute (ErasedExpansionStage D m) Δ x outX) :
    ScopedCompute (ErasedExpansionStage D m) Δ x outX ∧
      ProofShape.BetaRed (.app outF outX) outX :=
  ⟨RX, expansion_stage_identity_behavior RF outX⟩

/-- Even after the outer wrapper beta step has already fired, a computed body
from the bound variable returns the exact argument by beta. This uses only raw
beta substitution, not substitution of any guarded primitive. -/
theorem expansion_union_identity_contractum_beta
    (RB : ScopedCompute (ErasedExpansionUnion D) Δ (.bvar 0) outB) (a : ProofShape) :
    ProofShape.BetaRed (outB.inst a) a := by
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
    ProofShape.Subst.one, ProofShape.Subst.cons] using
    (expansion_union_variable_subst_beta (σ := ProofShape.Subst.one a) RB)

/-- The repaired wrapper square supplies a comparison in either mode at the
argument computation's relation. The identity function may have evolved through
the full expanded union; its guard depth does not enter the target certificate. -/
theorem expansion_union_identity_comparison
    (RF : ScopedCompute (ErasedExpansionUnion D) Δf (.lam A (.bvar 0)) outF)
    (RX : ScopedCompute Step Δ x outX) :
    ComputedJointCompare Step Δ mode x (.app outF outX) :=
  .compute RX (.beta (expansion_union_identity_behavior RF outX)) (.leaf .refl)

/-- The same comparison is available after the identity wrapper's outer beta
step has fired. Only its computed body must originate at the bound variable. -/
theorem expansion_union_identity_contractum_comparison
    (RB : ScopedCompute (ErasedExpansionUnion D) Δb (.bvar 0) outB)
    (RX : ScopedCompute Step Δ x outX) :
    ComputedJointCompare Step Δ mode x (outB.inst outX) :=
  .compute RX (.beta (expansion_union_identity_contractum_beta RB outX)) (.leaf .refl)

end Lean4Lean.VEnv.Strengthening
