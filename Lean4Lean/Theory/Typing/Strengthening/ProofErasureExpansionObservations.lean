import Lean4Lean.Theory.Typing.Strengthening.ProofShapeObservationEncoding
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionStages

/-! # Finite head observations survive every expanded guarded computation

At the empty constant interpretation, constant/projection-headed primitives have
no source observation to destroy. Universe changes preserve the observed head,
and controlled expansion preserves observations by backward beta. This invariant
covers arbitrary interleavings; it does not assert guarded confluence.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation

namespace ProofShape
/-- Finite beta-only observations of proof shapes, with an opaque proof marker. -/
def HeadObservation (S : Sets) (a : ProofShape) (o : Ob) : Prop :=
  Obs .empty S a.toObservationExpr o

/-- No constant/projection-headed spine has an observation in the empty
constant interpretation, regardless of the surrounding variable valuation. -/
theorem HeadObservation.not_primitiveHead (H : HeadObservation S a o) : ¬ PrimitiveHead a := by
  induction a generalizing S o with
  | const => exact fun _ => Obs.empty_const_false H
  | proj => exact fun _ => Obs.proj_false H
  | app f x ihf _ =>
    obtain ⟨keys, hf, _⟩ := Obs.app_inv H
    exact ihf hf
  | proof | bvar | sort | lam | forallE => exact fun h => h

/-- Forward beta preserves observations of the exact annotated proof shape. -/
theorem HeadObservation.beta_forward (H : HeadObservation S a o) (R : ProofShape.BetaRed a b) :
    HeadObservation S b o := Obs.beta_compute_forward R.toObservationExpr H

/-- Backward beta also preserves observations; its use here does not assert
that arbitrary reverse-beta steps have source-typed binder descent. -/
theorem HeadObservation.beta_backward (H : HeadObservation S b o) (R : ProofShape.BetaRed a b) :
    HeadObservation S a o := (PureObservation.BetaEta.of_beta R.toObservationExpr).obs_back H

/-- Operational adequacy yields an exact raw Pi reduct, including its actual
annotated domain and body, rather than just a semantic head label. -/
theorem HeadObservation.pi_exposure (H : HeadObservation (fun _ _ => False) a .pi) :
    ∃ A B, ProofShape.BetaRed a (.forallE A B) := by
  obtain ⟨A, B, R⟩ := Obs.pi_exposure H
  obtain ⟨b, RB, Eb⟩ := beta_of_toObservationExpr R.to_beta
  obtain ⟨A', B', rfl, _, _⟩ := toObservationExpr_forallE_inv Eb
  exact ⟨A', B', RB⟩

/-- Sort observations likewise yield literal raw sort reducts. -/
theorem HeadObservation.sort_exposure (H : HeadObservation (fun _ _ => False) a .sort) :
    ∃ u, ProofShape.BetaRed a (.sort u) := by
  obtain ⟨u, R⟩ := Obs.sort_exposure H
  obtain ⟨b, RB, Eb⟩ := beta_of_toObservationExpr R.to_beta
  cases b <;> cases Eb
  exact ⟨_, RB⟩

/-- The unused wrapper contracts by beta for every raw payload. -/
theorem constantExpansion_beta (a : ProofShape) : ProofShape.BetaRed (constantExpansion a) a := by
  simpa only [constantExpansion, ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
    ProofShape.lift_subst_cons, ProofShape.subst_id] using
    (ProofShape.BetaRed.beta (A := .sort (.succ .zero)) (b := a.liftN 1) (a := .sort .zero))

/-- Compatible computation preserves every finite observation whenever its
root primitives do. Binder annotations never have to remain syntactically fixed. -/
theorem ScopedCompute.headObservation
    (hstep : ∀ {Δ a b S o}, Step Δ a b → HeadObservation S a o → HeadObservation S b o)
    (R : ScopedCompute Step Δ a b) (H : HeadObservation S a o) : HeadObservation S b o := by
  induction R generalizing S o with
  | base R => exact hstep R H
  | beta R => exact H.beta_forward R
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ H)
  | app _ _ ihf iha =>
    obtain ⟨keys, hf, ha⟩ := Obs.app_inv H
    exact Obs.app (ihf hf) (fun key hk => iha (ha key hk))
  | proj => exact (Obs.proj_false H).elim
  | lam _ _ _ ihb =>
    obtain ⟨keys, result, hb, hle⟩ := Obs.lam_inv H
    exact Obs.sub (Obs.lam (ihb hb)) hle
  | forallE => exact Obs.sub Obs.pi (Obs.pi_inv H)
end ProofShape

variable [Params]
/-- Every expanded primitive preserves beta-only observations. Guarded source
heads are opaque, and both new expansion rules have exact reverse beta paths.
Neither source typing nor soundness of the supplied definition set is needed. -/
theorem erased_expansion_stage_headObservation : ∀ stage {Δ a b S o},
    ErasedExpansionStage D stage Δ a b → HeadObservation S a o → HeadObservation S b o := by
  intro stage
  induction stage with
  | zero =>
    intro Δ a b S o R H
    rcases R with (R | R) | R
    · exact (H.not_primitiveHead (erased_iota_primitive_head R)).elim
    · cases R with
      | sort => exact Obs.sub Obs.sort (Obs.sort_inv H)
      | const => exact (Obs.empty_const_false H).elim
    · cases R with
      | intro _ => exact H.beta_backward (constantExpansion_beta _)
  | succ stage ih =>
    intro Δ a b S o R H
    rcases R with R | R | R | R
    · exact ih R H
    · exact (H.not_primitiveHead R.2.head).elim
    · exact (H.not_primitiveHead R.head).elim
    · cases R with
      | intro _ =>
        apply H.beta_backward
        simpa only [ProofShape.inst, Nat.lt_irrefl, ↓reduceIte, ProofShape.liftN_zero] using
          (ProofShape.BetaRed.beta (b := .bvar 0))

/-- The invariant also holds over arbitrary finite guarded depth. -/
theorem erased_expansion_union_headObservation
    (R : ErasedExpansionUnion D Δ a b) (H : HeadObservation S a o) : HeadObservation S b o := by
  obtain ⟨stage, R⟩ := R
  exact erased_expansion_stage_headObservation stage R H

/-- A Pi head can be re-exposed by beta after any expanded computation from
that Pi, despite intermediate whole-Pi expansion and guarded steps. -/
theorem expansion_stage_pi_persistence
    (R : ScopedCompute (ErasedExpansionStage D stage) Δ (.forallE A B) out) :
    ∃ A' B', ProofShape.BetaRed out (.forallE A' B') :=
  (R.headObservation (erased_expansion_stage_headObservation stage) (Obs.pi (S := fun _ _ => False))).pi_exposure

/-- The same persistence holds for a sort head. -/
theorem expansion_stage_sort_persistence
    (R : ScopedCompute (ErasedExpansionStage D stage) Δ (.sort u) out) :
    ∃ v, ProofShape.BetaRed out (.sort v) :=
  (R.headObservation (erased_expansion_stage_headObservation stage) (Obs.sort (S := fun _ _ => False))).sort_exposure

/-- Pi persistence is independent of a uniform bound on all union primitives. -/
theorem expansion_union_pi_persistence
    (R : ScopedCompute (ErasedExpansionUnion D) Δ (.forallE A B) out) :
    ∃ A' B', ProofShape.BetaRed out (.forallE A' B') :=
  (R.headObservation erased_expansion_union_headObservation (Obs.pi (S := fun _ _ => False))).pi_exposure

/-- Sort persistence also holds over the full union. -/
theorem expansion_union_sort_persistence
    (R : ScopedCompute (ErasedExpansionUnion D) Δ (.sort u) out) :
    ∃ v, ProofShape.BetaRed out (.sort v) :=
  (R.headObservation erased_expansion_union_headObservation (Obs.sort (S := fun _ _ => False))).sort_exposure

end Lean4Lean.VEnv.Strengthening
