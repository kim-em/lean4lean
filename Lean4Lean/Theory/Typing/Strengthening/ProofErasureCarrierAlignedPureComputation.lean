import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedBetaLevelJoin

/-! # Guarded computation on syntax without constants or projections

Only beta reduction and universe conversion can act in this syntax. This
property is preserved by reduction, so no guarded rule can become enabled after
a preceding beta contraction. The statement holds at every finite stage and
at the union, independently of the number of nested guards elsewhere.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
namespace ProofShape

/-- Raw lambda calculus with sorts, proof markers and Pis, but no constants or
projections. It includes open terms, arbitrary applications and retained domains. -/
def PureLambda : ProofShape → Prop
  | .const .. | .proj .. => False
  | .app f a | .lam f a | .forallE f a => PureLambda f ∧ PureLambda a
  | _ => True

/-- Lifting does not introduce constants or projections. -/
theorem PureLambda.liftN (H : PureLambda a) : PureLambda (a.liftN n k) := by
  induction a generalizing k <;> simp_all [PureLambda, ProofShape.liftN]

/-- Instantiation by syntax in the same grammar stays in the grammar. -/
theorem PureLambda.inst (H : PureLambda a) (HX : PureLambda x) : PureLambda (a.inst x k) := by
  induction a generalizing k <;> simp_all [PureLambda, ProofShape.inst]
  split <;> simp_all [PureLambda]
  split
  · exact HX.liftN
  · trivial

/-- A beta path cannot introduce a constant or projection absent from its source. -/
theorem PureLambda.beta (H : PureLambda a) (R : BetaRed a b) : PureLambda b := by
  induction R with
  | refl => exact H
  | trans _ _ ihR ihS => exact ihS (ihR H)
  | app _ _ ihf ihx | lam _ _ ihf ihx | forallE _ _ ihf ihx => exact ⟨ihf H.1, ihx H.2⟩
  | proj => exact H.elim
  | beta => exact H.1.2.inst H.2

/-- No primitive constant/projection head occurs in this grammar. -/
theorem PureLambda.not_primitiveHead (H : PureLambda a) : ¬ PrimitiveHead a := by
  induction a <;> simp_all [PureLambda, PrimitiveHead]

/-- Universe conversion preserves the grammar. -/
theorem PureLambda.level (H : PureLambda a) (R : LevelPrimitive U a b) : PureLambda b := by
  cases R with
  | sort => trivial
  | const => exact H.elim

/-- A root law splits all computation into old primitive heads and level steps.
On pure syntax every old root is impossible, even after beta creates new redexes. -/
theorem ScopedCompute.pure_levels
    (hroot : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a ∨ LevelPrimitive U a b)
    (R : ScopedCompute Step Δ a b) (H : PureLambda a) :
    PureLambda b ∧ ScopedCompute (fun _ => LevelPrimitive U) Δ a b := by
  induction R with
  | base R =>
    rcases hroot R with hn | HL
    · exact (H.not_primitiveHead hn).elim
    · exact ⟨H.level HL, .base HL⟩
  | beta R => exact ⟨H.beta R, .beta R⟩
  | trans R S ihR ihS =>
    obtain ⟨H', R'⟩ := ihR H
    obtain ⟨H'', S'⟩ := ihS H'
    exact ⟨H'', R'.trans S'⟩
  | app _ _ ihf ihx =>
    obtain ⟨HF, RF⟩ := ihf H.1
    obtain ⟨HX, RX⟩ := ihx H.2
    exact ⟨⟨HF, HX⟩, .app RF RX⟩
  | lam _ _ ihA ihB =>
    obtain ⟨HA, RA⟩ := ihA H.1
    obtain ⟨HB, RB⟩ := ihB H.2
    exact ⟨⟨HA, HB⟩, .lam RA RB⟩
  | forallE _ _ ihA ihB =>
    obtain ⟨HA, RA⟩ := ihA H.1
    obtain ⟨HB, RB⟩ := ihB H.2
    exact ⟨⟨HA, HB⟩, .forallE RA RB⟩
  | proj => exact H.elim

end ProofShape
variable [Params]

/-- Every finite guarded stage collapses to beta/universe computation on this
syntax; the result remains in the grammar. -/
theorem erased_level_recovered_stage_pure_compute
    (R : ScopedCompute (ErasedLevelRecoveredStage D stage) Δ a b) (H : PureLambda a) :
    PureLambda b ∧ ScopedCompute (fun _ => LevelPrimitive univs) Δ a b :=
  R.pure_levels (erased_level_recovered_stage_root stage) H

/-- The same collapse holds across paths mixing arbitrarily many finite stages. -/
theorem erased_level_recovered_union_pure_compute
    (R : ScopedCompute (ErasedLevelRecoveredUnion D) Δ a b) (H : PureLambda a) :
    PureLambda b ∧ ScopedCompute (fun _ => LevelPrimitive univs) Δ a b :=
  R.pure_levels (fun ⟨stage, H⟩ => erased_level_recovered_stage_root stage H) H

/-- At a typed pure source, computations from any two finite guarded stages
have a common reduct using only beta and universe steps. -/
theorem proofErase_carrier_aligned_pure_stage_confluent
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (HP : PureLambda (proofErase Γ e))
    (R : ScopedCompute (ErasedLevelRecoveredStage D n) (proofEraseCtx Γ) (proofErase Γ e) a)
    (S : ScopedCompute (ErasedLevelRecoveredStage D m) (proofEraseCtx Γ) (proofErase Γ e) b) :
    ∃ c, ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) a c ∧
      ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) b c :=
  proofErase_carrier_aligned_beta_level_confluent hΓ ht
    (erased_level_recovered_stage_pure_compute R HP).2
    (erased_level_recovered_stage_pure_compute S HP).2

/-- Guarded union computation is confluent at every typed pure source. The
residual paths require no singleton/Eq guard and no termination assumption. -/
theorem proofErase_carrier_aligned_pure_union_confluent
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (HP : PureLambda (proofErase Γ e))
    (R : ScopedCompute (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ e) a)
    (S : ScopedCompute (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ e) b) :
    ∃ c, ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) a c ∧
      ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) b c :=
  proofErase_carrier_aligned_beta_level_confluent hΓ ht
    (erased_level_recovered_union_pure_compute R HP).2
    (erased_level_recovered_union_pure_compute S HP).2

end Lean4Lean.VEnv.Strengthening
