import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedExpansionPurity

/-! # Common reducts for pure computations with controlled expansion

The expanded paths need not themselves be forward beta/universe computations.
Their endpoints nevertheless have an exact forward common reduct. Raw joins
handle reverse beta steps; typed replay realizes the final universe variation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
namespace ProofShape

/-- The constant expansion contracts to its original source. -/
theorem ConstantExpansion.beta_back (R : ConstantExpansion a b) : BetaRed b a := by
  cases R
  have E : (a.liftN 1).inst (.sort .zero) = a := by
    simp only [inst_eq_subst, Subst.liftN, Subst.one, lift_subst_cons, subst_id]
  simpa only [E] using (show BetaRed (constantExpansion a)
    ((a.liftN 1).inst (.sort .zero)) from .beta)

/-- The recovered identity annotation is discarded by its beta contraction. -/
theorem NativeIdentityExpansion.beta_back [Params]
    (R : NativeIdentityExpansion Step Δ a b) : BetaRed b a := by
  cases R
  simpa only [inst, Nat.lt_irrefl, ↓reduceIte, liftN_zero] using
    (BetaRed.beta (b := .bvar 0) (a := a))

/-- Pure contextual paths have raw join certificates whenever their roots do.
Purity preservation keeps the root hypothesis applicable after every step. -/
theorem ScopedCompute.pure_join
    (hroot : ∀ {Δ a b}, Step Δ a b → PureContext Δ → PureLambda a → PureLambda b)
    (hjoin : ∀ {Δ a b}, Step Δ a b → PureLambda a → BetaLevelJoin a b)
    (R : ScopedCompute Step Δ a b) (HΔ : PureContext Δ) (H : PureLambda a) :
    BetaLevelJoin a b := by
  induction R with
  | base R => exact hjoin R H
  | beta R => exact .beta R
  | trans R _ ihR ihS => exact (ihR HΔ H).trans (ihS HΔ (R.pure_context hroot HΔ H))
  | app _ _ ihf ihx => exact .app (ihf HΔ H.1) (ihx HΔ H.2)
  | lam _ _ ihA ihB => exact .lam (ihA HΔ H.1) (ihB (HΔ.cons H.1) H.2)
  | forallE _ _ ihA ihB => exact .forallE (ihA HΔ H.1) (ihB (HΔ.cons H.1) H.2)
  | proj => exact H.elim

end ProofShape
variable [Params]

/-- Every expanded root at a pure source is beta-joinable modulo universes.
No purity assumption on recovered annotations is needed for this root lemma. -/
theorem erased_expansion_stage_pure_root_join : ∀ stage {Δ a b},
    ErasedExpansionStage D stage Δ a b → PureLambda a → BetaLevelJoin a b := by
  intro stage
  induction stage with
  | zero =>
    intro Δ a b R H
    rcases R with (R | R) | R
    · exact (H.not_primitiveHead (erased_iota_primitive_head R)).elim
    · exact .variant R.variant
    · exact (BetaLevelJoin.beta R.beta_back).symm
  | succ stage ih =>
    intro Δ a b R H
    rcases R with R | R | R | R
    · exact ih R H
    · exact (H.not_primitiveHead R.2.head).elim
    · exact (H.not_primitiveHead R.head).elim
    · exact (BetaLevelJoin.beta R.beta_back).symm

/-- Finite expanded computations in the pure fragment admit raw joins. -/
theorem erased_expansion_stage_pure_join
    (R : ScopedCompute (ErasedExpansionStage D stage) Δ a b)
    (HΔ : PureContext Δ) (H : PureLambda a) : BetaLevelJoin a b :=
  R.pure_join (erased_expansion_stage_pure_root stage)
    (erased_expansion_stage_pure_root_join stage) HΔ H

/-- Union computations in the pure fragment admit raw joins. -/
theorem erased_expansion_union_pure_join
    (R : ScopedCompute (ErasedExpansionUnion D) Δ a b)
    (HΔ : PureContext Δ) (H : PureLambda a) : BetaLevelJoin a b :=
  R.pure_join (fun ⟨stage, R⟩ => erased_expansion_stage_pure_root stage R)
    (fun ⟨stage, R⟩ => erased_expansion_stage_pure_root_join stage R) HΔ H

/-- A raw join has exact forward beta/universe residuals when its right endpoint
has an actual typing. Source replay supplies the final universe well-formedness. -/
theorem proofErase_carrier_aligned_raw_join_realize
    (hΓ : OnCtx Γ (env.IsType univs)) (hb : env.HasType univs Γ b B)
    (H : BetaLevelJoin a (proofErase Γ b)) :
    ∃ c, ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) a c ∧
      ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) (proofErase Γ b) c := by
  obtain ⟨a', b', RA, RB, V⟩ := H
  obtain ⟨b₀, HB, EB⟩ := proofErase_scoped_compute_realize
    (Step := fun _ => LevelPrimitive univs) erased_level_primitive_descent
    hΓ hb rfl rfl (ScopedCompute.beta RB)
  have V' : StructuralVariant a' (proofErase Γ b₀) := by simpa only [EB] using V
  have RV := (proofErase_carrier_aligned_variant_level_compute V' hΓ HB.hasType.2).scoped
    (Δ := proofEraseCtx Γ) (fun R => .base R)
  exact ⟨b', (ScopedCompute.beta RA).trans (by simpa only [EB] using RV), .beta RB⟩

/-- Different finite expanded stages have forward beta/universe common reducts
at typed pure sources in pure contexts. Canonical Eq is used only for replay. -/
theorem proofErase_carrier_aligned_expansion_stage_confluent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (HΔ : PureContext (proofEraseCtx Γ)) (H : PureLambda (proofErase Γ e))
    (R : ScopedCompute (ErasedExpansionStage D n) (proofEraseCtx Γ) (proofErase Γ e) a)
    (S : ScopedCompute (ErasedExpansionStage D m) (proofEraseCtx Γ) (proofErase Γ e) b) :
    ∃ c, ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) a c ∧
      ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) b c := by
  have J := (erased_expansion_stage_pure_join R HΔ H).symm.trans
    (erased_expansion_stage_pure_join S HΔ H)
  obtain ⟨b₀, HB, EB⟩ := proofErase_scoped_compute_realize
    (erased_expansion_stage_descent heq hs m) hΓ ht rfl rfl S
  rw [← EB] at J ⊢
  exact proofErase_carrier_aligned_raw_join_realize hΓ HB.hasType.2 J

/-- Arbitrary union paths, including controlled expansions, join by forward
beta/universe computation in the typed pure fragment. -/
theorem proofErase_carrier_aligned_expansion_union_confluent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (HΔ : PureContext (proofEraseCtx Γ)) (H : PureLambda (proofErase Γ e))
    (R : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ e) a)
    (S : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ e) b) :
    ∃ c, ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) a c ∧
      ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) b c := by
  have J := (erased_expansion_union_pure_join R HΔ H).symm.trans
    (erased_expansion_union_pure_join S HΔ H)
  obtain ⟨b₀, HB, EB⟩ := proofErase_scoped_compute_realize
    (erased_expansion_union_descent heq hs) hΓ ht rfl rfl S
  rw [← EB] at J ⊢
  exact proofErase_carrier_aligned_raw_join_realize hΓ HB.hasType.2 J

end Lean4Lean.VEnv.Strengthening
