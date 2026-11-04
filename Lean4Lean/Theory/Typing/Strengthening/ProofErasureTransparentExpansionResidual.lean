import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionBetaSquares
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedJoinSubstitution

/-! # Substitution residuals for beta-transparent expansions

Universe changes and constant/native identity expansions have raw joins before
any image recovery is considered. Their entire compatible closure therefore
substitutes up to a common reduct, for arbitrary terms and contexts. Singleton
and Eq-prefix computation remain outside this argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- The computational edits whose effect is a raw beta/universe join. Recovery
may use an arbitrary relation; its certificate is discarded with the wrapper. -/
def ErasedTransparentExpansion (Recovery : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  LevelPrimitive univs a b ∨ ConstantExpansion a b ∨ NativeIdentityExpansion Recovery Δ a b

/-- Every transparent root has a raw join, regardless of the source syntax,
context purity, or the relation used in its native recovery guard. -/
theorem erased_transparent_expansion_join
    (R : ErasedTransparentExpansion Recovery Δ a b) : BetaLevelJoin a b := by
  rcases R with R | R | R
  · exact .variant R.variant
  · exact (BetaLevelJoin.beta R.beta_back).symm
  · exact (BetaLevelJoin.beta R.beta_back).symm

omit [Params] in
/-- Compatible computation preserves raw joins when every primitive does.
This includes arbitrary intermediate terms and changing binder annotations. -/
theorem ProofShape.ScopedCompute.raw_level_join
    (hroot : ∀ {Δ a b}, Step Δ a b → BetaLevelJoin a b)
    (R : ScopedCompute Step Δ a b) : BetaLevelJoin a b := by
  induction R with
  | base R => exact hroot R
  | beta R => exact .beta R
  | trans _ _ ihR ihS => exact ihR.trans ihS
  | app _ _ ihR ihS => exact ihR.app ihS
  | lam _ _ ihR ihS => exact ihR.lam ihS
  | forallE _ _ ihR ihS => exact ihR.forallE ihS
  | proj _ ih => exact ih.proj

/-- Transparent roots guarded by the full expanded union already belong to
that union. No extra computational rule is introduced by isolating them. -/
theorem erased_transparent_into_expansion_union
    (R : ErasedTransparentExpansion (ErasedExpansionUnion D) Δ a b) :
    ErasedExpansionUnion D Δ a b := by
  rcases R with R | R | R
  · exact ⟨0, .inl (.inr R)⟩
  · exact ⟨0, .inr R⟩
  · exact erased_expansion_union_iff.2 (.inr (.inr (.inr R)))

/-- A whole transparent path substitutes up to an exact common reduct using
only beta and universe steps. The actual substitution need not supply native
images, and neither its terms nor either context must be pure. -/
theorem proofErase_transparent_compute_subst_join
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedTransparentExpansion Recovery) (proofEraseCtx Γ)
      (proofErase Γ e) out) :
    ∃ shared, ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ₀)
        (proofErase Γ₀ (e.subst σ)) shared ∧
      ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ₀) (out.subst τ) shared := by
  have H := (R.raw_level_join erased_transparent_expansion_join).subst (σ := τ)
  rw [← proofErase_subst_with hΓ₀ W ht ES] at H
  obtain ⟨shared, RR, RL⟩ := proofErase_carrier_aligned_raw_join_realize hΓ₀
    (ht.subst henv.orderedStrong W hΓ₀) H.symm
  exact ⟨shared, RL, RR⟩

/-- Whole transparent function computation and arbitrary controlled argument
computation commute with head beta up to a common residual. No recovery of the
original or computed argument is needed. The function's source may contain
constants, projections, or arbitrary dependent bodies and annotations. -/
theorem proofErase_transparent_function_beta_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (RF : ScopedCompute (ErasedTransparentExpansion Recovery) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) outF)
    (RX : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ∃ shared, ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) shared ∧
      ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) (.app outF outX) shared := by
  obtain ⟨x', HX, EX⟩ := proofErase_scoped_compute_realize
    (erased_expansion_union_descent heq hs) hΓA.1 hx rfl rfl RX
  have JF := RF.raw_level_join erased_transparent_expansion_join
  have JB : BetaLevelJoin
      ((proofErase (A :: Γ) b).inst outX) (.app outF outX) :=
    (BetaLevelJoin.beta (ProofShape.BetaRed.beta (A := proofErase Γ A))).symm.trans (JF.app .refl)
  have EI := proofErase_instN hΓA HX.hasType.2 Ctx.InstN.zero hb
  rw [EX] at EI
  rw [← EI] at JB
  obtain ⟨shared, RR, RL⟩ := proofErase_carrier_aligned_raw_join_realize hΓA.1
    (hb.instN henv Ctx.InstN.zero HX.hasType.2) JB.symm
  obtain ⟨stage, RX⟩ := RX.finite_stage (Stages := ErasedExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  have RXB := proofErase_expansion_compute_inst_argument heq hs hΓA hb hx RX
  rw [← EI] at RXB
  refine ⟨shared, (RXB.mono (fun H => ⟨stage, H⟩)).trans (RL.mono ?_), RR⟩
  intro Δ a b H
  exact ⟨0, .inl (.inr H)⟩

end Lean4Lean.VEnv.Strengthening
