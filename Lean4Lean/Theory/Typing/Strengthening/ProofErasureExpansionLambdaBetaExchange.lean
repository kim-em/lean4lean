import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionLambdaOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionConstantReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionBetaSquares
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeRetainedInstantiation

/-! # Head beta against whole expanded function computations

Lambda origin supplies the body history previously required as a premise.
Proof arguments need no native image; retained arguments use their original
assigned type. Constant functions discard arbitrary raw arguments altogether.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Full-union body computation instantiates with native images only for
non-proof arguments. The result retains its exact raw substituted output. -/
theorem proofErase_expansion_union_compute_inst_retained
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (hb : env.HasType univs (A :: Γ) b B)
    (RB : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) outB) :
    ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (outB.inst (proofErase Γ x)) := by
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
    ExpansionNativeSubstitution.compute_union_subst heq hs hΓ W (erasedSubstAgreement_one hΓA hx)
      (NativeImageTransport.Images.inst_retained hΓ hx HR) hb RB

/-- Independent body and argument paths meet at their exact instantiated raw
outputs. Native evidence is needed only for the original retained argument,
so proof arguments and loss of recovery during argument computation are allowed. -/
theorem proofErase_expansion_union_body_argument_square_retained
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (RB : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) outB)
    (RX : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (outB.inst outX) := by
  have R₁ := proofErase_expansion_union_compute_inst_retained heq hs hΓA.1 hx HR hb RB
  obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize
    (erased_expansion_union_descent heq hs) hΓA hb rfl rfl RB
  obtain ⟨m, RX⟩ := RX.finite_stage (Stages := ErasedExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  have R₂ := proofErase_expansion_compute_inst_argument heq hs hΓA HB.hasType.2 hx RX
  rw [proofErase_instN hΓA hx Ctx.InstN.zero HB.hasType.2, EB] at R₂
  exact R₁.trans (R₂.mono (fun H => ⟨m, H⟩))

/-- Whole expanded function computation commutes with the original head beta
at a selected residual. Annotation and body paths are recovered automatically.
The original retained argument needs its assigned native type; no native
certificate for the computed argument or precomputed body path is assumed. -/
theorem proofErase_expansion_union_beta_exchange_retained
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.lam A b))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (RF : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) outF)
    (RX : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ∃ X y, ProofShape.BetaRed outF (.lam X y) ∧
      ProofShape.BetaRed (.app outF outX) (y.inst outX) ∧
      ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) (y.inst outX) := by
  obtain ⟨X, y, _, RB, Rβ⟩ := proofErase_expansion_union_lambda_readout heq hs hΓ hA hb hn RF
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  exact ⟨X, y, Rβ, (ProofShape.BetaRed.app Rβ .refl).trans .beta,
    proofErase_expansion_union_body_argument_square_retained heq hs hΓA hb hx HR
      (by simpa only [proofEraseCtx] using RB) RX⟩

/-- Proof arguments discharge the recovery premise of the whole-function
beta square. The entire function and argument may still compute independently. -/
theorem proofErase_expansion_union_beta_exchange_proof
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.lam A b)) (hp : IsProof Γ x)
    (RF : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) outF)
    (RX : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ∃ X y, ProofShape.BetaRed outF (.lam X y) ∧
      ProofShape.BetaRed (.app outF outX) (y.inst outX) ∧
      ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) (y.inst outX) :=
  proofErase_expansion_union_beta_exchange_retained heq hs hΓ hA hb hx hn
    (fun hnp => (hnp hp).elim) RF RX

/-- An arbitrarily computed constant function beta-returns a lower computed
payload at every raw argument. This closes the whole-function version of the
constant-wrapper square without argument typing or native-image assumptions. -/
theorem proofErase_expansion_union_constant_function_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (ht : env.HasType univs Γ e T) (hn : ¬ IsProof Γ (.lam A e.lift))
    (RF : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) ((proofErase Γ e).liftN 1)) outF) :
    ∃ e', env.IsDefEq univs Γ e e' T ∧
      ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ e) (proofErase Γ e') ∧
      ∀ arg, ProofShape.BetaRed (.app outF arg) (proofErase Γ e') := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have EE := proofErase_liftN hΓ hΓA Ctx.LiftN.one ht
  have RF' : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) e.lift)) outF := by
    simpa only [VExpr.lift, EE] using RF
  obtain ⟨X, y, _, RB, Rβ⟩ :=
    proofErase_expansion_union_lambda_readout heq hs hΓ hA (ht.weak henv) hn RF'
  have RB' : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx (A :: Γ))
      ((proofErase Γ e).liftN 1) y := by
    simpa only [VExpr.lift, EE, proofEraseCtx] using RB
  obtain ⟨e', HE, RE, _, HB⟩ := proofErase_expansion_union_constant_body_readout heq hs hΓ hA ht RB'
  exact ⟨e', HE, RE, fun arg => (ProofShape.BetaRed.app Rβ .refl).trans (HB X arg)⟩

end Lean4Lean.VEnv.Strengthening
