import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaRetainedInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaApplication
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointImageComputation

/-! # Computed eta bodies and arguments meet at their exact beta contractum

The original retained argument supplies native recovery. Computed arguments
need no new native certificate, and proof arguments need none at either end.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions} {n k m : Nat}

/-- Argument computation passes through every occurrence of a typed template,
including annotations, at the same eta stage. -/
theorem proofErase_eta_compute_inst_argument
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (R : ScopedCompute (ErasedEtaExpansionStage D m) (proofEraseCtx Γ) (proofErase Γ x) out) :
    ScopedCompute (ErasedEtaExpansionStage D m) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) ((proofErase (A :: Γ) b).inst out) := by
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have H := proofErase_compute_subst_images_of_renaming (erased_eta_expansion_stage_rename heq hs m)
    hΓA.1 W hb (erasedSubstAgreement_one hΓA hx)
    (τ := ProofShape.Subst.one out) (fun i => by
      cases i with
      | zero => exact R
      | succ i => exact .refl)
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hb]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H

/-- Arbitrary eta-stage computations in a typed body and argument meet at the
exact substituted outputs. Only retained original arguments require recovery. -/
theorem proofErase_eta_body_argument_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedEtaExpansionStage D k)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (RB : ScopedCompute (ErasedEtaExpansionStage D n) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) outB)
    (RX : ScopedCompute (ErasedEtaExpansionStage D m) (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ScopedCompute (ErasedEtaExpansionStage D (max (n + k) m)) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (outB.inst outX) := by
  have R₁ := EtaNativeSubstitution.compute_inst_retained heq hs hΓA.1 hx HR hb RB
  obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize
    (erased_eta_expansion_stage_descent heq hs n) hΓA hb rfl rfl RB
  have R₂ := proofErase_eta_compute_inst_argument heq hs hΓA HB.hasType.2 hx RX
  rw [proofErase_instN hΓA hx Ctx.InstN.zero HB.hasType.2, EB] at R₂
  exact (R₁.mono (fun H => erased_eta_expansion_stage_mono (Nat.le_max_left _ _) H)).trans
    (R₂.mono (fun H => erased_eta_expansion_stage_mono (Nat.le_max_right _ _) H))

/-- After computations inside an eta body and its applied argument, the
original typed application computes to their exact beta contractum. The final
lambda annotation is arbitrary because beta discards it. -/
theorem proofErase_eta_expansion_body_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (hx : env.HasType univs Γ x A)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedEtaExpansionStage D k)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (RB : ScopedCompute (ErasedEtaExpansionStage D n) (proofErase Γ A :: proofEraseCtx Γ)
      (.app ((proofErase Γ f).liftN 1) (etaArgument u)) outB)
    (RX : ScopedCompute (ErasedEtaExpansionStage D m) (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ScopedCompute (ErasedEtaExpansionStage D (max (n + k) m)) (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) (outB.inst outX) ∧
      ∀ X, ProofShape.BetaRed (.app (.lam X outB) outX) (outB.inst outX) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hb : env.HasType univs (A :: Γ) (.app f.lift (.bvar 0)) B := by
    simpa only [VExpr.lift, VExpr.liftN, inst_liftN_bvar] using HasType.app (hf.weak henv) (.bvar .zero)
  have RB' : ScopedCompute (ErasedEtaExpansionStage D n) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) (.app f.lift (.bvar 0))) outB := by
    simpa only [proofEraseCtx, proofErase_eta_body hΓ hA hf hn] using RB
  have R := proofErase_eta_body_argument_square heq hs hΓA hb hx HR RB' RX
  refine ⟨?_, fun _ => .beta⟩
  simpa only [VExpr.inst, instVar_zero, inst_lift] using R

/-- Arbitrary finite eta-stage body and argument computations admit the same
square without a preselected common bound. Proof arguments need no recovery
even at the union. -/
theorem proofErase_eta_union_body_argument_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (RB : ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) outB)
    (RX : ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (outB.inst outX) := by
  classical
  have HI : ∃ k, ¬ IsProof Γ x → ScopedTypeRecovery (ErasedEtaExpansionStage D k)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A) := by
    by_cases hp : IsProof Γ x
    · exact ⟨0, fun hn => (hn hp).elim⟩
    · obtain ⟨k, R⟩ := (HR hp).finite_stage (Stages := ErasedEtaExpansionStage D)
        (fun {n m} hle {Δ a b} H => erased_eta_expansion_stage_mono hle H)
      exact ⟨k, fun _ => R⟩
  obtain ⟨k, HR⟩ := HI
  obtain ⟨n, RB⟩ := RB.finite_stage (Stages := ErasedEtaExpansionStage D)
    (fun {n m} hle {Δ a b} H => erased_eta_expansion_stage_mono hle H)
  obtain ⟨m, RX⟩ := RX.finite_stage (Stages := ErasedEtaExpansionStage D)
    (fun {n m} hle {Δ a b} H => erased_eta_expansion_stage_mono hle H)
  exact (proofErase_eta_body_argument_square heq hs hΓA hb hx HR RB RX).mono
    (fun H => ⟨max (n + k) m, H⟩)

end Lean4Lean.VEnv.Strengthening
