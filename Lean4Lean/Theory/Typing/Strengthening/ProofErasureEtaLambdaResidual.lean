import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaPiOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedEtaBeta

/-! # Native eta of a literal lambda has a component residual

Native recovery of a lambda starts with its displayed domain. Full Pi origin
therefore joins that domain to every selected native eta domain, without an
assigned-type coverage premise. Beta restores the original body, including
when eta uses an erased proof argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_forallE_parts from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
variable [Params] {D : PureObservation.Definitions}

/-- A lambda's native type starts with the displayed domain and a recovered
body type, followed by compatible computation. This is purely syntactic
inversion and makes no assertion about the lambda's assigned codomain. -/
theorem ProofShape.ScopedTypeRecovery.lam_compute
    (R : ScopedTypeRecovery Step Δ (.lam A b) out) :
    ∃ B, ScopedTypeRecovery Step (A :: Δ) b B ∧ ScopedCompute Step Δ (.forallE A B) out := by
  generalize E : ProofShape.lam A b = e at R
  induction R with
  | lam R => cases E; exact ⟨_, R, .refl⟩
  | convert _ RC ih =>
    obtain ⟨B, RB, RP⟩ := ih E
    exact ⟨B, RB, RP.trans RC⟩
  | bvar | sort | const | app | forallE | proj => cases E

/-- Every Pi recovered from a retained actual lambda has a domain joined to
the displayed domain. The original domain computes in the eta union, while
the selected domain needs only beta cleanup. No assigned-to-native path is
assumed: lambda recovery supplies the needed initial Pi itself. -/
theorem proofErase_eta_lambda_native_domain_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (R : ScopedTypeRecovery (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) (.forallE X Y)) :
    ∃ shared, ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) shared ∧ ProofShape.BetaRed X shared := by
  obtain ⟨C, RC, RP⟩ := R.lam_compute
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨C', hbC, EC⟩ := proofErase_scoped_typeRecovery_replay
    (erased_eta_expansion_union_descent heq hs) hΓA hb (by simpa only [proofEraseCtx] using RC)
  obtain ⟨v, hC⟩ := hbC.isType henv hΓA
  rw [← EC] at RP
  obtain ⟨X', Y', RA, _, RB⟩ := proofErase_eta_union_pi_readout heq hs hΓ hA hC RP
  obtain ⟨X'', Y'', E, RX, RY⟩ := beta_forallE_parts RB
  cases E
  exact ⟨_, RA, RX⟩

/-- A native eta step on an actual lambda meets a computation changing only
its displayed domain. The eta branch beta-reduces to that exact same lambda;
its original body is retained, even for a proposition-valued domain. -/
theorem proofErase_eta_lambda_component_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hn : ¬ IsProof Γ (.lam A b))
    (R : NativeEtaExpansion (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) out) :
    ∃ sharedA, ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) sharedA ∧
      ProofShape.BetaRed out (.lam sharedA (proofErase (A :: Γ) b)) := by
  cases R with
  | @intro X Y v RN SD =>
    obtain ⟨sharedA, RA, RX⟩ := proofErase_eta_lambda_native_domain_residual heq hs hΓ hA hb RN
    have hf := HasType.lam hA hb
    have Ef : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) := if_neg hn
    obtain ⟨D', C', hfD, ED, _⟩ := proofErase_scoped_recovered_pi_descend
      (erased_eta_expansion_union_descent heq hs) hΓ hΓ
      (show Ctx.LiftN 0 0 Γ Γ from .zero []) hf
      (by simpa only [ProofShape.liftN_zero, Ef] using RN)
    simp only [ProofShape.liftN_zero] at ED
    obtain ⟨_, hPi⟩ := hfD.isType henv hΓ
    obtain ⟨⟨_, hD⟩, _⟩ := hPi.forallE_inv henv
    have SD' : DomainSort (proofEraseCtx Γ) ((proofErase Γ D').liftN 0) v := by
      simpa only [ProofShape.liftN_zero, ED] using SD
    have hDv := SD'.descend hΓ hΓ (Ctx.LiftN.zero []) hD
    obtain ⟨⟨_, HAD⟩, _⟩ := (hf.uniqU henv hΓ hfD).forallE_inv henv hΓ
    have hAv := hDv.defeqU_l henv hΓ HAD.toU.symm
    exact ⟨sharedA, RA, (proofErase_eta_lambda_beta hΓ hAv hb X).trans (.lam RX .refl)⟩

/-- The whole literal-lambda/native-eta peak has a common reduct. The short
branch computes only the annotation; the long branch uses only beta. -/
theorem proofErase_eta_lambda_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hn : ¬ IsProof Γ (.lam A b))
    (R : NativeEtaExpansion (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) out) :
    ∃ shared, ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) shared ∧ ProofShape.BetaRed out shared := by
  have E : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) := if_neg hn
  rw [E] at R ⊢
  obtain ⟨sharedA, RA, RB⟩ := proofErase_eta_lambda_component_residual heq hs hΓ hA hb hn R
  exact ⟨_, .lam RA .refl, RB⟩

/-- A finite native eta guard on a literal lambda has a finite later
annotation residual. The long branch remains beta-only, independent of the
later bound needed to remove control wrappers from the recovered type path. -/
theorem proofErase_eta_stage_lambda_component_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hn : ¬ IsProof Γ (.lam A b))
    (R : NativeEtaExpansion (ErasedEtaExpansionStage D stage) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) out) :
    ∃ later sharedA, stage ≤ later ∧
      ScopedCompute (ErasedEtaExpansionStage D later) (proofEraseCtx Γ)
        (proofErase Γ A) sharedA ∧
      ProofShape.BetaRed out (.lam sharedA (proofErase (A :: Γ) b)) := by
  obtain ⟨sharedA, RA, RB⟩ := proofErase_eta_lambda_component_residual heq hs hΓ hA hb hn
    (R.mono (fun H => ⟨stage, H⟩))
  obtain ⟨n, RA⟩ := RA.finite_stage (Stages := ErasedEtaExpansionStage D)
    (fun {n m} hle {Δ a b} H => erased_eta_expansion_stage_mono hle H)
  exact ⟨max stage n, sharedA, Nat.le_max_left _ _,
    RA.mono (fun H => erased_eta_expansion_stage_mono (Nat.le_max_right _ _) H), RB⟩

end Lean4Lean.VEnv.Strengthening
