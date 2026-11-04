import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaLambdaResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedCoreJoin

/-! # Literal-lambda native eta has a common core reduct

When typed native-guard computations have core common reducts, Pi inversion
extracts a common reduct of the two domains. Beta restores the original body.
Consequently eta on a literal lambda introduces no new core convertibility,
even when its selected annotation differs from the displayed one.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_forallE_parts from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin

/-- A core without Pi-root primitives computes a literal Pi componentwise. -/
theorem ProofShape.Compute.pi_parts
    (hpi : ∀ {A B out}, ¬ Core (.forallE A B) out)
    (R : Compute Core (.forallE A B) out) :
    ∃ A' B', out = .forallE A' B' ∧ Compute Core A A' ∧ Compute Core B B' := by
  generalize E : ProofShape.forallE A B = source at R
  induction R generalizing A B with
  | base H => exact (hpi (E ▸ H)).elim
  | beta H =>
    cases E
    obtain ⟨A', B', HE, HA, HB⟩ := beta_forallE_parts H
    exact ⟨_, _, HE, .beta HA, .beta HB⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨A₁, B₁, rfl, HA, HB⟩ := ih₁ E
    obtain ⟨A₂, B₂, HE, HA', HB'⟩ := ih₂ rfl
    exact ⟨_, _, HE, HA.trans HA', HB.trans HB'⟩
  | forallE HA HB => cases E; exact ⟨_, _, rfl, HA, HB⟩
  | app | proj | lam => cases E

variable [Params]
/-- Joined native-guard computations give a common core reduct of a lambda's
displayed domain and its selected native Pi domain. The recovered body type
is reified only to type the initial Pi path; no assigned-type coverage is used. -/
theorem proofErase_native_lambda_domain_core_join
    (hrec : ErasedScopedPrimitiveDescent Recovery)
    (hjoin : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Recovery (proofEraseCtx Γ) (proofErase Γ e) out →
      ComputeJoin Core (proofErase Γ e) out)
    (hpi : ∀ {A B out}, ¬ Core (.forallE A B) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (RN : ScopedTypeRecovery Recovery (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) (.forallE X Y)) :
    ComputeJoin Core (proofErase Γ A) X := by
  obtain ⟨C, RC, RP⟩ := RN.lam_compute
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨C', hbC, EC⟩ := proofErase_scoped_typeRecovery_replay hrec hΓA hb
    (by simpa only [proofEraseCtx] using RC)
  obtain ⟨_, hC⟩ := hbC.isType henv hΓA
  have hP := HasType.forallE hA hC
  have EP : proofErase Γ (.forallE A C') = .forallE (proofErase Γ A) C := by
    rw [show proofErase Γ (.forallE A C') = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hP), EC]
  obtain ⟨shared, RA, RX⟩ := hjoin hΓ hP (EP ▸ RP)
  rw [EP] at RA
  obtain ⟨A', C'', rfl, HA, _⟩ := RA.pi_parts hpi
  obtain ⟨X', Y', E, HX, _⟩ := RX.pi_parts hpi
  cases E
  exact ⟨_, HA, HX⟩

/-- Native eta on a retained literal lambda is core-joinable whenever its
guard computations are. The body is restored literally by beta; only domain
computation is needed to meet the selected and original annotations. -/
theorem proofErase_native_eta_lambda_core_join
    (hrec : ErasedScopedPrimitiveDescent Recovery)
    (hjoin : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Recovery (proofEraseCtx Γ) (proofErase Γ e) out →
      ComputeJoin Core (proofErase Γ e) out)
    (hpi : ∀ {A B out}, ¬ Core (.forallE A B) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hn : ¬ IsProof Γ (.lam A b))
    (R : NativeEtaExpansion Recovery (proofEraseCtx Γ) (proofErase Γ (.lam A b)) out) :
    ComputeJoin Core (proofErase Γ (.lam A b)) out := by
  have Ef : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) := if_neg hn
  rw [Ef] at R ⊢
  cases R with
  | @intro X Y v RN SD =>
    obtain ⟨sharedA, RA, RX⟩ := proofErase_native_lambda_domain_core_join hrec hjoin hpi hΓ hA hb RN
    have hf := HasType.lam hA hb
    obtain ⟨D, C, hfD, ED, _⟩ := proofErase_scoped_recovered_pi_descend hrec hΓ hΓ
      (show Ctx.LiftN 0 0 Γ Γ from .zero []) hf
      (by simpa only [ProofShape.liftN_zero, Ef] using RN)
    simp only [ProofShape.liftN_zero] at ED
    obtain ⟨_, hPi⟩ := hfD.isType henv hΓ
    obtain ⟨⟨_, hD⟩, _⟩ := hPi.forallE_inv henv
    have SD' : DomainSort (proofEraseCtx Γ) ((proofErase Γ D).liftN 0) v := by
      simpa only [ProofShape.liftN_zero, ED] using SD
    have hDv := SD'.descend hΓ hΓ (Ctx.LiftN.zero []) hD
    obtain ⟨⟨_, HAD⟩, _⟩ := (hf.uniqU henv hΓ hfD).forallE_inv henv hΓ
    have hAv := hDv.defeqU_l henv hΓ HAD.toU.symm
    exact ⟨_, .lam RA .refl,
      (Compute.beta (proofErase_eta_lambda_beta hΓ hAv hb X)).trans (.lam RX .refl)⟩

end Lean4Lean.VEnv.Strengthening
