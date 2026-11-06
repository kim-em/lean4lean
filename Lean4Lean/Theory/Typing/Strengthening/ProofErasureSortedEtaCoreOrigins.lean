import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExactEtaCoreReflection

/-! # Sorted eta origins with full core histories

Domain and function histories include ordinary computation and universe steps.
Exact fresh reflection simulates a path from either orientation of an eta origin;
when the fresh boundary is crossed, the exposed domain keeps its function history.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : Definitions}

namespace ProofShape
/-- The written domain and short function retain independent full-core histories. -/
def EtaCoreOrigin (D : Definitions) (A₀ f₀ A f : ProofShape) : Prop :=
  Compute (ErasedLevelCore D) A₀ A ∧ Compute (ErasedLevelCore D) f₀ f

/-- A domain mark pairs a computed written eta annotation with an annotation
exposed by full-core computation of the original function, in either direction. -/
def EtaCoreDomains (D : Definitions) (A₀ f₀ A C : ProofShape) : Prop :=
  (Compute (ErasedLevelCore D) A₀ A ∧ ∃ b, Compute (ErasedLevelCore D) f₀ (.lam C b)) ∨
  (Compute (ErasedLevelCore D) A₀ C ∧ ∃ b, Compute (ErasedLevelCore D) f₀ (.lam A b))

/-- Reversing a domain pair retains its histories. -/
theorem EtaCoreDomains.symm (H : EtaCoreDomains D A₀ f₀ A C) : EtaCoreDomains D A₀ f₀ C A :=
  Or.symm H

/-- Full-core computation of either annotation preserves its recorded origin. -/
theorem EtaCoreDomains.compute_left (H : EtaCoreDomains D A₀ f₀ A C)
    (R : Compute (ErasedLevelCore D) A A') : EtaCoreDomains D A₀ f₀ A' C := by
  rcases H with ⟨HA, b, HF⟩ | ⟨HC, b, HF⟩
  · exact .inl ⟨HA.trans R, b, HF⟩
  · exact .inr ⟨HC, b, HF.trans (.lam R .refl)⟩
end ProofShape

/-- Full-core descendants of actual non-proof functions cannot be proof markers. -/
theorem proofErase_level_core_descendant_ne_proof (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T) (hn : ¬ IsProof Γ f)
    (R : Compute (ErasedLevelCore D) (proofErase Γ f) g) : g ≠ .proof := by
  obtain ⟨g₀, HE, EG⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hf rfl rfl (R.scoped (fun H => .base H))
  intro E
  exact hn ((isProof_congr hΓ HE).2 (proofErase_eq_proof.1 (EG.trans E)))

/-- Full-core domain histories retain their actual input sort witness. -/
theorem proofErase_level_core_domain_sort (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (R : Compute (ErasedLevelCore D) (proofErase Γ A) C) : DomainSort (proofEraseCtx Γ) C u := by
  obtain ⟨C₀, HE, EC⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hA rfl rfl (R.scoped (fun H => .base H))
  exact EC ▸ DomainSort.of_typed hΓ HE.hasType.2

/-- Eta beta restores the exact body of a lambda exposed by a full-core path
from the ambient function, including when its original input is a proposition. -/
theorem sorted_eta_lambda_beta_of_core_origin (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : Compute (ErasedLevelCore D) (proofErase Γ f) (.lam C body)) (X : ProofShape) :
    ProofShape.BetaRed (sortedEta u X (.lam C body)) (.lam X body) := by
  obtain ⟨g, HE, EG⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hf rfl rfl (R.scoped (fun H => .base H))
  have hg := HE.hasType.2
  obtain ⟨C₀, b, rfl, _, EC, EB⟩ := erase_lam_inv EG
  obtain ⟨⟨v, hC⟩, _, hb⟩ := hg.lam_inv henv hΓ
  obtain ⟨⟨_, HCA⟩, _⟩ := ((HasType.lam hC hb).uniqU henv hΓ hg).forallE_inv henv hΓ
  have hCu := hA.defeqU_l henv hΓ HCA.toU.symm
  simpa only [EC, EB, sortedEta] using proofErase_eta_lambda_beta hΓ hCu hb X

/-- Arbitrary full-core paths from a lifted sorted eta origin have matching
paths on the opposite side. The source endpoint stays exact. Crossing beta
creates a domain mark with a full function history, not a semantic placeholder. -/
theorem sorted_eta_origin_core (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (H : LiftedOrigin (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ A) (proofErase Γ f))) n a b)
    (R : Compute (ErasedLevelCore D) a a') :
    ∃ b', Compute (ErasedLevelCore D) b b' ∧
      AmbientVariant (EtaCoreDomains D (proofErase Γ A) (proofErase Γ f))
        (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ A) (proofErase Γ f))) n a' b' := by
  obtain ⟨x, y, H, rfl, rfl⟩ := H
  obtain ⟨out, R0, rfl⟩ := R.level_core_lift_inv
  cases H with
  | @etaL C g HG =>
    obtain ⟨C', body, rfl, RC, RB⟩ := R0.level_core_lam_inv
    obtain ⟨g₀, HE, EG⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
      hΓ hf rfl rfl (HG.2.scoped (fun H => .base H))
    have hng := mt (isProof_congr hΓ HE).2 hn
    obtain ⟨g', RF, HR⟩ := proofErase_level_core_fresh_application_classified hs hΓ hA HE.hasType.2 hng
      (by simpa only [EG] using RB)
    rw [EG] at RF
    have HG' : EtaCoreOrigin D (proofErase Γ A) (proofErase Γ f) C' g' :=
      ⟨HG.1.trans RC, HG.2.trans RF⟩
    refine ⟨g'.liftN n, RF.liftN (fun H => erased_level_core_liftN H), ?_⟩
    rcases HR with rfl | ⟨D, rfl⟩
    · exact .origin ⟨sortedEta u C' g', g', .etaL HG', rfl, rfl⟩
    · exact .marked (.inl ⟨HG'.1, body, HG'.2⟩) .refl
  | @etaR C g HG =>
    refine ⟨(sortedEta u C out).liftN n, ?_, ?_⟩
    · exact (ProofShape.Compute.lam .refl
        (.app (R0.liftN (fun H => erased_level_core_liftN H)) .refl)).liftN
          (fun H => erased_level_core_liftN H)
    · exact .origin ⟨out, sortedEta u C out, .etaR ⟨HG.1, HG.2.trans R0⟩, rfl, rfl⟩

end Lean4Lean.VEnv.Strengthening
