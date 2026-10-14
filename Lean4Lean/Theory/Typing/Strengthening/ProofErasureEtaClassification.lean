import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaArguments

/-! # Typed displayed eta guards have canonical argument classification

The raw eta guard offers a retained variable or a proof marker. Common original
typing forces that choice to agree with the actual displayed domain's sort.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_bvar_inv eta_argument from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- A displayed raw eta guard between common-typed originals is exactly the
canonical eta shape for its recovered original domain. In particular the proof
marker option cannot be used at a retained-variable domain. -/
theorem proofErase_eta_head_classified (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e T) (hf : env.HasType univs Γ f T)
    (H : ProofShape.EtaHead (proofErase Γ e) (proofErase Γ f)) :
    ∃ A B u, env.HasType univs Γ A (.sort u) ∧
      env.HasType univs Γ f (.forallE A B) ∧ ¬ IsProof Γ f ∧
      proofErase Γ e = .lam (proofErase Γ A)
        (.app ((proofErase Γ f).liftN 1) (ProofShape.etaArgument u)) := by
  obtain ⟨_, arg, HE, Harg⟩ := H.shape
  obtain ⟨A, body, rfl, hne, HA, Hb⟩ := erase_lam_inv HE
  obtain ⟨g, a, rfl, hnb, Hg, Ha⟩ := erase_app_inv Hb
  obtain ⟨⟨u, hA⟩, B, hb⟩ := he.lam_inv henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hfPi : env.HasType univs Γ f (.forallE A B) :=
    hf.defeqU_r henv hΓ (he.uniqU henv hΓ (HasType.lam hA hb))
  have hfw := hfPi.weak henv (B := A)
  have Ef := proofErase_liftN hΓ hΓA Ctx.LiftN.one hfPi
  have Eg : proofErase (A :: Γ) g = proofErase (A :: Γ) f.lift := Hg.trans Ef.symm
  obtain ⟨_, _, hg, ha⟩ := HasType.app_inv henv hΓA hb
  obtain ⟨_, HC⟩ := (proofErase_reflect hΓA hg hfw Eg).2 (not_isProof_fn hΓA hg ha hnb)
  have Hgf := (HC.defeq hΓA).of_l henv hΓA hg
  obtain ⟨⟨_, hCA⟩, _⟩ := (Hgf.hasType.2.uniqU henv hΓA hfw).forallE_inv henv hΓA
  have haA := hCA.defeq ha
  have Hax := eta_argument hΓ hA haA
    (Harg.elim (fun h => .inl (Ha.trans h)) (fun h => .inr (Ha.trans h)))
  have EA : arg = proofErase (A :: Γ) (.bvar 0) := by
    rcases Harg with rfl | rfl
    · obtain rfl := erase_bvar_inv Ha
      exact Ha.symm
    · have hpa := proofErase_eq_proof.1 Ha
      exact (proofErase_eq_proof.2 ((isProof_congr hΓA (Hax.of_l henv hΓA haA)).1 hpa)).symm
  have hnf := mt (isProof_congr hΓ (proofErase_eta_head_reflect hΓ he hf H)).2 hne
  refine ⟨A, B, u, hA, hfPi, hnf, ?_⟩
  simpa only [← HA, EA, proofErase_fresh_argument hΓ hA] using HE

end Lean4Lean.VEnv.Strengthening
