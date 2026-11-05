import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaDomainPrimitives

/-! # Full computation preserves historical lambda-domain observations

Control beta uses ordinary argument substitution. A changed control annotation
computes its recursive input demands and transports the body observation to the
new binder. Payload domains descend to their original context independently of
the body and of the temporary control program.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : PureObservation.Definitions}

private theorem typed_beta_interpretation
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = .app (.lam A b) a) :
    ContextSubstitution (A :: proofEraseCtx Γ) (proofEraseCtx Γ) (ProofShape.Subst.one a) := by
  obtain ⟨f₀, x, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
  obtain ⟨A₀, b₀, rfl, _, EA, _⟩ := erase_lam_inv Ef
  obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
  obtain ⟨⟨u, hA⟩, _, hb⟩ := hf.lam_inv henv hΓ
  have hxA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hx
  have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have WI : ContextSubstitution (proofEraseCtx (A₀ :: Γ)) (proofEraseCtx Γ)
      (ProofShape.Subst.one (proofErase Γ x)) :=
    ContextSubstitution.of_typed hΓ (Ctx.InstN.zero.substEq hΓA hxA) (erasedSubstAgreement_one hΓA hxA)
  intro Γ₀ hΓ₀ EΓ₀
  have HH := WI hΓ₀ (by simpa only [proofEraseCtx, EA] using EΓ₀)
  simpa only [Ex] using HH

namespace LambdaDomainObservation

/-- Every compatible full-union computation preserves the domain observer,
including computed control bodies, temporary binders, beta interleavings and
native eta on either payloads or higher-order control functions. -/
theorem Obs.compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ source out)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = source)
    (HS : Valuation D Γ anchor n Δ S) (H : Obs D Γ anchor n Δ S source o) :
    Obs D Γ anchor n Δ S out o := by
  induction R using ScopedCompute.rootBeta_induction generalizing Γ' n S o e T with
  | refl => exact H
  | base R =>
    obtain ⟨stage, R⟩ := R
    exact Obs.stage heq hs hΓ stage R H hΓ' W ht EΓ Ee HS
  | beta =>
    apply H.beta_forward
    cases EΓ
    exact typed_beta_interpretation hΓ' ht Ee
  | trans R₁ _ ih₁ ih₂ =>
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize
      (erased_static_structure_eta_expansion_union_descent heq hs) hΓ' ht EΓ Ee R₁
    exact ih₂ hΓ' W HE.hasType.2 EΓ EE HS (ih₁ hΓ' W ht EΓ Ee HS H)
  | app _ _ ihf ihx =>
    obtain ⟨f, x, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ'
    cases H with
    | app HF HX =>
      exact .app (ihf hΓ' W hf EΓ Ef HS HF) (fun key hk => ihx hΓ' W hx EΓ Ex HS (HX key hk))
  | proj => exact H.not_proj.elim
  | forallE => exact H.not_forallE.elim
  | @lam Δ A A' b b' RA RB _ ihb =>
    cases H with
    | payload HP =>
      obtain ⟨A₀, u, hA₀, E, R₀⟩ := HP
      have RA₀ : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ')
          ((proofErase Γ A₀).liftN n) A' := by simpa only [EΓ, E] using RA
      obtain ⟨A₁, HA₁, R₁, EA₁⟩ := proofErase_scoped_compute_certificate_descend
        (erased_static_structure_eta_expansion_union_certificate_descent heq hs)
        hΓ hΓ' W hA₀ rfl RA₀
      exact .payload ⟨A₁, u, HA₁.hasType.2, EA₁, R₀.trans R₁⟩
    | lam SD HD HB =>
      obtain ⟨A₀, b₀, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
      obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ'
      have hΓA : OnCtx (A₀ :: Γ') (env.IsType univs) := ⟨hΓ', u, hA⟩
      have W' : Ctx.LiftN (n+1) 0 Γ (A₀ :: Γ') := W.comp (by omega) (by omega) Ctx.LiftN.one
      have EΓA : proofEraseCtx (A₀ :: Γ') = A :: Δ := by simp only [proofEraseCtx, EA, EΓ]
      obtain ⟨A₁, HA₁, EA₁⟩ := proofErase_scoped_compute_realize
        (erased_static_structure_eta_expansion_union_descent heq hs) hΓ' hA EΓ EA RA
      have HC : IsDefEqCtx env univs [] (A₀ :: Γ') (A₁ :: Γ') := .succ (.refl hΓ') HA₁
      have WC : ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id := by
        intro Γ₀ hΓ₀ EΓ₀
        have HH := control_context_substitution HC hΓ₀ (EΓ₀.trans EΓA.symm)
        simpa only [proofEraseCtx, EA₁, EΓ] using HH
      apply Obs.lam ⟨Γ', A₁, hΓ', EΓ, HA₁.hasType.2, EA₁⟩
      · intro key hk
        have HD' : LowerDomainDemand D Γ anchor key n (proofEraseCtx Γ') (proofErase Γ' A₀) := by
          simpa only [EΓ, EA] using HD key hk
        have RA' : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ')
            (proofErase Γ' A₀) A' := by simpa only [EΓ, EA] using RA
        simpa only [EΓ] using HD'.compute_type heq hs hΓ hΓ' W hA RA'
      · exact (ihb hΓA W' hb EΓA Eb (HS.cons SD HD) HB).context WC

/-- A literal lambda at the payload demand exposes its domain certificate
exactly; control lambdas carry functional demands and cannot match this case. -/
theorem Obs.literal_lambda (H : Obs D Γ anchor n Δ S (.lam A b) .pi) :
    LowerDomainHistory D Γ anchor n Δ A b := by
  cases H with
  | payload HP => exact HP

end LambdaDomainObservation

/-- A full static structure/function-eta computation between literal lambdas
retains a forward computation from the original written domain to the final
written domain. Arbitrary computed control functions are included; no native
cut coverage, normalization or type-fork joining is assumed. -/
theorem proofErase_static_structure_lambda_domain_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hn : ¬ IsProof Γ (.lam A b))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) (.lam X y)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ A) X := by
  have H : LambdaDomainObservation.Obs D Γ (proofErase Γ A) 0 (proofEraseCtx Γ)
      (fun _ _ => False) (proofErase Γ (.lam A b)) .pi := by
    rw [show proofErase Γ (.lam A b) = .lam _ _ from if_neg hn]
    exact .payload ⟨A, u, hA, ProofShape.liftN_zero _, .refl⟩
  have HO := H.compute heq hs hΓ R hΓ (Ctx.LiftN.zero []) (HasType.lam hA hb) rfl rfl
    (fun _ _ h => h.elim)
  obtain ⟨A', _, _, E, RA⟩ := HO.literal_lambda
  simp only [ProofShape.liftN_zero] at E
  exact E ▸ RA

end Lean4Lean.VEnv.Strengthening
