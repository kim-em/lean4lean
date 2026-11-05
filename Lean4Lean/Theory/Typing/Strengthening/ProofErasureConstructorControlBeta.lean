import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorControlNative

/-! # Beta evolution of constructor control programs

Complete beta reduction preserves the observer through arbitrary higher-order
control syntax, dependent fields and changed control annotations. Native output
histories therefore remain available after these reductions without exact
native recovery of substituted arguments. Enriched primitive preservation and
constructor-prefix evolution remain separate obligations.
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

namespace ConstructorControlObservation

/-- Every compatible beta computation preserves the historical constructor
observer. This includes computation inside function controls and their bodies,
not just root contraction of a literal identity or constant wrapper. -/
theorem Obs.beta_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (R : ProofShape.BetaRed source out)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = source)
    (HS : Valuation D Γ origin n Δ S) (H : Obs D Γ r info origin n Δ S source o) :
    Obs D Γ r info origin n Δ S out o := by
  induction R generalizing Γ' n Δ S o e T with
  | refl => exact H
  | beta =>
    apply H.beta_forward
    cases EΓ
    exact typed_beta_interpretation hΓ' ht Ee
  | trans R₁ _ ih₁ ih₂ =>
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize
      (erased_static_structure_eta_expansion_union_descent heq hs) hΓ' ht EΓ Ee (.beta R₁)
    exact ih₂ hΓ' W HE.hasType.2 EΓ EE HS (ih₁ hΓ' W ht EΓ Ee HS H)
  | app RF RX ihf ihx =>
    obtain ⟨f, x, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ'
    cases H with
    | payload HP =>
      cases EΓ
      exact .payload (HP.beta heq hs hΓ hΓ' W (.app RF RX))
    | app HF HX =>
      exact .app (ihf hΓ' W hf EΓ Ef HS HF) (fun key hk => ihx hΓ' W hx EΓ Ex HS (HX key hk))
  | proj => exact H.not_proj.elim
  | forallE => exact H.not_forallE.elim
  | @lam A A' b b' RA RB _ ihb =>
    cases H with
    | payload HP => have E := HP.head; cases E
    | lam SD HD HB =>
      obtain ⟨A₀, b₀, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
      obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ'
      have hΓA : OnCtx (A₀ :: Γ') (env.IsType univs) := ⟨hΓ', u, hA⟩
      have W' : Ctx.LiftN (n+1) 0 Γ (A₀ :: Γ') := W.comp (by omega) (by omega) Ctx.LiftN.one
      have EΓA : proofEraseCtx (A₀ :: Γ') = A :: Δ := by simp only [proofEraseCtx, EA, EΓ]
      obtain ⟨A₁, HA₁, EA₁⟩ := proofErase_scoped_compute_realize
        (erased_static_structure_eta_expansion_union_descent heq hs) hΓ' hA EΓ EA (.beta RA)
      have HC : IsDefEqCtx env univs [] (A₀ :: Γ') (A₁ :: Γ') := .succ (.refl hΓ') HA₁
      have WC : ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id := by
        intro Γ₀ hΓ₀ EΓ₀
        have HH := control_context_substitution HC hΓ₀ (EΓ₀.trans EΓA.symm)
        simpa only [proofEraseCtx, EA₁, EΓ] using HH
      apply Obs.lam ⟨Γ', A₁, hΓ', EΓ, HA₁.hasType.2, EA₁⟩
      · intro key hk
        have HD' : LowerTypeDemand D Γ origin key n (proofEraseCtx Γ') (proofErase Γ' A₀) := by
          simpa only [EΓ, EA] using HD key hk
        have RA' : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ')
            (proofErase Γ' A₀) A' := by simpa only [EΓ, EA] using (ScopedCompute.beta (Step := ErasedStaticStructureEtaExpansionUnion D) (Δ := Δ) RA)
        simpa only [EΓ] using HD'.compute_type heq hs hΓ hΓ' W hA RA'
      · exact (ihb hΓA W' hb EΓA Eb (HS.cons SD HD) HB).context WC

end ConstructorControlObservation
end Lean4Lean.VEnv.Strengthening
