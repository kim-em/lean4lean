import Lean4Lean.Theory.Typing.Strengthening.ProofErasureControlObservation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiOriginTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaStages

/-! # Preserving typed Pi observations through eta-aware computation

The closed control types exclude the untyped eta counterexample. Ordinary
context substitution handles changed lambda annotations; native images are not
needed to transport the observation itself. Only marked Pi components require
their original-context closure law.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.ControlObservation
open private erase_app_inv erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Every primitive eta-aware stage preserves typed marked observations.
Native eta uses its preceding stage only for ordinary typed replay. -/
theorem erased_eta_stage_controlObservation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) : ∀ stage {Δ a b P n S t o},
    ErasedEtaExpansionStage D stage Δ a b → Obs P n Δ S a t o → Obs P n Δ S b t o := by
  intro stage
  induction stage with
  | zero =>
    intro Δ a b P n S t o R H
    rcases R with (R | R) | R
    · exact (H.not_primitiveHead (erased_iota_primitive_head R)).elim
    · cases R with
      | sort => exact H.not_sort.elim
      | const => exact (H.not_primitiveHead trivial).elim
    · cases R
      exact H.constant_expansion
  | succ stage ih =>
    intro Δ a b P n S t o R H
    rcases R with R | R | R | R | R
    · exact ih R H
    · exact (H.not_primitiveHead R.2.head).elim
    · exact (H.not_primitiveHead R.head).elim
    · exact H.native_identity (erased_eta_expansion_stage_descent heq hs stage) R
    · exact H.native_eta (erased_eta_expansion_stage_descent heq hs stage) R

/-- Unbounded finite eta guard depth preserves the same typed demand. -/
theorem erased_eta_union_controlObservation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ErasedEtaExpansionUnion D Δ a b) (H : Obs P n Δ S a t o) : Obs P n Δ S b t o := by
  obtain ⟨stage, R⟩ := R
  exact erased_eta_stage_controlObservation heq hs stage R H

/-- Compatible computation preserves typed marked observations when literal
Pi components preserve their histories below every temporary binder prefix.
Free control valuations retain ordinary typing; lambda annotation changes are
handled by identity context substitution after the body has computed. -/
theorem proofErase_scoped_compute_controlObservation
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hroot : ∀ {Δ a b n S t o}, Step Δ a b → Obs P n Δ S a t o → Obs P n Δ S b t o)
    (hpi : PiOriginComponentClosure Step Γ P)
    (R : ScopedCompute Step Δ source out)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = source)
    (HS : S.Typed Δ) (H : Obs P n Δ S source t o) : Obs P n Δ S out t o := by
  induction R using ScopedCompute.rootBeta_induction generalizing Γ' n S t o e T with
  | refl => exact H
  | base R => exact hroot R H
  | beta => exact H.beta_forward HS
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize hstep hΓ' ht EΓ Ee R₁
    exact ih₂ hΓ' W HE.hasType.2 EΓ EE HS (ih₁ hΓ' W ht EΓ Ee HS H)
  | app RF RX ihf ihx =>
    have HT := H.typing.compute hstep (.app RF RX)
    obtain ⟨f, x, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ'
    cases H with
    | app _ HF HX =>
      exact .app HT (ihf hΓ' W hf EΓ Ef HS HF)
        (fun key hk => ihx hΓ' W hx EΓ Ex HS (HX key hk))
  | proj => exact H.not_proj.elim
  | @lam Δ D D' b b' RA RB ihA ihb =>
    have HT := H.typing.compute hstep (.lam RA RB)
    obtain ⟨A, body, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, C, hb⟩ := ht.lam_inv henv hΓ'
    have hΓA : OnCtx (A :: Γ') (env.IsType univs) := ⟨hΓ', u, hA⟩
    have W' : Ctx.LiftN (n+1) 0 Γ (A :: Γ') := W.comp (by omega) (by omega) Ctx.LiftN.one
    have EΓA : proofEraseCtx (A :: Γ') = D :: Δ := by simp only [proofEraseCtx, EA, EΓ]
    have SD : DomainSort Δ D u := ⟨Γ', A, hΓ', EΓ, hA, EA⟩
    obtain ⟨A', HA', EA'⟩ := proofErase_scoped_compute_realize hstep hΓ' hA EΓ EA RA
    have HC : IsDefEqCtx env univs [] (A :: Γ') (A' :: Γ') := .succ (.refl hΓ') HA'
    have WC : ContextSubstitution (D :: Δ) (D' :: Δ) ProofShape.Subst.id := by
      intro Γ₀ hΓ₀ EΓ₀
      have HH := control_context_substitution HC hΓ₀ (EΓA.trans EΓ₀.symm).symm
      simpa only [proofEraseCtx, EA', EΓ] using HH
    cases H with
    | lam HL HK HB =>
      have HX := HL.lam_parts.2
      apply Obs.lam HT HK
      exact (ihb hΓA W' hb EΓA Eb (HS.cons HX SD) HB).context WC
  | forallE RA RB =>
    have HT := H.typing.compute hstep (.forallE RA RB)
    cases H with
    | payload _ HP =>
      obtain ⟨A', B', HP', EX, EY⟩ := hpi hΓ' W HP (EΓ ▸ RA) (EΓ ▸ RB)
      rw [EX, EY] at HT ⊢
      exact Obs.payload HT HP'

end Lean4Lean.VEnv.Strengthening
