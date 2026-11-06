import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqIteratedConsumption

/-! # Preserve target completion across a computed used annotation

Computation of an existing binder's annotation preserves iterated completion.
When the binder belongs to an unused inserted block, rebuild that block. When
it lies above the block, descend its actual computation certificate, convert
the lower source context, and restore the insertion with the new annotation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

private theorem completion_annotation_insert
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ') (hf : env.HasType univs Γ f T)
    (HP : IteratedAmbientEqCompletion Δ v w original (proofEraseCtx Γ) (proofErase Γ f))
    (ih : ∀ {A Ξ A'}, proofEraseCtx Γ = A :: Ξ → ScopedCompute Step Ξ A A' →
      IteratedAmbientEqCompletion Δ v w original (A' :: Ξ) (proofErase Γ f))
    (E : proofEraseCtx Γ' = rawA :: Ξ) (RD : ScopedCompute Step Ξ rawA rawA') :
    IteratedAmbientEqCompletion Δ v w original (rawA' :: Ξ)
      ((proofErase Γ f).liftN count offset) := by
  cases W with
  | zero As hlen =>
    cases As with
    | nil =>
      have hn : count = 0 := hlen.symm
      simpa only [hn, ProofShape.liftN_zero] using ih E RD
    | cons A As =>
      obtain ⟨hTail, u, hA⟩ := hΓ'
      obtain ⟨EA, EΞ⟩ := List.cons.inj E
      obtain ⟨A', HA, EA'⟩ := proofErase_scoped_compute_realize hstep.descent hTail hA EΞ EA RD
      have hNew : OnCtx (A' :: (As ++ Γ)) (env.IsType univs) := ⟨hTail, u, HA.hasType.2⟩
      have Wnew : Ctx.LiftN count 0 Γ (A' :: (As ++ Γ)) := .zero (A' :: As) hlen
      have HH := IteratedAmbientEqCompletion.insert hΓ hNew Wnew hf HP
      have EAnew : proofErase (As ++ Γ) A' = rawA' := EA'
      have ECtx : proofEraseCtx (As ++ Γ) = Ξ := EΞ
      simpa only [proofEraseCtx, EAnew, ECtx] using HH
  | @succ offset Γ₀ Γ₀' A W =>
    obtain ⟨hΓ₀, u, hA⟩ := hΓ
    obtain ⟨hΓ₀', _, _⟩ := hΓ'
    obtain ⟨EA, EΞ⟩ := List.cons.inj E
    have EA₀ : (proofErase Γ₀ A).liftN count offset = rawA :=
      (proofErase_liftN hΓ₀ hΓ₀' W hA).symm.trans EA
    obtain ⟨A', HA, RA, EA'⟩ := proofErase_scoped_compute_certificate_descend
      hstep hΓ₀ hΓ₀' W hA EΞ (EA₀.symm ▸ RD)
    have C : IsDefEqCtx env univs [] (A :: Γ₀) (A' :: Γ₀) := .succ (.refl hΓ₀) HA
    have hLower : OnCtx (A' :: Γ₀) (env.IsType univs) := ⟨hΓ₀, u, HA.hasType.2⟩
    have hUpper : OnCtx (A'.liftN count offset :: Γ₀') (env.IsType univs) :=
      ⟨hΓ₀', u, HA.hasType.2.weakN henv W⟩
    have Ef := proofErase_defeqCtx (show OnCtx (A :: Γ₀) (env.IsType univs) from ⟨hΓ₀, u, hA⟩) C hf
    have HPnew : IteratedAmbientEqCompletion Δ v w original (proofEraseCtx (A' :: Γ₀))
        (proofErase (A' :: Γ₀) f) := by
      simpa only [proofEraseCtx, Ef] using ih rfl RA
    have HH := IteratedAmbientEqCompletion.insert hLower hUpper W.succ (hf.defeqDFC henv C) HPnew
    have EUpper : proofEraseCtx (A'.liftN count offset :: Γ₀') = rawA' :: Ξ := by
      rw [proofEraseCtx, proofErase_liftN hΓ₀ hΓ₀' W HA.hasType.2, EA', EΞ]
    simpa only [EUpper, ← Ef] using HH

/-- Computing the annotation of an existing top binder preserves target
completion, including when the body uses that binder and unused blocks were
inserted at several depths. The proof retains lower annotation certificates
through each insertion, converts only actual semantic source realizations,
and restores the exact new raw context. It does not require substitution or
context-conversion closure of native recovery guards. -/
theorem IteratedAmbientEqCompletion.compute_annotation
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (HP : IteratedAmbientEqCompletion Δ v w original (rawA :: Ξ) source)
    (RD : ScopedCompute Step Ξ rawA rawA') :
    IteratedAmbientEqCompletion Δ v w original (rawA' :: Ξ) source := by
  have pure : ∀ {Γ v' w' pre F},
      OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F →
      ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) →
      EqPrefixSpecialization Γ Δ v w v' w' original pre →
      ∀ {A Ξ A'}, proofEraseCtx Γ = A :: Ξ → ScopedCompute Step Ξ A A' →
      IteratedAmbientEqCompletion Δ v w original (A' :: Ξ)
        (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)) := by
    intro Γ v' w' pre F hΓ hf hn HS rawA Ξ rawA' E RD
    cases Γ with
    | nil => cases E
    | cons A Γ =>
      obtain ⟨hΓ, u, hA⟩ := hΓ
      obtain ⟨EA, EΞ⟩ := List.cons.inj E
      obtain ⟨A', HA, EA'⟩ := proofErase_scoped_compute_realize hstep.descent hΓ hA EΞ EA RD
      have C : IsDefEqCtx env univs [] (A :: Γ) (A' :: Γ) := .succ (.refl hΓ) HA
      have hOld : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
      have hNew : OnCtx (A' :: Γ) (env.IsType univs) := ⟨hΓ, u, HA.hasType.2⟩
      have hn' : ¬ IsProof (A' :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) :=
        fun hp => hn ((isProof_defeqCtx C).2 hp)
      obtain ⟨σ, pending, HS⟩ := HS
      refine .base ⟨A' :: Γ, A' :: Γ, 0, 0, v', w', pre, F, hNew, hNew,
        .zero [], ?_, hf.defeqDFC henv C, hn', (HS.source_convert hΔ C).forget, ?_⟩
      · simp only [proofEraseCtx, EA', EΞ]
      · simpa only [ProofShape.liftN_zero] using (proofErase_defeqCtx hOld C hf).symm
  generalize E : rawA :: Ξ = context at HP
  induction HP generalizing rawA Ξ rawA' with
  | base H =>
    obtain ⟨Γ, Γ', count, offset, v', w', pre, F, hΓ, hΓ', W, EΓ, hf, hn, HS, ES⟩ := H
    have Hpure : IteratedAmbientEqCompletion Δ v w original (proofEraseCtx Γ)
        (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)) :=
      .base ⟨Γ, Γ, 0, 0, v', w', pre, F, hΓ, hΓ, .zero [], rfl, hf, hn, HS,
        ProofShape.liftN_zero _⟩
    exact ES ▸ completion_annotation_insert hstep hΓ hΓ' W hf Hpure
      (pure hΓ hf hn HS) (EΓ.trans E.symm) RD
  | insert hΓ hΓ' W hf H ih =>
    exact completion_annotation_insert hstep hΓ hΓ' W hf H
      (fun E RD => ih RD E.symm) E.symm RD

end Lean4Lean.VEnv.Strengthening
