import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSortedEtaConsumer

/-! # Removing eta wrappers from applied pattern prefixes

An interpreted ambient function supplies a Pi carrier in the actual consumer
context, even when the consumer wrote a different representative or assignment.
This forces proof arguments where needed and permits beta cleanup of eta on the
right side of a paired application, without demanding a lambda on the left.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private subst_shift from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedAnnotationChecking
variable [Params]

/-- An interpreted ambient Pi typing transfers to any non-proof representative
with the same substituted erasure. The selected domain retains its original
sort. This is semantic typing transport, not a native recovery certificate. -/
theorem proofErase_interpreted_function_carrier
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (hA : env.HasType univs Γ₀ A (.sort u))
    (hf : env.HasType univs Γ₀ f (.forallE A B))
    (W : ContextSubstitution (proofEraseCtx Γ₀) (proofEraseCtx Γ) τ)
    (hΓ : OnCtx Γ (env.IsType univs)) (hg : env.HasType univs Γ g T) (hn : ¬ IsProof Γ g)
    (E : proofErase Γ g = (proofErase Γ₀ f).subst τ) :
    ∃ C E, env.HasType univs Γ g (.forallE C E) ∧ env.HasType univs Γ C (.sort u) := by
  obtain ⟨Γ₁, σ, hΓ₁, EΓ₁, HS, ES⟩ := W hΓ₀ rfl
  have HC := proofEraseCtx_defeq hΓ₁ hΓ EΓ₁
  have HF := hf.subst henv.orderedStrong HS hΓ₁
  have HF' := HF.defeqDFC henv HC
  have HA := (hA.subst henv.orderedStrong HS hΓ₁).defeqDFC henv HC
  have EF := (proofErase_defeqCtx hΓ₁ HC HF).symm.trans (proofErase_subst_with hΓ₁ HS hf ES)
  obtain ⟨_, HN⟩ := (proofErase_reflect hΓ hg HF' (E.trans EF.symm)).2 hn
  have HG := ((HN.defeq hΓ).symm.of_l henv hΓ HF').hasType.2
  exact ⟨A.subst σ, B.subst σ.lift, HG, HA⟩

/-- A visible application of an interpreted proof-domain function must supply
a proof-erased argument. No lambda shape or native type certificate is needed. -/
theorem proofErase_interpreted_function_proof_argument
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (hA : env.HasType univs Γ₀ A (.sort .zero))
    (hf : env.HasType univs Γ₀ f (.forallE A B))
    (W : ContextSubstitution (proofEraseCtx Γ₀) (proofEraseCtx Γ) τ)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = .app ((proofErase Γ₀ f).subst τ) x) : x = .proof := by
  obtain ⟨g, a, rfl, hn, EG, EX⟩ := erase_app_inv Ee
  obtain ⟨D, F, hg, ha⟩ := ht.app_inv henv hΓ
  obtain ⟨C, E, hgC, hC⟩ := proofErase_interpreted_function_carrier hΓ₀ hA hf W hΓ hg
    (not_isProof_fn hΓ hg ha hn) EG
  have haC := argument_at_displayed_domain hΓ hg hgC ha
  exact EX.symm.trans (proofErase_eq_proof.2 ⟨C, haC, hC⟩)

/-- Applying the right eta wrapper removes it by beta and retains the paired
argument. The source is an arbitrary visible application, not a lambda redex.
This is the cleanup needed when eta hides a constant-headed pattern prefix. -/
theorem sorted_eta_right_application_cleanup
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (hA : env.HasType univs Γ₀ A (.sort u))
    (hf : env.HasType univs Γ₀ f (.forallE A B)) (hn : ¬ IsProof Γ₀ f)
    (HG : EtaBetaOrigin (proofErase Γ₀ A) (proofErase Γ₀ f) C g)
    (VX : AmbientVariant (EtaBetaDomains (proofErase Γ₀ A) (proofErase Γ₀ f))
      (SortedEtaAtom u (EtaBetaOrigin (proofErase Γ₀ A) (proofErase Γ₀ f))) n x y)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = .app (g.liftN n) x)
    (W : ContextRenaming (proofEraseCtx Γ₀) (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    ProofShape.BetaRed (.app ((sortedEta u C g).liftN n) y) (.app (g.liftN n) y) := by
  have Eη : (sortedEta u C g).liftN n =
      .lam (C.liftN n) (.app ((g.liftN n).liftN 1) (etaArgument u)) := by
    simp only [sortedEta, ProofShape.liftN, etaArgument_liftN]
    rw [ProofShape.liftN_comm g n 1 0 0 (Nat.zero_le _)]
  rw [Eη]
  by_cases hu : u ≈ .zero
  · obtain ⟨g₀, RG, EG⟩ := proofErase_beta_replay hΓ₀ hf HG.2
    have hg := (beta_eq hΓ₀ hf RG).hasType.2
    have hA0 := (IsDefEq.sortDF (hA.sort_r henv hΓ₀) (by trivial) hu).defeq hA
    have EX : x = .proof := proofErase_interpreted_function_proof_argument hΓ₀ hA0 hg
      W.interpretation hΓ ht (by simpa only [subst_shift, EG] using Ee)
    rw [EX] at VX
    obtain rfl := AmbientVariant.proof_right
      (Atom := SortedEtaAtom u (EtaBetaOrigin (proofErase Γ₀ A) (proofErase Γ₀ f)))
      (fun H => SortedEtaAtom.ne_proof
        (fun H => proofErase_beta_descendant_ne_proof hΓ₀ hf hn H.2) H) VX
    simpa only [etaArgument, if_pos hu, sorted_eta_proof_body_inst] using
      (ProofShape.BetaRed.beta (A := C.liftN n)
        (b := .app ((g.liftN n).liftN 1) .proof) (a := .proof))
  · simpa only [etaArgument, if_neg hu, retained_eta_body_inst] using
      (ProofShape.BetaRed.beta (A := C.liftN n)
        (b := .app ((g.liftN n).liftN 1) (.bvar 0)) (a := y))

end Lean4Lean.VEnv.Strengthening
