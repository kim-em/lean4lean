import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSortedEtaCoreOrigins
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaApplicationCleanup

/-! # Applying sorted eta origins after full-core function computation

The ambient domain and function may have arbitrary full-core histories. Actual
consumer typing still forces proof arguments where required, so applying eta
origins and removing right wrappers need only beta on the target side.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private liftN_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private subst_shift from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedAnnotationChecking
variable [Params] {D : Definitions}

/-- Typed application of a sorted eta origin simulates beta. For a proof input,
the consumer's own typing forces its argument to erase to proof, and the paired
argument is also proof because guarded short functions cannot be proof markers. -/
theorem sorted_eta_core_origin_apply (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (hA : env.HasType univs Γ₀ A₀ (.sort u))
    (hf : env.HasType univs Γ₀ f (.forallE A₀ B)) (hn : ¬ IsProof Γ₀ f)
    (H : LiftedOrigin (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A₀) (proofErase Γ₀ f)))
      n (.lam A body) g)
    (VX : AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A₀) (proofErase Γ₀ f))
      (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A₀) (proofErase Γ₀ f))) n x y)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = .app (.lam A body) x)
    (W : ContextRenaming (proofEraseCtx Γ₀) (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    ∃ out, ProofShape.BetaRed (.app g y) out ∧
      AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A₀) (proofErase Γ₀ f))
        (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A₀) (proofErase Γ₀ f))) n (body.inst x) out := by
  obtain ⟨a, b, H, EA, rfl⟩ := H
  cases H with
  | @etaL C _ HG =>
    simp only [sortedEta, ProofShape.liftN, etaArgument_liftN] at EA
    obtain ⟨rfl, rfl⟩ := ProofShape.lam.inj EA
    rw [← ProofShape.liftN_comm b n 1 0 0 (Nat.zero_le _)] at Ee ⊢
    by_cases hu : u ≈ .zero
    · obtain ⟨eF, eX, rfl, _, EF, EX⟩ := erase_app_inv Ee
      obtain ⟨eA, eB, rfl, _, EDom, _⟩ := erase_lam_inv EF
      have S := proofErase_level_core_domain_sort hs hΓ₀ hA HG.1
      obtain ⟨C₀, hC, EC⟩ := S.realize hΓ₀
      have hC0 := (IsDefEq.sortDF (hC.sort_r henv hΓ₀) (by trivial) hu).defeq hC
      have S0 := ContextSubstitution.sort W.interpretation (EC ▸ DomainSort.of_typed hΓ₀ hC0)
      simp only [subst_shift, ← EDom] at S0
      have EX0 := EX.symm.trans (proofErase_beta_proof_argument hΓ ht S0)
      rw [EX0] at VX ⊢
      obtain rfl := AmbientVariant.proof_right
        (Atom := SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A₀) (proofErase Γ₀ f)))
        (fun H => SortedEtaAtom.ne_proof
          (fun H => proofErase_level_core_descendant_ne_proof hs hΓ₀ hf hn H.2) H) VX
      simp only [etaArgument, if_pos hu, sorted_eta_proof_body_inst]
      exact ⟨_, .refl, .refl⟩
    · simp only [etaArgument, if_neg hu, retained_eta_body_inst]
      exact ⟨_, .refl, .app .refl VX⟩
  | @etaR C _ HG =>
    obtain ⟨D, b, rfl, rfl, rfl⟩ := liftN_lam_inv EA.symm
    refine ⟨(b.liftN n 1).inst y, ?_, AmbientVariant.refl.inst_pair VX⟩
    exact (ProofShape.BetaRed.app (sorted_eta_lambda_beta_of_core_origin hs hΓ₀ hA hf HG.2 C).liftN .refl).trans .beta


/-- Applying the right eta wrapper removes it by beta and retains the paired
argument. The source is an arbitrary visible application, not a lambda redex.
This is the cleanup needed when eta hides a constant-headed pattern prefix. -/
theorem sorted_eta_core_right_application_cleanup (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (hA : env.HasType univs Γ₀ A (.sort u))
    (hf : env.HasType univs Γ₀ f (.forallE A B)) (hn : ¬ IsProof Γ₀ f)
    (HG : EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f) C g)
    (VX : AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
      (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n x y)
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
  · obtain ⟨g₀, HE, EG⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
      hΓ₀ hf rfl rfl (HG.2.scoped (fun H => .base H))
    have hg := HE.hasType.2
    have hA0 := (IsDefEq.sortDF (hA.sort_r henv hΓ₀) (by trivial) hu).defeq hA
    have EX : x = .proof := proofErase_interpreted_function_proof_argument hΓ₀ hA0 hg
      W.interpretation hΓ ht (by simpa only [subst_shift, EG] using Ee)
    rw [EX] at VX
    obtain rfl := AmbientVariant.proof_right
      (Atom := SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f)))
      (fun H => SortedEtaAtom.ne_proof
        (fun H => proofErase_level_core_descendant_ne_proof hs hΓ₀ hf hn H.2) H) VX
    simpa only [etaArgument, if_pos hu, sorted_eta_proof_body_inst] using
      (ProofShape.BetaRed.beta (A := C.liftN n)
        (b := .app ((g.liftN n).liftN 1) .proof) (a := .proof))
  · simpa only [etaArgument, if_neg hu, retained_eta_body_inst] using
      (ProofShape.BetaRed.beta (A := C.liftN n)
        (b := .app ((g.liftN n).liftN 1) (.bvar 0)) (a := y))


end Lean4Lean.VEnv.Strengthening
