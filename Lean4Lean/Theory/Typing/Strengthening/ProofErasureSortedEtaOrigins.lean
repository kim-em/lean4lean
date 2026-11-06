import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAmbientTypedBeta
import Lean4Lean.Theory.Typing.Strengthening.FreshBetaReflection

/-! # Protected eta origins classified by their actual input sort

The same origin syntax handles retained and proof-erased fresh arguments.
Actual ambient typing validates reflection through the erased opened body and
beta of an exposed lambda. Applying the long proof-domain form uses the typing
of the consumer to establish that its supplied argument is a proof marker.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private beta_eq erase_app_inv erase_lam_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private liftN_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private subst_shift from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedAnnotationChecking

namespace ProofShape
/-- Eta syntax retains the argument classification from the input sort. -/
noncomputable def sortedEta (u : VLevel) (A f : ProofShape) : ProofShape :=
  .lam A (.app (f.liftN 1) (etaArgument u))

/-- Both orientations of an eta origin carry the same sort classification. -/
inductive SortedEtaAtom (u : VLevel) (EtaGuard : ProofShape → ProofShape → Prop) :
    ProofShape → ProofShape → Prop where
  | etaL : EtaGuard A f → SortedEtaAtom u EtaGuard (sortedEta u A f) f
  | etaR : EtaGuard A f → SortedEtaAtom u EtaGuard f (sortedEta u A f)

/-- Reversing an origin preserves its recorded domain, function and input sort. -/
theorem SortedEtaAtom.symm (H : SortedEtaAtom u EtaGuard a b) : SortedEtaAtom u EtaGuard b a := by
  cases H with
  | etaL H => exact .etaR H
  | etaR H => exact .etaL H

/-- If every guarded short function is non-proof, no atom starts at proof. -/
theorem SortedEtaAtom.ne_proof
    (hf : ∀ {A f}, EtaGuard A f → f ≠ .proof) (H : SortedEtaAtom u EtaGuard a b) : a ≠ .proof := by
  cases H with
  | etaL H => intro E; cases E
  | etaR H => exact hf H

/-- Instantiating an erased eta body keeps its proof argument literally. -/
theorem sorted_eta_proof_body_inst :
    (ProofShape.app (f.liftN 1) .proof).inst x = .app f .proof := by
  simp only [inst_eq_subst, Subst.liftN, subst, Subst.one, lift_subst_cons, subst_id]
end ProofShape

variable [Params]

/-- Typed beta reflection keeps the exact eta argument, including a proof
marker. The returned function path is beta-only, so its original history is
retained without introducing declaration or other core steps. -/
theorem proofErase_beta_fresh_application_classified
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (R : ProofShape.BetaRed (.app ((proofErase Γ f).liftN 1) (etaArgument u)) body) :
    ∃ g, ProofShape.BetaRed (proofErase Γ f) g ∧ ClassifiedEtaBody u body g := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  obtain ⟨_, _, hopen⟩ := (IsDefEq.eta hf).hasType.1.lam_inv henv hΓ
  have E := proofErase_eta_body hΓ hA hf hn
  obtain ⟨out, R0, EO⟩ := proofErase_beta_replay hΓA hopen (E.symm ▸ R)
  obtain ⟨g, RF, H⟩ := beta_fresh_application R0
  have HF := beta_eq hΓ hf RF
  have hg := HF.hasType.2
  have hng := mt (isProof_congr hΓ HF).2 hn
  refine ⟨proofErase Γ g, proofErase_beta_forward hΓ hf RF, ?_⟩
  rcases H with rfl | ⟨C, rfl⟩
  · exact .inl (EO.symm.trans (proofErase_eta_body hΓ hA hg hng))
  · obtain ⟨⟨v, hC⟩, _, hb⟩ := hg.lam_inv henv hΓ
    obtain ⟨⟨_, HCA⟩, _⟩ := ((HasType.lam hC hb).uniqU henv hΓ hg).forallE_inv henv hΓ
    have EB := proofErase_defeqCtx (Γ₁ := C :: Γ) ⟨hΓ, _, hC⟩ (.succ .zero HCA) hb
    refine .inr ⟨proofErase Γ C, ?_⟩
    rw [show proofErase Γ (.lam C out) =
      .lam (proofErase Γ C) (proofErase (C :: Γ) out) from if_neg hng, EB, EO]

/-- A beta descendant of a typed non-proof function cannot become a marker. -/
theorem proofErase_beta_descendant_ne_proof
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T) (hn : ¬ IsProof Γ f)
    (R : ProofShape.BetaRed (proofErase Γ f) g) : g ≠ .proof := by
  obtain ⟨g₀, RG, EG⟩ := proofErase_beta_replay hΓ hf R
  intro E
  exact hn ((isProof_congr hΓ (beta_eq hΓ hf RG)).2 (proofErase_eq_proof.1 (EG.trans E)))

/-- A computed written annotation retains its actual sort witness. -/
theorem proofErase_beta_domain_sort
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (R : ProofShape.BetaRed (proofErase Γ A) C) : DomainSort (proofEraseCtx Γ) C u := by
  obtain ⟨C₀, RC, EC⟩ := proofErase_beta_replay hΓ hA R
  exact EC ▸ DomainSort.of_typed hΓ (beta_eq hΓ hA RC).hasType.2

/-- A lambda exposed by the supplied function restores its exact erased body
under eta beta at the original input sort, including proposition inputs. -/
theorem sorted_eta_lambda_beta_of_origin
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ProofShape.BetaRed (proofErase Γ f) (.lam C body)) (X : ProofShape) :
    ProofShape.BetaRed (sortedEta u X (.lam C body)) (.lam X body) := by
  obtain ⟨g, RG, EG⟩ := proofErase_beta_replay hΓ hf R
  have hg := (beta_eq hΓ hf RG).hasType.2
  obtain ⟨C₀, b, rfl, _, EC, EB⟩ := erase_lam_inv EG
  obtain ⟨⟨v, hC⟩, _, hb⟩ := hg.lam_inv henv hΓ
  obtain ⟨⟨_, HCA⟩, _⟩ := ((HasType.lam hC hb).uniqU henv hΓ hg).forallE_inv henv hΓ
  have hCu := hA.defeqU_l henv hΓ HCA.toU.symm
  simpa only [EC, EB, sortedEta] using proofErase_eta_lambda_beta hΓ hCu hb X

/-- Actual source histories simulate beta inside either orientation of a
sorted eta origin. Crossing the opened boundary records the exposed domain. -/
theorem sorted_eta_origin_beta
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (H : LiftedOrigin (SortedEtaAtom u (EtaBetaOrigin (proofErase Γ A) (proofErase Γ f))) n a b)
    (R : ProofShape.BetaRed a a') :
    ∃ b', ProofShape.BetaRed b b' ∧
      AmbientVariant (EtaBetaDomains (proofErase Γ A) (proofErase Γ f))
        (SortedEtaAtom u (EtaBetaOrigin (proofErase Γ A) (proofErase Γ f))) n a' b' := by
  obtain ⟨x, y, H, rfl, rfl⟩ := H
  obtain ⟨out, R0, rfl⟩ := R.liftN_inv
  cases H with
  | @etaL C g HG =>
    obtain ⟨C', body, rfl, RC, RB⟩ := R0.lam_inv
    obtain ⟨g₀, RG, EG⟩ := proofErase_beta_replay hΓ hf HG.2
    have HE := beta_eq hΓ hf RG
    have hng := mt (isProof_congr hΓ HE).2 hn
    obtain ⟨g', RF, HR⟩ := proofErase_beta_fresh_application_classified hΓ hA HE.hasType.2 hng
      (by simpa only [EG] using RB)
    rw [EG] at RF
    have HG' : EtaBetaOrigin (proofErase Γ A) (proofErase Γ f) C' g' :=
      ⟨HG.1.trans RC, HG.2.trans RF⟩
    refine ⟨g'.liftN n, RF.liftN, ?_⟩
    rcases HR with rfl | ⟨D, rfl⟩
    · exact .origin ⟨sortedEta u C' g', g', .etaL HG', rfl, rfl⟩
    · exact .marked (.inl ⟨HG'.1, body, HG'.2⟩) .refl
  | @etaR C g HG =>
    refine ⟨(sortedEta u C out).liftN n, ?_, ?_⟩
    · exact (ProofShape.BetaRed.lam .refl (.app R0.liftN .refl)).liftN
    · exact .origin ⟨out, sortedEta u C out, .etaR ⟨HG.1, HG.2.trans R0⟩, rfl, rfl⟩

/-- Typed application of a sorted eta origin simulates beta. For a proof input,
the consumer's own typing forces its argument to erase to proof, and the paired
argument is also proof because guarded short functions cannot be proof markers. -/
theorem sorted_eta_origin_apply
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (hA : env.HasType univs Γ₀ A₀ (.sort u))
    (hf : env.HasType univs Γ₀ f (.forallE A₀ B)) (hn : ¬ IsProof Γ₀ f)
    (H : LiftedOrigin (SortedEtaAtom u (EtaBetaOrigin (proofErase Γ₀ A₀) (proofErase Γ₀ f)))
      n (.lam A body) g)
    (VX : AmbientVariant (EtaBetaDomains (proofErase Γ₀ A₀) (proofErase Γ₀ f))
      (SortedEtaAtom u (EtaBetaOrigin (proofErase Γ₀ A₀) (proofErase Γ₀ f))) n x y)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = .app (.lam A body) x)
    (W : ContextRenaming (proofEraseCtx Γ₀) (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    ∃ out, ProofShape.BetaRed (.app g y) out ∧
      AmbientVariant (EtaBetaDomains (proofErase Γ₀ A₀) (proofErase Γ₀ f))
        (SortedEtaAtom u (EtaBetaOrigin (proofErase Γ₀ A₀) (proofErase Γ₀ f))) n (body.inst x) out := by
  obtain ⟨a, b, H, EA, rfl⟩ := H
  cases H with
  | @etaL C _ HG =>
    simp only [sortedEta, ProofShape.liftN, etaArgument_liftN] at EA
    obtain ⟨rfl, rfl⟩ := ProofShape.lam.inj EA
    rw [← ProofShape.liftN_comm b n 1 0 0 (Nat.zero_le _)] at Ee ⊢
    by_cases hu : u ≈ .zero
    · obtain ⟨eF, eX, rfl, _, EF, EX⟩ := erase_app_inv Ee
      obtain ⟨eA, eB, rfl, _, EDom, _⟩ := erase_lam_inv EF
      have S := proofErase_beta_domain_sort hΓ₀ hA HG.1
      obtain ⟨C₀, hC, EC⟩ := S.realize hΓ₀
      have hC0 := (IsDefEq.sortDF (hC.sort_r henv hΓ₀) (by trivial) hu).defeq hC
      have S0 := ContextSubstitution.sort W.interpretation (EC ▸ DomainSort.of_typed hΓ₀ hC0)
      simp only [subst_shift, ← EDom] at S0
      have EX0 := EX.symm.trans (proofErase_beta_proof_argument hΓ ht S0)
      rw [EX0] at VX ⊢
      obtain rfl := AmbientVariant.proof_right
        (Atom := SortedEtaAtom u (EtaBetaOrigin (proofErase Γ₀ A₀) (proofErase Γ₀ f)))
        (fun H => SortedEtaAtom.ne_proof
          (fun H => proofErase_beta_descendant_ne_proof hΓ₀ hf hn H.2) H) VX
      simp only [etaArgument, if_pos hu, sorted_eta_proof_body_inst]
      exact ⟨_, .refl, .refl⟩
    · simp only [etaArgument, if_neg hu, retained_eta_body_inst]
      exact ⟨_, .refl, .app .refl VX⟩
  | @etaR C _ HG =>
    obtain ⟨D, b, rfl, rfl, rfl⟩ := liftN_lam_inv EA.symm
    refine ⟨(b.liftN n 1).inst y, ?_, AmbientVariant.refl.inst_pair VX⟩
    exact (ProofShape.BetaRed.app (sorted_eta_lambda_beta_of_origin hΓ₀ hA hf HG.2 C).liftN .refl).trans .beta

end Lean4Lean.VEnv.Strengthening
