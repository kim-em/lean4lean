import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSortedEtaOrigins

/-! # All input sorts in arbitrary-function eta consumer beta transport

Typing supplies proof arguments at applied eta origins and restores exposed
lambda bodies. Every typed function and typed consumer is covered, with no
input-sort restriction and no assumed native or domain comparison coverage.
The latter certificates are still explicit premises of inferred readout.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Source typing and concrete histories discharge both origin interactions
for every input sort. The consumer context may contain any local prefix. -/
theorem sorted_eta_beta_left
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (hA : env.HasType univs Γ₀ A (.sort u))
    (hf : env.HasType univs Γ₀ f (.forallE A B)) (hn : ¬ IsProof Γ₀ f)
    (R : ProofShape.BetaRed a a')
    (V : AmbientVariant (EtaBetaDomains (proofErase Γ₀ A) (proofErase Γ₀ f))
      (SortedEtaAtom u (EtaBetaOrigin (proofErase Γ₀ A) (proofErase Γ₀ f))) n a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = a)
    (W : ContextRenaming (proofEraseCtx Γ₀) (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    ∃ b', ProofShape.BetaRed b b' ∧
      AmbientVariant (EtaBetaDomains (proofErase Γ₀ A) (proofErase Γ₀ f))
        (SortedEtaAtom u (EtaBetaOrigin (proofErase Γ₀ A) (proofErase Γ₀ f))) n a' b' :=
  ambient_variant_typed_beta_left
    (Guard := EtaBetaDomains (proofErase Γ₀ A) (proofErase Γ₀ f))
    (Atom := SortedEtaAtom u (EtaBetaOrigin (proofErase Γ₀ A) (proofErase Γ₀ f)))
    (fun H R => H.beta_left R) (fun H R => sorted_eta_origin_beta hΓ₀ hA hf hn H R)
    (fun H VX hΓ ht Ee W => sorted_eta_origin_apply hΓ₀ hA hf hn H VX hΓ ht Ee W)
    R V hΓ ht Ee W

/-- Every typed function gives a sorted eta origin, or identical proof erasures.
Neither the input sort nor proof-valued output is restricted. -/
theorem proofErase_sorted_eta_variant
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) :
    AmbientVariant (EtaBetaDomains (proofErase Γ A) (proofErase Γ f))
      (SortedEtaAtom u (EtaBetaOrigin (proofErase Γ A) (proofErase Γ f))) 0
      (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) (proofErase Γ f) := by
  by_cases hn : IsProof Γ f
  · rw [proofErase_eq_proof.2 hn,
      proofErase_eq_proof.2 ((isProof_congr hΓ (IsDefEq.eta hf)).2 hn)]
    exact .refl
  · rw [proofErase_nativeEtaExpansion hΓ hA hf hn]
    exact .origin ⟨sortedEta u (proofErase Γ A) (proofErase Γ f), proofErase Γ f,
      .etaL ⟨.refl, .refl⟩, by simp only [ProofShape.liftN_zero, sortedEta],
      by simp only [ProofShape.liftN_zero]⟩

/-- Every occurrence in any typed consumer retains the classified ambient
origin, including dependent annotations and both fresh-argument erasures. -/
theorem proofErase_sorted_eta_consumer_variant
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (ht : env.HasType univs (.forallE A B :: Γ) t T) :
    AmbientVariant (EtaBetaDomains (proofErase Γ A) (proofErase Γ f))
      (SortedEtaAtom u (EtaBetaOrigin (proofErase Γ A) (proofErase Γ f))) 0
      (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) (proofErase Γ (t.inst f)) := by
  have hΓF : OnCtx (.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, hf.isType henv hΓ⟩
  rw [proofErase_instN hΓF (IsDefEq.eta hf).hasType.1 Ctx.InstN.zero ht,
    proofErase_instN hΓF hf Ctx.InstN.zero ht]
  simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN]
  apply AmbientVariant.subst_images
  intro i
  cases i with
  | zero => exact proofErase_sorted_eta_variant hΓ hA hf
  | succ i => exact .refl

/-- Unconditional beta residual coverage of eta in every typed consumer, for
arbitrary supplied functions and every input sort. All exposed domain pairs
remain recorded; no native recovery, comparison or normalization is assumed. -/
theorem proofErase_sorted_eta_consumer_beta_residuals
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (RL : ProofShape.BetaRed (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) left)
    (RR : ProofShape.BetaRed (proofErase Γ (t.inst f)) right) :
    ∃ left' right', ProofShape.BetaRed left left' ∧ ProofShape.BetaRed right right' ∧
      AmbientVariant (EtaBetaDomains (proofErase Γ A) (proofErase Γ f))
        (SortedEtaAtom u (EtaBetaOrigin (proofErase Γ A) (proofErase Γ f))) 0 left' right' := by
  by_cases hn : IsProof Γ f
  · have hΓF : OnCtx (.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, hf.isType henv hΓ⟩
    have EE : proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0)))) = proofErase Γ (t.inst f) := by
      rw [proofErase_instN hΓF (IsDefEq.eta hf).hasType.1 Ctx.InstN.zero ht,
        proofErase_instN hΓF hf Ctx.InstN.zero ht, proofErase_eq_proof.2 hn,
        proofErase_eq_proof.2 ((isProof_congr hΓ (IsDefEq.eta hf)).2 hn)]
    rw [EE] at RL
    obtain ⟨out, PL, PR⟩ := RL.raw_confluent RR
    exact ⟨out, out, PL, PR, .refl⟩
  · have V := proofErase_sorted_eta_consumer_variant hΓ hA hf ht
    have hleft := ht.instN henv Ctx.InstN.zero (IsDefEq.eta hf).hasType.1
    have hright := ht.instN henv Ctx.InstN.zero hf
    obtain ⟨b₁, RB₁, V₁⟩ := sorted_eta_beta_left hΓ hA hf hn RL V hΓ hleft rfl ContextRenaming.identity
    obtain ⟨q', RQ, RB₁'⟩ := RR.raw_confluent RB₁
    obtain ⟨e₁, RE, EE⟩ := proofErase_beta_replay hΓ hright RB₁
    obtain ⟨p', RP, V₂⟩ := sorted_eta_beta_left hΓ hA hf hn RB₁'
      (V₁.symm (fun H => H.symm) (fun H => H.symm))
      hΓ (beta_eq hΓ hright RE).hasType.2 EE ContextRenaming.identity
    exact ⟨p', q', RP, RQ, V₂.symm (fun H => H.symm) (fun H => H.symm)⟩

/-- Sorted eta residuals in arbitrary consumers have inferred readout from
ambient origin and domain certificates. Establishing that certificate coverage
for all source functions remains missing; beta transport itself is supplied. -/
theorem proofErase_sorted_eta_consumer_beta_check
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (hguard : ∀ {C E}, EtaBetaDomains (proofErase Γ A) (proofErase Γ f) C E →
      ComputedJointCompare Step (proofEraseCtx Γ) false C E)
    (heta : ∀ {C g mode}, EtaBetaOrigin (proofErase Γ A) (proofErase Γ f) C g →
      ComputedJointCompare Step (proofEraseCtx Γ) mode (sortedEta u C g) g)
    (RL : ProofShape.BetaRed (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) left)
    (RR : ProofShape.BetaRed (proofErase Γ (t.inst f)) right) :
    ComputedJointCompare Step (proofEraseCtx Γ) mode left right := by
  obtain ⟨left', right', PL, PR, V⟩ := proofErase_sorted_eta_consumer_beta_residuals hΓ hA hf ht RL RR
  have hleft := ht.instN henv Ctx.InstN.zero (IsDefEq.eta hf).hasType.1
  obtain ⟨e, RE, EE⟩ := proofErase_beta_replay hΓ hleft (RL.trans PL)
  have HO {a b mode} (H : SortedEtaAtom u (EtaBetaOrigin (proofErase Γ A) (proofErase Γ f)) a b) :
      ComputedJointCompare Step (proofEraseCtx Γ) mode a b := by
    cases H with
    | etaL H => exact heta H
    | etaR H => exact (heta H).symm
  exact .compute (.beta PL) (.beta PR)
    (ambient_variant_computed_check hrename (fun H => hguard H) (fun H => HO H) V
      hΓ (beta_eq hΓ hleft RE).hasType.2 EE ContextRenaming.identity)

/-- Native-domain certificates discharge every sorted eta atom, including proof
inputs. The remaining exposed-domain comparison and native coverage assumptions
are explicit; arbitrary consumer substitution is handled by the proved transport. -/
theorem proofErase_sorted_eta_consumer_beta_check_of_native_domains
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (hguard : ∀ {C E}, EtaBetaDomains (proofErase Γ A) (proofErase Γ f) C E →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1))
        (proofEraseCtx Γ) false C E)
    (Hnative : ∀ {C g}, EtaBetaOrigin (proofErase Γ A) (proofErase Γ f) C g →
      ∃ X Y, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D stage)
        (proofEraseCtx Γ) g (.forallE X Y) ∧ DomainSort (proofEraseCtx Γ) X u ∧
        ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1))
          (proofEraseCtx Γ) false C X)
    (RL : ProofShape.BetaRed (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) left)
    (RR : ProofShape.BetaRed (proofErase Γ (t.inst f)) right) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1))
      (proofEraseCtx Γ) mode left right := by
  apply proofErase_sorted_eta_consumer_beta_check
    (erased_static_structure_eta_expansion_stage_rename heq hs (stage+1))
    hΓ hA hf ht (fun H => hguard H) ?_ RL RR
  intro C g mode H
  obtain ⟨X, Y, RN, SC, HX⟩ := Hnative H
  obtain ⟨g₀, RG, EG⟩ := proofErase_beta_replay hΓ hf H.2
  have hg := (beta_eq hΓ hf RG).hasType.2
  rw [← EG] at RN ⊢
  exact classified_eta_native_domain_check hΓ hA hg (.inl rfl) RN SC HX

end Lean4Lean.VEnv.Strengthening
