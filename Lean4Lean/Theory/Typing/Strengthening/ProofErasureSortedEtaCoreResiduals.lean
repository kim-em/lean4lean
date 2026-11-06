import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaCoreConsumer

/-! # Independent full-core residuals of eta in arbitrary typed consumers

Every typed function and input sort is covered. Exposed domains and residual eta
origins keep concrete histories; inferred readout still requires certificates
for those recorded pairs, whose general coverage remains open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- Every typed function gives a sorted eta origin, or identical proof erasures.
Neither the input sort nor proof-valued output is restricted. -/
theorem proofErase_sorted_eta_core_variant
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) :
    AmbientVariant (EtaCoreDomains D (proofErase Γ A) (proofErase Γ f))
      (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ A) (proofErase Γ f))) 0
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
theorem proofErase_sorted_eta_core_consumer_variant
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (ht : env.HasType univs (.forallE A B :: Γ) t T) :
    AmbientVariant (EtaCoreDomains D (proofErase Γ A) (proofErase Γ f))
      (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ A) (proofErase Γ f))) 0
      (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) (proofErase Γ (t.inst f)) := by
  have hΓF : OnCtx (.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, hf.isType henv hΓ⟩
  rw [proofErase_instN hΓF (IsDefEq.eta hf).hasType.1 Ctx.InstN.zero ht,
    proofErase_instN hΓF hf Ctx.InstN.zero ht]
  simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN]
  apply AmbientVariant.subst_images
  intro i
  cases i with
  | zero => exact proofErase_sorted_eta_core_variant hΓ hA hf
  | succ i => exact .refl

/-- Full-core residual coverage of eta in every typed consumer, for
arbitrary supplied functions and every input sort. All exposed domain pairs
remain recorded; source confluence is the only joining premise. No native
recovery, comparison or normalization is assumed. -/
theorem proofErase_sorted_eta_consumer_core_residuals
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (RL : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) left)
    (RR : Compute (ErasedLevelCore D) (proofErase Γ (t.inst f)) right) :
    ∃ left' right', Compute (ErasedLevelCore D) left left' ∧ Compute (ErasedLevelCore D) right right' ∧
      AmbientVariant (EtaCoreDomains D (proofErase Γ A) (proofErase Γ f))
        (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ A) (proofErase Γ f))) 0 left' right' := by
  have hright := ht.instN henv Ctx.InstN.zero hf
  by_cases hn : IsProof Γ f
  · have hΓF : OnCtx (.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, hf.isType henv hΓ⟩
    have EE : proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0)))) = proofErase Γ (t.inst f) := by
      rw [proofErase_instN hΓF (IsDefEq.eta hf).hasType.1 Ctx.InstN.zero ht,
        proofErase_instN hΓF hf Ctx.InstN.zero ht, proofErase_eq_proof.2 hn,
        proofErase_eq_proof.2 ((isProof_congr hΓ (IsDefEq.eta hf)).2 hn)]
    rw [EE] at RL
    obtain ⟨out, PL, PR⟩ := hc hΓ hright RL RR
    exact ⟨out, out, PL, PR, .refl⟩
  · have V := proofErase_sorted_eta_core_consumer_variant (D := D) hΓ hA hf ht
    have hleft := ht.instN henv Ctx.InstN.zero (IsDefEq.eta hf).hasType.1
    obtain ⟨b₁, RB₁, V₁⟩ := sorted_eta_core_left hs hΓ hA hf hn RL V hΓ hleft rfl ContextRenaming.identity
    obtain ⟨q', RQ, RB₁'⟩ := hc hΓ hright RR RB₁
    obtain ⟨e₁, RE, EE⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
      hΓ hright rfl rfl (RB₁.scoped (fun H => .base H))
    obtain ⟨p', RP, V₂⟩ := sorted_eta_core_left hs hΓ hA hf hn RB₁'
      (V₁.symm (fun H => H.symm) (fun H => H.symm))
      hΓ RE.hasType.2 EE ContextRenaming.identity
    exact ⟨p', q', RP, RQ, V₂.symm (fun H => H.symm) (fun H => H.symm)⟩

/-- Sorted eta residuals in arbitrary consumers have inferred readout from
ambient origin and domain certificates. Establishing that certificate coverage
for all source functions remains missing; full-core transport itself is supplied. -/
theorem proofErase_sorted_eta_consumer_core_check
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hcore : ∀ {Δ a b}, ErasedLevelCore D a b → Step Δ a b)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (hguard : ∀ {C E}, EtaCoreDomains D (proofErase Γ A) (proofErase Γ f) C E →
      ComputedJointCompare Step (proofEraseCtx Γ) false C E)
    (heta : ∀ {C g mode}, EtaCoreOrigin D (proofErase Γ A) (proofErase Γ f) C g →
      ComputedJointCompare Step (proofEraseCtx Γ) mode (sortedEta u C g) g)
    (RL : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) left)
    (RR : Compute (ErasedLevelCore D) (proofErase Γ (t.inst f)) right) :
    ComputedJointCompare Step (proofEraseCtx Γ) mode left right := by
  obtain ⟨left', right', PL, PR, V⟩ := proofErase_sorted_eta_consumer_core_residuals hs hc hΓ hA hf ht RL RR
  have hleft := ht.instN henv Ctx.InstN.zero (IsDefEq.eta hf).hasType.1
  obtain ⟨e, RE, EE⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hleft rfl rfl ((RL.trans PL).scoped (fun H => .base H))
  have HO {a b mode} (H : SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ A) (proofErase Γ f)) a b) :
      ComputedJointCompare Step (proofEraseCtx Γ) mode a b := by
    cases H with
    | etaL H => exact heta H
    | etaR H => exact (heta H).symm
  exact .compute (PL.scoped (fun H => .base (hcore H))) (PR.scoped (fun H => .base (hcore H)))
    (ambient_variant_computed_check hrename (fun H => hguard H) (fun H => HO H) V
      hΓ RE.hasType.2 EE ContextRenaming.identity)


namespace StoredCore
/-- For actual stored definitions and concrete patterns, the existing core
confluence theorem supplies the joining premise of arbitrary eta-consumer
residual coverage. Functions, consumers and input sorts are unrestricted. -/
theorem sorted_eta_consumer_core_residuals
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (RL : Compute (ErasedLevelCore (Definitions.ofEnv env univs henv))
      (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) left)
    (RR : Compute (ErasedLevelCore (Definitions.ofEnv env univs henv))
      (proofErase Γ (t.inst f)) right) :
    ∃ left' right', Compute (ErasedLevelCore (Definitions.ofEnv env univs henv)) left left' ∧
      Compute (ErasedLevelCore (Definitions.ofEnv env univs henv)) right right' ∧
      AmbientVariant (EtaCoreDomains (Definitions.ofEnv env univs henv) (proofErase Γ A) (proofErase Γ f))
        (SortedEtaAtom u (EtaCoreOrigin (Definitions.ofEnv env univs henv) (proofErase Γ A) (proofErase Γ f)))
        0 left' right' :=
  proofErase_sorted_eta_consumer_core_residuals (Definitions.ofEnv_sound henv)
    (typed_level_core_confluence hcon) hΓ hA hf ht RL RR
end StoredCore

end Lean4Lean.VEnv.Strengthening
