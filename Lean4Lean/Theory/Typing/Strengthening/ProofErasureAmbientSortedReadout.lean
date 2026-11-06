import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaCoreDomainBoundary

/-! # Reading ambient variants from shared-sort conversion certificates

An exposed lambda annotation needs its retained common-mode conversion and
actual sort witnesses. No promotion to inferred comparison of the domains is
needed for the enclosing inferred lambda comparison.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ambient_cons subst_shift
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedAnnotationChecking
variable [Params]

/-- Shared-sort common domain checks suffice at exposed annotation marks.
Structural syntax and eta atoms retain their existing checking modes. -/
theorem ambient_variant_sorted_domain_check
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hguard : ∀ {A C}, Guard A C →
      ∃ u, DomainSort Δ A u ∧ DomainSort Δ C u ∧ ComputedJointCompare Step Δ true A C)
    (horigin : ∀ {a b mode}, Atom a b → ComputedJointCompare Step Δ mode a b)
    (V : AmbientVariant Guard Atom n a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = a)
    (W : ContextRenaming Δ (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    ComputedJointCompare Step (proofEraseCtx Γ) mode a b := by
  induction V generalizing Γ e T mode with
  | refl => exact .leaf .refl
  | app VF VX ihf ihx =>
    obtain ⟨f, x, rfl, _, EF, EX⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
    exact .app (ihf hΓ hf EF W) (ihx hΓ hx EX W)
  | proj V ih =>
    obtain ⟨m, rfl, _, EM⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj (ih hΓ hm.hasType.2 EM W)
  | lam VA VB ihA ihB =>
    obtain ⟨A, body, rfl, _, EA, EB⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    apply ComputedJointCheck.lam (ihA hΓ hA EA W)
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    simpa only [proofEraseCtx, EA] using ihB hΓA hb EB (ambient_cons W hΓ hA)
  | forallE VA VB ihA ihB =>
    obtain ⟨A, body, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.forallE_inv henv
    apply ComputedJointCheck.forallE (ihA hΓ hA EA W)
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    simpa only [proofEraseCtx, EA] using ihB hΓA hb EB (ambient_cons W hΓ hA)
  | marked HG VB ihB =>
    obtain ⟨A, body, rfl, _, EA, EB⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have HB := ihB (mode := mode) hΓA hb EB (ambient_cons W hΓ hA)
    obtain ⟨v, SA, SC, HG⟩ := hguard HG
    have HG' := HG.rename hrename W
    have SA' := ContextSubstitution.sort W.interpretation SA
    have SC' := ContextSubstitution.sort W.interpretation SC
    simp only [JointCheckKind.subst, subst_shift] at HG' SA' SC'
    simp only [proofEraseCtx, EA] at HB
    exact .lamSorted SA' SC' HG' HB
  | origin HO =>
    obtain ⟨a, b, HO, rfl, rfl⟩ := HO
    have H := (horigin (mode := mode) HO).rename hrename W
    simpa only [JointCheckKind.subst, subst_shift] using H

/-- Full-core eta consumer readout uses common domain-conversion evidence.
The actual source histories supply the shared sort witnesses; the conversion
certificates themselves remain explicit and are not synthesized from typing. -/
theorem proofErase_sorted_eta_consumer_core_sorted_check
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hcore : ∀ {Δ a b}, ErasedLevelCore D a b → Step Δ a b)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (hguard : ∀ {C E}, EtaCoreDomains D (proofErase Γ A) (proofErase Γ f) C E →
      ComputedJointCompare Step (proofEraseCtx Γ) true C E)
    (heta : ∀ {C g mode}, EtaCoreOrigin D (proofErase Γ A) (proofErase Γ f) C g →
      ComputedJointCompare Step (proofEraseCtx Γ) mode (sortedEta u C g) g)
    (RL : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) left)
    (RR : Compute (ErasedLevelCore D) (proofErase Γ (t.inst f)) right) :
    ComputedJointCompare Step (proofEraseCtx Γ) mode left right := by
  obtain ⟨left', right', PL, PR, V⟩ := proofErase_sorted_eta_consumer_core_residuals hs hc hΓ hA hf ht RL RR
  have hleft := ht.instN henv Ctx.InstN.zero (IsDefEq.eta hf).hasType.1
  obtain ⟨e, RE, EE⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hleft rfl rfl ((RL.trans PL).scoped (fun H => .base H))
  have HD {C E} (H : EtaCoreDomains D (proofErase Γ A) (proofErase Γ f) C E) :
      ∃ v, DomainSort (proofEraseCtx Γ) C v ∧ DomainSort (proofEraseCtx Γ) E v ∧
        ComputedJointCompare Step (proofEraseCtx Γ) true C E := by
    obtain ⟨C₀, E₀, hC, hE, _, EC, EE⟩ := proofErase_eta_core_domain_realize hs hΓ hA hf H
    exact ⟨u, EC ▸ DomainSort.of_typed hΓ hC, EE ▸ DomainSort.of_typed hΓ hE, hguard H⟩
  have HO {a b mode} (H : SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ A) (proofErase Γ f)) a b) :
      ComputedJointCompare Step (proofEraseCtx Γ) mode a b := by
    cases H with
    | etaL H => exact heta H
    | etaR H => exact (heta H).symm
  exact .compute (PL.scoped (fun H => .base (hcore H))) (PR.scoped (fun H => .base (hcore H)))
    (ambient_variant_sorted_domain_check hrename (fun H => HD H) (fun H => HO H) V
      hΓ RE.hasType.2 EE ContextRenaming.identity)

end Lean4Lean.VEnv.Strengthening
