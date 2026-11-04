import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaEtaCoreJoin

/-! # Two native eta guards at the same typed source

The selected domains may differ, but their sort witnesses classify the fresh
argument identically. A common reduct of the native Pi types then joins the
two long forms by annotation computation alone. Neutral short sources are
allowed; neither long form is required to reduce to that short source.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape

/-- Equivalent universe levels choose the same erased eta argument. -/
theorem ProofShape.etaArgument_equiv (H : u ≈ v) : etaArgument u = etaArgument v := by
  have E : (u ≈ .zero) ↔ (v ≈ .zero) :=
    ⟨fun h => H.symm.trans h, fun h => H.trans h⟩
  unfold etaArgument
  by_cases hu : u ≈ .zero
  · rw [if_pos hu, if_pos (E.1 hu)]
  · rw [if_neg hu, if_neg (fun hv => hu (E.2 hv))]

variable [Params]
/-- A native Pi guard's sort witness is realized at its actual recovered
domain. No typing at a preselected Pi is assumed. -/
theorem proofErase_native_eta_domain_realize
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (RN : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) (.forallE X Y))
    (SD : DomainSort (proofEraseCtx Γ) X u) :
    ∃ A B, env.HasType univs Γ f (.forallE A B) ∧ env.HasType univs Γ A (.sort u) ∧
      proofErase Γ A = X ∧ proofErase (A :: Γ) B = Y := by
  obtain ⟨A, B, hfAB, EA, EB⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ hΓ
    (show Ctx.LiftN 0 0 Γ Γ from .zero []) hf
    (by simpa only [ProofShape.liftN_zero] using RN)
  simp only [ProofShape.liftN_zero] at EA EB
  obtain ⟨_, hPi⟩ := hfAB.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _⟩ := hPi.forallE_inv henv
  have SD' : DomainSort (proofEraseCtx Γ) ((proofErase Γ A).liftN 0) u := by
    simpa only [ProofShape.liftN_zero, EA] using SD
  exact ⟨A, B, hfAB, SD'.descend hΓ hΓ (Ctx.LiftN.zero []) hA, EA, EB⟩

/-- Independently recovered eta domains at the same source have equivalent
sort levels. Thus one guard cannot erase the fresh argument while the other
retains it, even when their annotations or recovery relations differ. -/
theorem proofErase_native_eta_domains_equiv
    (hleft : ErasedScopedPrimitiveDescent Left) (hright : ErasedScopedPrimitiveDescent Right)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (RL : ScopedTypeRecovery Left (proofEraseCtx Γ) (proofErase Γ f) (.forallE X Y))
    (RR : ScopedTypeRecovery Right (proofEraseCtx Γ) (proofErase Γ f) (.forallE X' Y'))
    (SL : DomainSort (proofEraseCtx Γ) X u) (SR : DomainSort (proofEraseCtx Γ) X' v) : u ≈ v := by
  obtain ⟨A, B, hfAB, hA, _, _⟩ := proofErase_native_eta_domain_realize hleft hΓ hf RL SL
  obtain ⟨A', B', hfAB', hA', _, _⟩ := proofErase_native_eta_domain_realize hright hΓ hf RR SR
  obtain ⟨⟨_, HA⟩, _⟩ := (hfAB.uniqU henv hΓ hfAB').forallE_inv henv hΓ
  exact (hA.uniqU henv hΓ (hA'.defeqU_l henv hΓ HA.toU.symm)).sort_inv henv hΓ

/-- A join of the two selected domains is the only premise needed to join
two eta expansions of a common typed source. Bodies stay literally identical
after their fresh-argument classifications are aligned by uniqueness. -/
theorem proofErase_native_eta_domain_diamond
    (hleft : ErasedScopedPrimitiveDescent Left) (hright : ErasedScopedPrimitiveDescent Right)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (RL : ScopedTypeRecovery Left (proofEraseCtx Γ) (proofErase Γ f) (.forallE X Y))
    (RR : ScopedTypeRecovery Right (proofEraseCtx Γ) (proofErase Γ f) (.forallE X' Y'))
    (SL : DomainSort (proofEraseCtx Γ) X u) (SR : DomainSort (proofEraseCtx Γ) X' v)
    (HJ : ComputeJoin Core X X') :
    ComputeJoin Core
      (.lam X (.app ((proofErase Γ f).liftN 1) (etaArgument u)))
      (.lam X' (.app ((proofErase Γ f).liftN 1) (etaArgument v))) := by
  rw [etaArgument_equiv (proofErase_native_eta_domains_equiv hleft hright hΓ hf RL RR SL SR)]
  exact HJ.lam .refl

/-- A common core reduct of the two native Pi outputs supplies their domain
join when core primitives cannot consume Pi roots. This works for arbitrary
typed short sources, including neutral variables and projections. -/
theorem proofErase_native_eta_type_diamond
    (hleft : ErasedScopedPrimitiveDescent Left) (hright : ErasedScopedPrimitiveDescent Right)
    (hpi : ∀ {A B out}, ¬ Core (.forallE A B) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (RL : ScopedTypeRecovery Left (proofEraseCtx Γ) (proofErase Γ f) (.forallE X Y))
    (RR : ScopedTypeRecovery Right (proofEraseCtx Γ) (proofErase Γ f) (.forallE X' Y'))
    (SL : DomainSort (proofEraseCtx Γ) X u) (SR : DomainSort (proofEraseCtx Γ) X' v)
    (HJ : ComputeJoin Core (.forallE X Y) (.forallE X' Y')) :
    ComputeJoin Core
      (.lam X (.app ((proofErase Γ f).liftN 1) (etaArgument u)))
      (.lam X' (.app ((proofErase Γ f).liftN 1) (etaArgument v))) := by
  obtain ⟨shared, RA, RB⟩ := HJ
  obtain ⟨A, B, rfl, HA, _⟩ := RA.pi_parts hpi
  obtain ⟨A', B', E, HB, _⟩ := RB.pi_parts hpi
  cases E
  exact proofErase_native_eta_domain_diamond hleft hright hΓ hf RL RR SL SR ⟨_, HA, HB⟩

end Lean4Lean.VEnv.Strengthening
