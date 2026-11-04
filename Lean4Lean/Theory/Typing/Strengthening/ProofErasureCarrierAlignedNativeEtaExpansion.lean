import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeIdentityExpansion

/-! # Eta expansion using a natively recovered function type

The short source already has a typed representative. Recovery reconstructs the
binder annotation below insertion; its sort witness determines whether the
fresh argument is retained or erased. No eta contractum is reconstructed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Native Pi recovery and an ambient domain-sort witness license eta expansion
with the exact recovered annotation and the correctly erased fresh argument. -/
inductive ProofShape.NativeEtaExpansion
    (Step : List ProofShape → ProofShape → ProofShape → Prop) (Δ : List ProofShape) :
    ProofShape → ProofShape → Prop where
  | intro : ScopedTypeRecovery Step Δ f (.forallE A B) → DomainSort Δ A u →
      NativeEtaExpansion Step Δ f (.lam A (.app (f.liftN 1) (etaArgument u)))

/-- Eta expansion is monotone in its native recovery relation. -/
theorem ProofShape.NativeEtaExpansion.mono
    (hstep : ∀ {Δ a b}, Step Δ a b → Step' Δ a b)
    (H : NativeEtaExpansion Step Δ a b) : NativeEtaExpansion Step' Δ a b := by
  cases H with
  | intro R S => exact .intro (R.mono hstep) S

/-- A non-proof function retains its whole eta expansion under erasure. -/
theorem proofErase_nativeEtaExpansion (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f) :
    proofErase Γ (.lam A (.app f.lift (.bvar 0))) =
      .lam (proofErase Γ A) (.app ((proofErase Γ f).liftN 1) (etaArgument u)) := by
  have hn' := mt (isProof_congr hΓ (IsDefEq.eta hf)).1 hn
  rw [show proofErase Γ (.lam A (.app f.lift (.bvar 0))) = .lam _ _ from if_neg hn']
  rw [proofErase_eta_body hΓ hA hf hn]

/-- Recovered eta expansion descends through any inserted binder block at the
original source type. The native guard supplies a lower Pi annotation, and
DomainSort.descend fixes the fresh argument's erasure without strengthening. -/
theorem erased_nativeEtaExpansion_descent (hstep : ErasedScopedPrimitiveDescent Step) :
    ErasedScopedPrimitiveDescent (NativeEtaExpansion Step) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  cases H with
  | intro R S =>
    obtain ⟨A, B, he, EA, _⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ hΓ' W ht R
    obtain ⟨_, hPi⟩ := he.isType henv hΓ
    obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
    have hA := (EA ▸ S).descend hΓ hΓ' W hA
    have hn : ¬ IsProof Γ e := by
      intro hp
      exact R.ne_proof (by rw [proofErase_eq_proof.2 hp]; rfl)
    refine ⟨_, (IsDefEq.eta he).symm.toU.of_l henv hΓ ht, ?_⟩
    rw [proofErase_nativeEtaExpansion hΓ hA he hn]
    simp only [ProofShape.liftN, etaArgument_liftN, EA]
    rw [ProofShape.liftN_comm _ n 1 k 0 (Nat.zero_le _)]

/-- Exact interpreted renaming transports both recovery and the sort witness. -/
theorem ProofShape.NativeEtaExpansion.rename
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step' Δ' (a.subst τ) (b.subst τ))
    (H : NativeEtaExpansion Step Δ a b) (W : ContextRenaming Δ Δ' τ) :
    NativeEtaExpansion Step' Δ' (a.subst τ) (b.subst τ) := by
  cases H with
  | intro R S =>
    simpa only [ProofShape.subst, lift_subst_lift, etaArgument_subst] using
      NativeEtaExpansion.intro (R.rename hrename W) (ContextSubstitution.sort W.interpretation S)

/-- Exact native-image substitution preserves the eta expansion recipe. The
sort witness uses the underlying typed substitution, with no new coverage premise. -/
theorem ProofShape.NativeEtaExpansion.subst_typed
    (hrename : ∀ {Δ Δ' a b τ}, ImageStep Δ a b → ContextRenaming Δ Δ' τ →
      ImageStep Δ' (a.subst τ) (b.subst τ))
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hinclude : ∀ {Δ a b}, ImageStep Δ a b → Target Δ a b)
    (hcompute : ∀ {Γ Δ Δ' τ e T source out}, ScopedCompute Source Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source →
      NativeImageTransport.ImageSubstitution ImageStep Δ Δ' τ →
      ScopedCompute Target Δ' (source.subst τ) (out.subst τ))
    (H : NativeEtaExpansion Source Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : NativeImageTransport.ImageSubstitution ImageStep Δ Δ' τ) :
    NativeEtaExpansion Target Δ' (source.subst τ) (out.subst τ) := by
  cases H with
  | intro R S =>
    simpa only [ProofShape.subst, lift_subst_lift, etaArgument_subst] using
      NativeEtaExpansion.intro
        (NativeImageTransport.recovery_of_compute hrename hstep hinclude hcompute R hΓ ht EΓ Ee W)
        (ContextSubstitution.sort W.interpretation S)

end Lean4Lean.VEnv.Strengthening
