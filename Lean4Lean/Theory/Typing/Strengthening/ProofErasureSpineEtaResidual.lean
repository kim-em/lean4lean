import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSpineRecoveryTransport

/-! # Reconstructing native eta after spine arguments change

The computed short branch obtains its native Pi from the original certificate.
Its selected domain is a core reduct of the original domain, so its sort witness
survives. The two long forms then join by core computation alone.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- Any descending context-independent core transports a realized domain sort
along its computation. This uses source replay, not native type completeness. -/
theorem ProofShape.DomainSort.compute_descent
    (hc : ErasedScopedPrimitiveDescent (fun _ => Core))
    (S : DomainSort Δ A u) (R : Compute Core A B) : DomainSort Δ B u := by
  obtain ⟨Γ, a, hΓ, EΓ, ha, Ea⟩ := S
  obtain ⟨b, hb, Eb⟩ := proofErase_scoped_compute_realize hc hΓ ha EΓ Ea
    (R.scoped (fun H => .base H))
  exact ⟨Γ, b, hΓ, EΓ, hb.hasType.2, Eb⟩

/-- Changing a neutral spine's arguments reconstructs native eta at the new
short source. Its long form core-joins the original expansion. The original
native guard may have arbitrary descending, typed-core-joinable conversions;
neither the changed source nor any argument needs supplied native evidence. -/
theorem proofErase_spine_native_eta_residual
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hcore : ErasedScopedPrimitiveDescent (fun _ => Core)) (hc : TypedCoreConfluence Core)
    (hpi : ∀ {A B out}, ¬ Core (.forallE A B) out)
    (hsubst : ∀ {a b τ}, Core a b → Core (a.subst τ) (b.subst τ))
    (hjoin : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ e) out → ComputeJoin Core (proofErase Γ e) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (H : NativeSpineJoin Core (proofErase Γ e) target)
    (R : NativeEtaExpansion Source (proofEraseCtx Γ) (proofErase Γ e) expanded) :
    ∃ expanded', NativeEtaExpansion (fun _ => Core) (proofEraseCtx Γ) target expanded' ∧
      ComputeJoin Core expanded expanded' := by
  cases R with
  | intro RN SD =>
    obtain ⟨out', RN', RT⟩ := proofErase_spine_native_transport hstep hc hpi hsubst hjoin
      RN hΓ he rfl rfl H
    obtain ⟨X, Y, rfl, RX, _⟩ := RT.pi_parts hpi
    have SD' := SD.compute_descent hcore RX
    refine ⟨_, .intro RN' SD', (ComputeJoin.of_compute RX).lam ?_⟩
    have HF := H.join.subst hsubst (σ := fun i => .bvar (liftVar 1 i 0))
    simp only [subst_bvar_liftN] at HF
    exact HF.app .refl

end Lean4Lean.VEnv.Strengthening
