import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeImages

/-! # Exact recovery and checking from typed computation transport

An image bound is enough to transport all recovery constructors. Conversion
replays the selected source type, then transports its forward computation.
-/
namespace Lean4Lean.VEnv.Strengthening.NativeImageTransport
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]
variable {ImageStep Target : List ProofShape → ProofShape → ProofShape → Prop}

/-- Every native recovery constructor transports exactly once typed computation
transport is established and the target relation includes the image relation. -/
theorem recovery_of_compute
    (hrename : ∀ {Δ Δ' a b τ}, ImageStep Δ a b → ContextRenaming Δ Δ' τ →
      ImageStep Δ' (a.subst τ) (b.subst τ))
    (hstep : ErasedScopedPrimitiveDescent Source) (hinclude : ∀ {Δ a b}, ImageStep Δ a b → Target Δ a b)
    (hcompute : ∀ {Γ Δ Δ' τ e T source out}, ScopedCompute Source Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source → ImageSubstitution ImageStep Δ Δ' τ →
      ScopedCompute Target Δ' (source.subst τ) (out.subst τ))
    (R : ScopedTypeRecovery Source Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : ImageSubstitution ImageStep Δ Δ' τ) :
    ScopedTypeRecovery Target Δ' (source.subst τ) (out.subst τ) := by
  induction R generalizing Γ e T Δ' τ with
  | bvar =>
    rename_i Δ i
    obtain rfl := erase_bvar_inv Ee
    obtain ⟨A, hl⟩ := ht.bvar_inv henv hΓ
    have hn : ¬ IsProof Γ (.bvar i) := by
      intro hp; rw [proofErase_eq_proof.2 hp] at Ee; cases Ee
    obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, HI⟩ := W hΓ EΓ
    simpa only [EΓ, EΓ₀, ProofShape.subst] using
      (HI hl hn).mono (Step' := Target) hinclude
  | sort hu => exact .sort hu
  | const hc hw hn =>
    rw [proofErase_closed_subst ((henv.ordered.closedC hc).instL)]
    exact .const hc hw hn
  | lam _ ih =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    exact .lam (ih hΓA hb (by simp only [proofEraseCtx, EA, EΓ]) Eb (W.cons hrename))
  | app _ ih =>
    obtain ⟨f, a, rfl, _, Ef, _⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    rw [ProofShape.subst_inst]
    exact .app (ih hΓ hf EΓ Ef W)
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    exact .forallE (ihA hΓ hA EΓ EA W)
      (ihB hΓA hB (by simp only [proofEraseCtx, EA, EΓ]) EB (W.cons hrename))
  | proj hi HT hj hlen _ ih =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    have HR := ih hΓ hm.hasType.2 EΓ Em W
    simp only [ProofShape.subst_mkApps, ProofShape.subst] at HR
    rw [projectionType_subst HT hj (by omega)]
    exact .proj hi HT hj (by simpa only [List.length_map] using hlen) HR
  | convert R RC ih =>
    obtain ⟨A, he, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ ht
      (by simpa only [EΓ, Ee] using R)
    obtain ⟨_, hA⟩ := he.isType henv hΓ
    exact .convert (ih hΓ ht EΓ Ee W) (hcompute RC hΓ hA EΓ EA W)

/-- Full joint checking transports using exact native recovery for the selected
application domain. Computed applications and all guard constructors are included. -/
theorem check_of_compute
    (hrename : ∀ {Δ Δ' a b τ}, ImageStep Δ a b → ContextRenaming Δ Δ' τ →
      ImageStep Δ' (a.subst τ) (b.subst τ))
    (hstep : ErasedScopedPrimitiveDescent Source) (hinclude : ∀ {Δ a b}, ImageStep Δ a b → Target Δ a b)
    (hcompute : ∀ {Γ Δ Δ' τ e T source out}, ScopedCompute Source Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source → ImageSubstitution ImageStep Δ Δ' τ →
      ScopedCompute Target Δ' (source.subst τ) (out.subst τ))
    (H : ComputedJointCheck Source Δ kind a b) :
    ComputedJointTransportResult (ImageSubstitution ImageStep)
      Target Δ kind a b := by
  apply H.transport_application (ImageSubstitution ImageStep) hstep
    (fun W => W.cons hrename) (fun W S => ContextSubstitution.sort W.interpretation S) hcompute
  intro Γ Δ' τ f x y C E A B g mode hΓ hf hx hy hn R W HF HX
  exact .appCarrier (recovery_of_compute hrename hstep hinclude hcompute R hΓ hf rfl rfl W) HF HX

end Lean4Lean.VEnv.Strengthening.NativeImageTransport
