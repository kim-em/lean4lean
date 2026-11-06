import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationCount
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCountedWrappers
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureBackwardContext

/-! # Exact primitive counts through native image transport

A primitive-to-primitive transport preserves the entire outer count. Native
identity images supplied by a computed annotation therefore move body paths
back to the preceding binder without changing their cost or their raw endpoints.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- One target primitive per source primitive preserves the exact count.
Transitive intermediates are realized by source descent, and bodies use their
actual source annotation with the extended transport. -/
theorem ProofShape.ScopedComputeCount.transport_typed
    (hstep : ErasedScopedPrimitiveDescent Step)
    (Transport : List ProofShape → List ProofShape → ProofShape.Subst → Prop)
    (hcons : ∀ {Δ Δ' τ A}, Transport Δ Δ' τ →
      Transport (A :: Δ) (A.subst τ :: Δ') τ.lift)
    (hprimitive : ∀ {Γ Δ Δ' τ e T source out}, Step Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source → Transport Δ Δ' τ →
      Target Δ' (source.subst τ) (out.subst τ))
    (R : ProofShape.ScopedComputeCount Step cost Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : Transport Δ Δ' τ) :
    ProofShape.ScopedComputeCount Target cost Δ' (source.subst τ) (out.subst τ) := by
  induction R generalizing Γ e T Δ' τ with
  | base H => exact .base (hprimitive H hΓ ht EΓ Ee W)
  | beta H => exact .beta H.subst
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize hstep hΓ ht EΓ Ee R₁.forget
    exact .trans (ih₁ hΓ ht EΓ Ee W) (ih₂ hΓ HE.hasType.2 EΓ EE W)
  | app _ _ ihf iha =>
    obtain ⟨f, a, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact .app (ihf hΓ hf EΓ Ef W) (iha hΓ ha EΓ Ea W)
  | proj _ ihm =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj (ihm hΓ hm.hasType.2 EΓ Em W)
  | lam _ _ ihA ihb =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    exact .lam (ihA hΓ hA EΓ EA W)
      (ihb hΓA hb (by simp only [proofEraseCtx, EA, EΓ]) Eb (hcons W))
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    exact .forallE (ihA hΓ hA EΓ EA W)
      (ihB hΓA hB (by simp only [proofEraseCtx, EA, EΓ]) EB (hcons W))

open ProofShape PureObservation

/-- Exact native images preserve the Pi-inert head restriction and the
outer primitive count. Only the finite guard stage increases. -/
theorem pi_inert_compute_count_native_transport
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ScopedComputeCount (PiInertStage D n) cost Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : StaticStructureEtaNativeSubstitution.ImageSubstitution D k Δ Δ' τ) :
    ScopedComputeCount (PiInertStage D (n+k)) cost Δ' (source.subst τ) (out.subst τ) := by
  apply R.transport_typed
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
    (StaticStructureEtaNativeSubstitution.ImageSubstitution D k)
    (fun W => NativeImageTransport.ImageSubstitution.cons
      (erased_static_structure_eta_expansion_stage_rename heq hs k) W) _ hΓ ht EΓ Ee W
  intro Γ Δ Δ' τ e T source out H hΓ ht EΓ Ee W
  refine ⟨StaticStructureEtaNativeSubstitution.primitive_subst heq hs n H.1 hΓ ht EΓ Ee W, ?_⟩
  rcases H.2 with H | ⟨u, rfl⟩
  · exact .inl H.subst
  · exact .inr ⟨u, rfl⟩

/-- Pull a counted body computation back across a computed annotation.
Its exact endpoints and primitive count survive; the annotation stage is
added to the body's guard stage rather than to its primitive count. -/
theorem pi_inert_compute_count_backward_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (RA : ScopedCompute (PiInertStage D k) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ B))
    (ht : env.HasType univs (B :: Γ) e T)
    (R : ScopedComputeCount (PiInertStage D n) cost (proofEraseCtx (B :: Γ))
      (proofErase (B :: Γ) e) out) :
    ScopedComputeCount (PiInertStage D (n+k)) cost (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out := by
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.2⟩
  have HR := pi_inert_compute_count_native_transport heq hs R hΓB ht rfl rfl
    (static_structure_native_backward_context heq hs hΓ HAB (RA.mono pi_inert_stage_embed))
  simp only [ProofShape.subst_id] at HR
  have EE := proofErase_defeqCtx hΓB (IsDefEqCtx.succ .zero HAB.symm) ht
  simpa only [EE] using HR

end Lean4Lean.VEnv.Strengthening
