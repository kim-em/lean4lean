import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCountedNativeTransport

/-! # Count-preserving substitution for Pi-inert body tails

At stage zero, ordinary interpreted substitution suffices even for positive
primitive counts. At arbitrary stages, exact recovery of the consumed argument
supplies the native image condition. Neither statement assumes normalization.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Stage-zero paths retain their exact primitive count under any interpreted
substitution. Each core or constant-expansion root substitutes to one root;
compatible bodies extend only the ordinary context interpretation. -/
theorem pi_inert_zero_compute_count_substitution
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ScopedComputeCount (PiInertStage D 0) cost Δ source out)
    (HT : TypedSource Δ source) (W : ContextSubstitution Δ Θ τ) :
    ScopedComputeCount (PiInertStage D 0) cost Θ (source.subst τ) (out.subst τ) := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  apply R.transport_typed
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0))
    ContextSubstitution (fun W => W.cons) _ hΓ ht EΓ Ee W
  intro Γ Δ Θ τ e T source out H hΓ ht EΓ Ee W
  refine ⟨?_, ?_⟩
  · rcases H.1 with H | H
    · exact .inl (erased_level_core_subst H)
    · exact .inr (H.subst_typed hΓ ht EΓ Ee W)
  · rcases H.2 with H | ⟨u, rfl⟩
    · exact .inl H.subst
    · exact .inr ⟨u, rfl⟩

/-- An interpreted one-binder consumption with exact native recovery of its
actual raw argument has the image condition required by all-stage transport.
The remaining variable images are identities. No recovery is inferred from
ordinary assigned typing alone. -/
theorem pi_inert_native_inst_image_substitution
    (W : ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D k) Δ x A) :
    StaticStructureEtaNativeSubstitution.ImageSubstitution D k (A :: Δ) Δ (ProofShape.Subst.one x) := by
  intro Γ hΓ EΓ
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ EΓ
  refine ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, ?_⟩
  intro i T hl hn
  cases Γ with
  | nil => cases EΓ
  | cons B Γ =>
    obtain ⟨EB, EG⟩ := List.cons.inj EΓ
    cases hl with
    | zero =>
      simpa only [proofEraseCtx, EB, EG, EΓ₀, contextOracle, TypeOracle.cons,
        ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id,
        ProofShape.Subst.cons] using RN
    | succ hl =>
      simp only [proofEraseCtx, EB, EG, contextOracle, TypeOracle.cons,
        ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id]
      rw [← EΓ₀]
      exact .bvar

/-- Exact native recovery of the consumed argument transports an arbitrary
finite-stage body tail with the same primitive count. The guard stage may
increase, which is harmless for minima quantified over all finite stages. -/
theorem pi_inert_compute_count_native_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ScopedComputeCount (PiInertStage D n) cost (A :: Δ) source out)
    (HT : TypedSource (A :: Δ) source)
    (W : ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D k) Δ x A) :
    ScopedComputeCount (PiInertStage D (n+k)) cost Δ (source.inst x) (out.inst x) := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  have RR := pi_inert_compute_count_native_transport heq hs R hΓ ht EΓ Ee
    (pi_inert_native_inst_image_substitution W RN)
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RR

end Lean4Lean.VEnv.Strengthening
