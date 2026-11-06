import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextEmbedding

/-! # Reverse completion retaining the actual context embedding

The embedding construction supports annotation replay. Consequently a further
proof endpoint beneath changed retained annotations preserves the same kind
of witness, allowing repeated proof-valued scope moves at arbitrary depth.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- A proof endpoint admits a reverse variable renaming after replaying its
recorded annotation changes. The round trip fixes every retained variable
of the actual source context, and the construction retains binder insertions
and extensions so later annotation histories can be transported. -/
theorem ProofEndpointContext.embedding_retraction
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ProofEndpointContext D Ξ Ξ' τ)
    (hΓ : OnCtx Γ (env.IsType univs)) (EΓ : proofEraseCtx Γ = Ξ) :
    ∃ Θ κ, PiInertContextHistory D Ξ Θ ∧ ContextEmbedding Ξ' Θ κ ∧
      (∀ {i B}, Lookup Γ i B → ¬ IsProof Γ (.bvar i) → (τ i).subst κ = .bvar i) := by
  induction H generalizing Γ with
  | identity =>
    exact ⟨_, ProofShape.Subst.id, .refl, ContextEmbedding.identity,
      (fun _ _ => rfl)⟩
  | @inst Ξ rawA rawX SD _ =>
    cases Γ with
    | nil => cases EΓ
    | cons A Γ =>
      obtain ⟨hΓ, u, hA⟩ := hΓ
      obtain ⟨EA, EΓ⟩ := List.cons.inj EΓ
      have SD' : DomainSort (proofEraseCtx Γ) rawA .zero := EΓ.symm ▸ SD
      obtain ⟨P, hP, EP⟩ := SD'.realize hΓ
      obtain ⟨_, HPA⟩ := (proofErase_reflect hΓ hP hA (EP.trans EA.symm)).2
        (not_isProof_of_sort hΓ hP)
      have hA₀ := ((HPA.defeq hΓ).of_l henv hΓ hP).hasType.2
      refine ⟨rawA :: Ξ, (fun i => .bvar (liftVar 1 i 0)), .refl,
        ContextEmbedding.insert .identity SD, ?_⟩
      intro i B hl hn
      cases i with
      | zero => exact (hn ⟨A.lift, .bvar .zero, hA₀.weak henv.ordered⟩).elim
      | succ i => simp [ProofShape.Subst.one, ProofShape.Subst.cons,
          ProofShape.Subst.id, ProofShape.subst, liftVar, Nat.add_comm]
  | @binder n Ξ rawA rawA' Ξ' τ RD H ih =>
    cases Γ with
    | nil => cases EΓ
    | cons A Γ =>
      obtain ⟨hΓ, u, hA⟩ := hΓ
      obtain ⟨EA, EΓ⟩ := List.cons.inj EΓ
      obtain ⟨Θ, κ, HH, WK, HK⟩ := ih hΓ EΓ
      obtain ⟨A', HA, EA'⟩ := proofErase_scoped_compute_realize
        (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)) hΓ hA EΓ EA RD
      have ER : (rawA'.subst τ).subst κ = rawA' := by
        rw [← EA', ProofShape.subst_subst]
        exact proofErase_subst_retained hΓ HA.hasType.2 HK
      have WK' := WK.binder (A := rawA'.subst τ)
      rw [ER] at WK'
      refine ⟨rawA' :: Θ, κ.lift, .step (.head RD) HH.tail, WK', ?_⟩
      intro i B hl hn
      cases hl with
      | zero => rfl
      | succ hl =>
        have hn' : ¬ IsProof Γ (.bvar _) := fun hp => hn (IsProof.lift' (Ctx.Lift'.skip .refl) hp)
        simp only [ProofShape.Subst.lift, ProofShape.lift_subst_lift, HK hl hn']
        simp [ProofShape.liftN, liftVar, Nat.add_comm]

/-- Bounded target completion after a constructed context embedding. Retaining
the insertion structure permits later annotation transport; forgetting it
recovers the general reverse-renaming readout witness. -/
def EqTargetPrefixEmbedding (Δ : List VExpr) (v w : VLevel) (original : List VExpr)
    (Ξ : List ProofShape) (source : ProofShape) : Prop :=
  ∃ Θ κ, ContextEmbedding Ξ Θ κ ∧ EqTargetPrefixCompletion Δ v w original Θ (source.subst κ)

/-- The constructed witness has every existing reverse-renaming readout. -/
theorem EqTargetPrefixEmbedding.forget
    (H : EqTargetPrefixEmbedding Δ v w original Ξ source) :
    EqTargetPrefixRetraction Δ v w original Ξ source := by
  obtain ⟨Θ, κ, W, HP⟩ := H
  exact ⟨Θ, κ, W.renaming, HP⟩

/-- Ordinary completion starts the embedding invariant with identity. -/
theorem EqTargetPrefixCompletion.embedding
    (H : EqTargetPrefixCompletion Δ v w original Ξ source) :
    EqTargetPrefixEmbedding Δ v w original Ξ source :=
  ⟨Ξ, ProofShape.Subst.id, .identity, by simpa only [ProofShape.subst_id] using H⟩

/-- Reverse pullback composes constructed embeddings and retains their full
insertion structure for subsequent annotation changes. -/
theorem EqTargetPrefixEmbedding.pullback
    (H : EqTargetPrefixEmbedding Δ v w original Ξ' (source.subst τ))
    (W : ContextEmbedding Ξ Ξ' τ) : EqTargetPrefixEmbedding Δ v w original Ξ source := by
  obtain ⟨Θ, κ, WK, HP⟩ := H
  exact ⟨Θ, τ.comp κ, W.compose WK, by simpa only [ProofShape.subst_subst] using HP⟩

/-- Replay all retained annotation computations through the existing reverse
embedding, preserving completion in the rebuilt target context. -/
theorem EqTargetPrefixEmbedding.context_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqTargetPrefixEmbedding Δ v w original Ξ source)
    (R : PiInertContextHistory D Ξ Ξ') :
    EqTargetPrefixEmbedding Δ v w original Ξ' source := by
  obtain ⟨Θ, κ, WK, HP⟩ := H
  obtain ⟨Θ', WK', R'⟩ := WK.context_history heq hs R
  exact ⟨Θ', κ, WK', HP.context_history heq hs hΔ R'⟩

/-- A further proof endpoint, including every recorded changed retained
annotation above it, preserves the constructed embedding invariant. First
transport its annotation history through the old embedding, then compose
the endpoint's reverse embedding. Typed erasure makes the round trip exact. -/
theorem EqTargetPrefixEmbedding.proof_endpoint
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqTargetPrefixEmbedding Δ v w original Ξ source)
    (HT : TypedSource Ξ source) (HC : ProofEndpointContext D Ξ Ξ' τ) :
    EqTargetPrefixEmbedding Δ v w original Ξ' (source.subst τ) := by
  obtain ⟨Γ, f, F, hΓ, EΓ, hf, Ef⟩ := HT
  obtain ⟨Θ, κ, HH, WK, HK⟩ := HC.embedding_retraction heq hs hΓ EΓ
  have ES : (source.subst τ).subst κ = source := by
    rw [← Ef, ProofShape.subst_subst]
    exact proofErase_subst_retained hΓ hf HK
  have HP := H.context_history heq hs hΔ HH
  exact (ES.symm ▸ HP).pullback WK

/-- An actual endpoint context now preserves the embedding invariant or
identifies its consumed base binder without a Prop-domain witness. Arbitrary
retained depth, annotation histories and earlier embeddings are covered. -/
theorem EqTargetPrefixEmbedding.endpoint_or_unwitnessed_domain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqTargetPrefixEmbedding Δ v w original Ξ source)
    (HT : TypedSource Ξ source) (HC : PiInertEndpointContext D Ξ Ξ' τ) :
    EqTargetPrefixEmbedding Δ v w original Ξ' (source.subst τ) ∨
      ∃ Θ A x depth, ContextSubstitution (A :: Θ) Θ (ProofShape.Subst.one x) ∧
        ¬ DomainSort Θ A .zero ∧ τ = (ProofShape.Subst.one x).liftN depth := by
  rcases HC.proof_or_unwitnessed_domain with HC | HN
  · exact .inl (H.proof_endpoint heq hs hΔ HT HC)
  · exact .inr HN

end Lean4Lean.VEnv.Strengthening
