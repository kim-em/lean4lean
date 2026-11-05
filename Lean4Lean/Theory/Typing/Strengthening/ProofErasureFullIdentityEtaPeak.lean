import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIdentityEtaCriticalPeak
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaDomainReadout

/-! # Full residual joining of the first identity-beta/eta peak

The earlier core obstruction does not settle what happens when all enriched
rules are permitted in the residuals. Lambda-domain readout now shows an exact
pointwise equivalence: joining this full residual peak is joining its original
ordinary type conversion. No confluence or coverage premise proves the readout.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : Definitions}

/-- A common full-union reduct of two typed raw lambdas joins their raw domains.
The actual ordinary representatives may have different written annotations with
those same erasures. No computation transport across type conversion is assumed. -/
theorem typed_raw_lambda_domain_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f T) (hg : env.HasType univs Γ g U)
    (Ef : proofErase Γ f = .lam A b) (Eg : proofErase Γ g = .lam B c)
    (RF : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.lam A b) out)
    (RG : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.lam B c) out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) A shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) B shared := by
  obtain ⟨A₀, b₀, rfl, hn, EA, _⟩ := erase_lam_inv Ef
  obtain ⟨B₀, c₀, rfl, hm, EB, _⟩ := erase_lam_inv Eg
  obtain ⟨⟨u, hA⟩, C, hb⟩ := hf.lam_inv henv hΓ
  obtain ⟨⟨v, hB⟩, E, hc⟩ := hg.lam_inv henv hΓ
  obtain ⟨shared, RA, RB⟩ := proofErase_static_structure_lambda_domain_join heq hs hΓ
    hA hb hB hc hn hm (Ef ▸ RF) (Eg ▸ RG)
  exact ⟨shared, EA ▸ RA, EB ▸ RB⟩

omit [Params] in
/-- The identity wrapper stores the assigned domain B around a lambda written
with A. The constant body is Prop; neither domain needs an inhabitant. -/
def identityEtaSource (A B : VExpr) : VExpr :=
  .app (.lam (.forallE B (.sort (.succ .zero))) (.bvar 0)) (.lam A (.sort .zero))

/-- The native eta endpoint selected using the assigned domain's universe.
Its guard is supplied at stage zero in the following construction. -/
noncomputable def identityEtaTarget (Γ : List VExpr) (A B : VExpr) (u : VLevel) : ProofShape :=
  .lam (proofErase Γ B) (.app ((proofErase Γ (identityEtaSource A B)).liftN 1) (etaArgument u))

/-- One beta branch and one native eta branch with a stage-zero guard encode
any ordinary type conversion. Even with all enriched rules allowed afterwards,
the two residuals join exactly when the original domains join. -/
theorem identity_eta_full_conversion_peak
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u)) :
    env.HasType univs Γ (identityEtaSource A B) (.forallE B (.sort (.succ .zero))) ∧
      BetaRed (proofErase Γ (identityEtaSource A B)) (.lam (proofErase Γ A) (.sort .zero)) ∧
      NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ (identityEtaSource A B)) (identityEtaTarget Γ A B u) ∧
      BetaRed (identityEtaTarget Γ A B u) (.lam (proofErase Γ B) (.sort .zero)) ∧
      ((∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (.lam (proofErase Γ A) (.sort .zero)) shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (identityEtaTarget Γ A B u) shared) ↔
       ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ A) shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ B) shared) := by
  let Q : VExpr := .forallE B (.sort (.succ .zero))
  let f : VExpr := .lam A (.sort .zero)
  let source : VExpr := .app (.lam Q (.bvar 0)) f
  have hA := HAB.hasType.1
  have hB := HAB.hasType.2
  have hb : env.HasType univs (A :: Γ) (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hf : env.HasType univs Γ f Q :=
    (IsDefEq.forallEDF HAB (HasType.sort (l := .succ .zero) (by trivial))).defeq (HasType.lam hA hb)
  have hn : ¬ IsProof Γ f := not_isProof_function_to_sort hΓ hf
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, hB⟩
  have Ef : proofErase Γ f = .lam (proofErase Γ A) (.sort .zero) := by
    rw [show proofErase Γ f = .lam (proofErase Γ A) (proofErase (A :: Γ) (.sort .zero)) from if_neg hn]
    exact congrArg (ProofShape.lam (proofErase Γ A)) (if_neg (not_isProof_of_sort hΓA hb))
  have hQ : env.HasType univs Γ Q (.sort (.imax u (.succ (.succ .zero)))) :=
    .forallE hB (.sort (by trivial))
  have EQ : proofErase Γ Q = .forallE (proofErase Γ B) (.sort (.succ .zero)) := by
    rw [show proofErase Γ Q = .forallE (proofErase Γ B) (proofErase (B :: Γ) (.sort (.succ .zero))) from
      if_neg (not_isProof_of_sort hΓ hQ)]
    exact congrArg (ProofShape.forallE (proofErase Γ B))
      (if_neg (not_isProof_of_sort hΓB (HasType.sort (by trivial))))
  have RB : BetaRed (proofErase Γ source) (.lam (proofErase Γ A) (.sort .zero)) := by
    simpa only [Ef] using proofErase_identity_wrapper_beta hΓ hf hn
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (proofErase Γ source) (.forallE (proofErase Γ B) (.sort (.succ .zero))) := by
    simpa only [EQ] using proofErase_identity_wrapper_native (Step := ErasedStaticStructureEtaExpansionStage D 0) hΓ hf hn
  let etaOut := ProofShape.lam (proofErase Γ B)
    (.app ((proofErase Γ source).liftN 1) (etaArgument u))
  have RE : NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (proofErase Γ source) etaOut := .intro RN (.of_typed hΓ hB)
  have Rbeta : BetaRed etaOut (.lam (proofErase Γ B) (.sort .zero)) := by
    apply (BetaRed.lam .refl (.app RB.liftN .refl)).trans
    have R := proofErase_eta_lambda_beta hΓ hA hb (proofErase Γ B)
    simpa only [show proofErase (A :: Γ) (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hΓA hb)] using R
  have hsrc := (nativeIdentityExpansion_equal hf).hasType.1
  refine ⟨hsrc, RB, RE, Rbeta, ?_⟩
  constructor
  · rintro ⟨shared, RL, RR⟩
    have Rfull : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ source) etaOut :=
      .base ⟨1, .inr (.inr (.inr (.inr (.inl RE))))⟩
    obtain ⟨right, HR, ER⟩ := proofErase_scoped_compute_realize
      (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hsrc rfl rfl Rfull
    exact typed_raw_lambda_domain_join heq hs hΓ (HasType.lam hA hb) HR.hasType.2 Ef ER RL RR
  · rintro ⟨shared, RA, RB⟩
    exact ⟨.lam shared (.sort .zero), .lam RA .refl, (ScopedCompute.beta Rbeta).trans (.lam RB .refl)⟩

/-- Supplying the source conversion's domain join repairs this peak in that
same target relation. No extra guard depth is required in the residuals; only
compatible lambdas and beta cleanup are used. This isolates the exact input a
source-typing induction would have to supply for this critical pair. -/
theorem identity_eta_residual_repair
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (RA : ScopedCompute Target (proofEraseCtx Γ) (proofErase Γ A) domain)
    (RB : ScopedCompute Target (proofEraseCtx Γ) (proofErase Γ B) domain) :
    ScopedCompute Target (proofEraseCtx Γ) (.lam (proofErase Γ A) (.sort .zero)) (.lam domain (.sort .zero)) ∧
      ScopedCompute Target (proofEraseCtx Γ) (identityEtaTarget Γ A B u) (.lam domain (.sort .zero)) := by
  have Rβ := (identity_eta_full_conversion_peak heq hs hΓ HAB).2.2.2.1
  exact ⟨.lam RA .refl, (ScopedCompute.beta Rβ).trans (.lam RB .refl)⟩

end Lean4Lean.VEnv.Strengthening
