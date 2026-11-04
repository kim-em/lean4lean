import Lean4Lean.Theory.Typing.Strengthening.ProofErasureUnitEtaNativeTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaUnitBetaBoundary

/-! # Unit eta repairs the unit-indexed native obstruction

The same four-variable context has no common native type in the full function
eta union, but has one at unit-eta stage one. No native completeness premise is
used: context lookup supplies both unit guards and the source's declared type.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- Two natively recovered inhabitants of the same empty structure compute to
its constructor, including its entire parameter spine, one guard stage later. -/
theorem unit_eta_native_join
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hz : info.numFields = 0) (hp : ps.length = info.nparams)
    (RA : ScopedTypeRecovery (ErasedUnitEtaExpansionStage D n) Δ a
      (ProofShape.mkApps (.const family ls) ps))
    (RB : ScopedTypeRecovery (ErasedUnitEtaExpansionStage D n) Δ b
      (ProofShape.mkApps (.const family ls) ps)) :
    ScopedCompute (ErasedUnitEtaExpansionStage D (n+1)) Δ a
        (ProofShape.mkApps (.const info.ctorName ls) ps) ∧
      ScopedCompute (ErasedUnitEtaExpansionStage D (n+1)) Δ b
        (ProofShape.mkApps (.const info.ctorName ls) ps) := by
  exact ⟨.base (.inr (.inr (.inr (.inr (.inr (.intro hi hx hz hp RA)))))),
    .base (.inr (.inr (.inr (.inr (.inr (.intro hi hx hz hp RB))))))⟩

/-- Lookup guards suffice to repair the family-indexed mismatch. The common
native type is F applied to the registered empty constructor. -/
theorem unit_eta_family_native_repair
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.bvar f) (.forallE (.const family []) (.sort (.succ .zero))))
    (hli : Lookup Γ i (.const family [])) (hlj : Lookup Γ j (.const family []))
    (hlp : Lookup Γ p (.app (.bvar f) (.bvar i))) :
    ScopedTypeRecovery (ErasedUnitEtaExpansionStage D 1) (proofEraseCtx Γ)
        (proofErase Γ (.bvar p)) (.app (proofErase Γ (.bvar f)) (.const info.ctorName [])) ∧
      ScopedCompute (ErasedUnitEtaExpansionStage D 1) (proofEraseCtx Γ)
        (proofErase Γ (.app (.bvar f) (.bvar j)))
        (.app (proofErase Γ (.bvar f)) (.const info.ctorName [])) := by
  have hSΓ : env.HasType univs Γ (.const family []) (.sort (.succ u)) := hS.weak0 henv.ordered
  have hiT : env.HasType univs Γ (.bvar i) (.const family []) := .bvar hli
  have hjT : env.HasType univs Γ (.bvar j) (.const family []) := .bvar hlj
  have ES : proofErase Γ (.const family []) = .const family [] := if_neg (not_isProof_of_sort hΓ hSΓ)
  have Ri := proofErase_scoped_lookup_recovery (Step := ErasedUnitEtaExpansionStage D 0)
    hΓ hli (not_proof_at_positive_type hΓ hSΓ hiT) .refl
  have Rj := proofErase_scoped_lookup_recovery (Step := ErasedUnitEtaExpansionStage D 0)
    hΓ hlj (not_proof_at_positive_type hΓ hSΓ hjT) .refl
  rw [ES] at Ri Rj
  obtain ⟨CI, CJ⟩ := unit_eta_native_join hi hx hz (ps := []) hp.symm Ri Rj
  have hFi : env.HasType univs Γ (.app (.bvar f) (.bvar i)) (.sort (.succ .zero)) := .app hF hiT
  have hFj : env.HasType univs Γ (.app (.bvar f) (.bvar j)) (.sort (.succ .zero)) := .app hF hjT
  have CI' : ScopedCompute (ErasedUnitEtaExpansionStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (.app (.bvar f) (.bvar i)))
      (.app (proofErase Γ (.bvar f)) (.const info.ctorName [])) := by
    rw [show proofErase Γ (.app (.bvar f) (.bvar i)) = .app _ _ from if_neg (not_isProof_of_sort hΓ hFi)]
    exact .app .refl CI
  refine ⟨proofErase_scoped_lookup_recovery hΓ hlp
    (not_proof_at_positive_type hΓ hFi (.bvar hlp)) CI', ?_⟩
  rw [show proofErase Γ (.app (.bvar f) (.bvar j)) = .app _ _ from if_neg (not_isProof_of_sort hΓ hFj)]
  exact .app .refl CJ

/-- A single context simultaneously witnesses failure of common native
coverage at every old function-eta depth and its repair at unit-eta depth one.
The identity-wrapper beta step from the previous obstruction is retained. -/
theorem unit_eta_strict_native_repair_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ p A shared, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ p A ∧ ¬ IsProof Γ p ∧
      env.IsDefEq univs Γ (.app (.lam A (.bvar 0)) p) p A ∧
      ProofShape.BetaRed (proofErase Γ (.app (.lam A (.bvar 0)) p)) (proofErase Γ p) ∧
      ScopedTypeRecovery (ErasedUnitEtaExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam A (.bvar 0)) p)) (proofErase Γ A) ∧
      ScopedTypeRecovery (ErasedUnitEtaExpansionStage D 1) (proofEraseCtx Γ) (proofErase Γ p) shared ∧
      ScopedCompute (ErasedUnitEtaExpansionStage D 1) (proofEraseCtx Γ) (proofErase Γ A) shared ∧
      (∀ native out, ScopedTypeRecovery (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ p) native →
        ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ A) out →
        ¬ ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ) native out) := by
  let S := VExpr.const family []
  let FT := VExpr.forallE S (.sort (.succ .zero))
  let Γ₀ := [FT, S, S]
  have hFT : env.HasType univs [] FT (.sort (.imax (.succ u) (.succ (.succ .zero)))) :=
    .forallE hS (.sort (by trivial))
  have hΓ₀ : OnCtx Γ₀ (env.IsType univs) :=
    ⟨⟨⟨trivial, _, hS⟩, _, hS.weak0 henv.ordered⟩, _, hFT.weak0 henv.ordered⟩
  have hF₀ : env.HasType univs Γ₀ (.bvar 0) FT := .bvar .zero
  have hI₀ : env.HasType univs Γ₀ (.bvar 1) S := .bvar (.succ .zero)
  have hA : env.HasType univs Γ₀ (.app (.bvar 0) (.bvar 1)) (.sort (.succ .zero)) := .app hF₀ hI₀
  let Γ := .app (.bvar 0) (.bvar 1) :: Γ₀
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨hΓ₀, _, hA⟩
  have hF : env.HasType univs Γ (.bvar 1) FT := .bvar (.succ .zero)
  have hI : Lookup Γ 2 S := .succ (.succ .zero)
  have hJ : Lookup Γ 3 S := .succ (.succ (.succ .zero))
  have hl : Lookup Γ 0 (.app (.bvar 1) (.bvar 2)) := .zero
  obtain ⟨ht, hn, Hno⟩ := eta_unit_common_native_failure heq hs hi hp hx hz hS hΓ hF
    (.bvar hI) (.bvar hJ) (by decide) (by decide) (by decide) hl
  obtain ⟨RN, RC⟩ := unit_eta_family_native_repair (D := D) hi hp hx hz hS hΓ hF hI hJ hl
  exact ⟨Γ, .bvar 0, .app (.bvar 1) (.bvar 3), _, hΓ, ht, hn,
    nativeIdentityExpansion_equal ht, proofErase_identity_wrapper_beta hΓ ht hn,
    proofErase_identity_wrapper_native hΓ ht hn, RN, RC, Hno⟩

end Lean4Lean.VEnv.Strengthening
