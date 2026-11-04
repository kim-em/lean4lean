import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionNativeUnion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedLevelExposure

/-! # Dependent identity expansions beyond the old computation union

The recovered annotation can depend on the ambient context. The fresh generic
Type variable gives an actual typed witness, rather than just a raw rewrite.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private scoped_normal_fixed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params] {D : PureObservation.Definitions}

/-- A native certificate enables the exact erased identity expansion at the
next finite stage. Its domain need not be closed or a literal universe. -/
theorem proofErase_expansion_identity_forward (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e A)
    (R : ScopedTypeRecovery (ErasedExpansionStage D n) (proofEraseCtx Γ)
      (proofErase Γ e) (proofErase Γ A)) :
    ScopedCompute (ErasedExpansionStage D (n + 1)) (proofEraseCtx Γ)
      (proofErase Γ e) (proofErase Γ (.app (.lam A (.bvar 0)) e)) := by
  have hn : ¬ IsProof Γ e := fun hp => R.ne_proof (proofErase_eq_proof.2 hp)
  rw [proofErase_nativeIdentityExpansion hΓ ht hn]
  exact .base (.inr (.inr (.inr (.intro R))))

/-- A universe-extended primitive still cannot move a bare variable. -/
theorem erased_level_recovered_union_variable_fixed
    (R : ScopedCompute (ErasedLevelRecoveredUnion D) Δ (.bvar i) out) : out = .bvar i := by
  apply scoped_normal_fixed R
  intro Δ
  refine ⟨?_, trivial⟩
  rintro out ⟨n, H⟩
  rcases erased_level_recovered_stage_root n H with H | H
  · exact H
  · cases H

/-- A generic type variable now computes to its identity expansion, although
no computation in the entire previous union can do so. Both endpoints are
erasures of actual terms in the same well-formed context. -/
theorem generic_type_identity_repair (hΓ : OnCtx Γ (env.IsType univs)) :
    let ΓT := VExpr.sort (.succ .zero) :: Γ
    let e := VExpr.bvar 0
    let expanded := VExpr.app (.lam (.sort (.succ .zero)) (.bvar 0)) e
    (¬ ScopedCompute (ErasedLevelRecoveredUnion D) (proofEraseCtx ΓT)
      (proofErase ΓT e) (proofErase ΓT expanded)) ∧
    ScopedCompute (ErasedExpansionStage D 1) (proofEraseCtx ΓT)
      (proofErase ΓT e) (proofErase ΓT expanded) := by
  dsimp only
  let ΓT := VExpr.sort (.succ .zero) :: Γ
  have hS : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := .sort (by trivial)
  have hΓT : OnCtx ΓT (env.IsType univs) := ⟨hΓ, _, hS⟩
  have ht : env.HasType univs ΓT (.bvar 0) (.sort (.succ .zero)) := .bvar .zero
  have hn := not_isProof_of_sort hΓT ht
  have EE : proofErase ΓT (.bvar 0) = .bvar 0 := if_neg hn
  have ES : proofErase ΓT (.sort (.succ .zero)) = .sort (.succ .zero) :=
    if_neg (not_isProof_of_sort hΓT (HasType.sort (by trivial)))
  have R : ScopedTypeRecovery (ErasedExpansionStage D 0) (proofEraseCtx ΓT)
      (proofErase ΓT (.bvar 0)) (proofErase ΓT (.sort (.succ .zero))) := by
    rw [EE, ES]
    have EΓ : proofEraseCtx ΓT = .sort (.succ .zero) :: proofEraseCtx Γ := by
      rw [show proofEraseCtx ΓT = proofErase Γ (.sort (.succ .zero)) :: proofEraseCtx Γ from rfl]
      rw [show proofErase Γ (.sort (.succ .zero)) = .sort _ from if_neg (not_isProof_of_sort hΓ hS)]
    rw [EΓ]
    exact .bvar
  constructor
  · intro H
    change ScopedCompute _ (proofEraseCtx ΓT) (proofErase ΓT (.bvar 0))
      (proofErase ΓT (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.bvar 0))) at H
    rw [proofErase_nativeIdentityExpansion hΓT ht hn, EE, ES] at H
    cases erased_level_recovered_union_variable_fixed H
  · exact proofErase_expansion_identity_forward hΓT ht R

end Lean4Lean.VEnv.Strengthening
