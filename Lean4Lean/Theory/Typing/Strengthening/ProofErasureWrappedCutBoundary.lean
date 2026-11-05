import Lean4Lean.Theory.Typing.Strengthening.ProofErasureWrappedCutSquare
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeBetaResidualBoundary

/-! # A created wrapper survives loss of its argument's native certificate

The positive empty-structure example supplies a typed retained value without
native recovery at its assigned type. A recoverable identity wrapper around it
starts the marked development. A further identity frame is created by a native
guard, then its argument computes to the unrecoverable value. Its ordinary
annotation history remains valid and the frame can still contract.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- A wrapper introduced by an actual native guard remains a valid developed
state after its argument loses that guard. This uses the established positive
empty-structure environment assumptions, not a confluence or strengthening
counterexample. The final frame can contract without renewing the lost guard. -/
theorem wrapped_cut_development_outlives_native_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ A x w v, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ x A ∧
      env.HasType univs Γ w A ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ w) (proofErase Γ A) ∧
      ¬ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ x) (proofErase Γ A) ∧
      ReflTransGen (WrappedCutStep D Γ A (.bvar 0) w v A.lift)
        (.cut (proofErase Γ A, proofErase (A :: Γ) (.bvar 0), proofErase Γ w) (.bvar 0))
        (.identity (proofErase Γ A) (.done (proofErase Γ x))) ∧
      WrappedCut.Valid D Γ A (.bvar 0) w v A.lift
        (.identity (proofErase Γ A) (.done (proofErase Γ x))) ∧
      WrappedCutStep D Γ A (.bvar 0) w v A.lift
        (.identity (proofErase Γ A) (.done (proofErase Γ x))) (.done (proofErase Γ x)) := by
  obtain ⟨Γ, x, A, hΓ, ht, hn, Hno, _⟩ := descending_native_exact_coverage_failure
    (erased_static_structure_eta_expansion_union_descent heq hs) hi hp hx hz hS
  let w : VExpr := .app (.lam A (.bvar 0)) x
  have hw : env.HasType univs Γ w A := (nativeIdentityExpansion_equal ht).hasType.1
  have hnw : ¬ IsProof Γ w := fun H => hn ((isProof_congr hΓ (nativeIdentityExpansion_equal ht)).1 H)
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ w) (proofErase Γ A) := proofErase_identity_wrapper_native hΓ ht hn
  obtain ⟨v, hA⟩ := ht.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
  have hb : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have hnv : ¬ IsProof (A :: Γ) (.bvar 0) := by
    intro H
    have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := w) (A₀ := A)).substEq hΓA hw
    exact hnw ((isProof_subst hΓ W hb).2 H)
  have EV : proofErase (A :: Γ) (.bvar 0) = .bvar 0 := if_neg hnv
  let initial : WrappedCut :=
    .cut (proofErase Γ A, proofErase (A :: Γ) (.bvar 0), proofErase Γ w) (.bvar 0)
  have RNinitial : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      initial.source (proofErase Γ A) := by
    change ScopedTypeRecovery _ _ (.app (.lam _ (proofErase (A :: Γ) (.bvar 0))) _) _
    rw [EV]
    exact raw_identity_native _ _
  have R₁ : ReflTransGen (WrappedCutStep D Γ A (.bvar 0) w v A.lift)
      initial (.identity (proofErase Γ A) initial) := .tail .rfl (.identity_expand RNinitial)
  have R₂ := R₁.tail (WrappedCutStep.identity_inner (WrappedCutStep.cut_contract))
  have R₂' : ReflTransGen (WrappedCutStep D Γ A (.bvar 0) w v A.lift)
      initial (.identity (proofErase Γ A) (.done (proofErase Γ w))) := by
    simpa only [EV, ProofShape.inst, instVar, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self,
      ProofShape.liftN_zero] using R₂
  have RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ w) (proofErase Γ x) := .beta (proofErase_identity_wrapper_beta hΓ ht hn)
  have R₃ := R₂'.tail (WrappedCutStep.identity_inner (WrappedCutStep.done_compute RX))
  have hno : ¬ IsProof Γ (.app (.lam A (.bvar 0)) w) :=
    fun H => hnw ((isProof_congr hΓ (nativeIdentityExpansion_equal hw)).1 H)
  have Hinit : WrappedCut.Valid D Γ A (.bvar 0) w v A.lift initial :=
    .cut (CutPivotHistory.refl hA hb hw)
  have Hfinal := (wrapped_cut_steps_simulate heq hs hΓ hno (fun _ => RN) R₃ Hinit).1
  exact ⟨Γ, A, x, w, v, hΓ, ht, hw, RN, Hno, R₃, Hfinal, .identity_contract⟩

end Lean4Lean.VEnv.Strengthening
