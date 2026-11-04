import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstantExpansion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeImageRecovery

/-! # Identity expansion with a recovered annotation

The new binder's domain must be recovered from the retained source. This
certificate, unlike an arbitrary reverse beta redex, reconstructs its annotation
below an inserted block. Guard transport uses exact native-image recovery.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- A native recovery certificate never starts at the erased proof marker. -/
theorem ProofShape.ScopedTypeRecovery.ne_proof (R : ScopedTypeRecovery Step Δ a A) : a ≠ .proof := by
  induction R with
  | convert _ _ ih => exact ih
  | bvar | sort | const | lam | app | forallE | proj => intro E; cases E

/-- Identity expansion uses a type certified at the preceding computation layer. -/
inductive ProofShape.NativeIdentityExpansion
    (Step : List ProofShape → ProofShape → ProofShape → Prop) (Δ : List ProofShape) :
    ProofShape → ProofShape → Prop where
  | intro : ScopedTypeRecovery Step Δ a A → NativeIdentityExpansion Step Δ a (.app (.lam A (.bvar 0)) a)

/-- Increasing the recovery relation preserves identity expansion. -/
theorem ProofShape.NativeIdentityExpansion.mono
    (hstep : ∀ {Δ a b}, Step Δ a b → Step' Δ a b)
    (H : NativeIdentityExpansion Step Δ a b) : NativeIdentityExpansion Step' Δ a b := by
  cases H with
  | intro R => exact .intro (R.mono hstep)

/-- Every typed term is equal to its identity expansion at its actual type. -/
theorem nativeIdentityExpansion_equal (ht : env.HasType univs Γ e A) :
    env.IsDefEq univs Γ (.app (.lam A (.bvar 0)) e) e A := by
  simpa only [VExpr.inst_lift, VExpr.inst, instVar, Nat.lt_irrefl, ↓reduceIte,
    Nat.sub_self, VExpr.liftN_zero] using
    (IsDefEq.beta (show env.HasType univs (A :: Γ) (.bvar 0) A.lift from .bvar .zero) ht)

/-- The fresh identity variable is retained exactly when its actual argument
is retained; typed substitution reflects this fact without strengthening. -/
theorem proofErase_nativeIdentityExpansion (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e A) (hn : ¬ IsProof Γ e) :
    proofErase Γ (.app (.lam A (.bvar 0)) e) =
      .app (.lam (proofErase Γ A) (.bvar 0)) (proofErase Γ e) := by
  obtain ⟨u, hA⟩ := ht.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hx : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := e) (A₀ := A)).substEq hΓA ht
  have hnx : ¬ IsProof (A :: Γ) (.bvar 0) := by
    intro hp
    exact hn ((isProof_subst hΓ W hx).2 hp)
  have hn' := mt (isProof_congr hΓ (nativeIdentityExpansion_equal ht)).1 hn
  rw [show proofErase Γ (.app _ _) = .app _ _ from if_neg hn']
  rw [show proofErase Γ (.lam A (.bvar 0)) = .lam _ _ from
    if_neg (not_isProof_fn hΓ (HasType.lam hA hx) ht hn')]
  rw [show proofErase (A :: Γ) (.bvar 0) = .bvar 0 from if_neg hnx]

/-- Native recovery brings the identity's annotation below every inserted
binder block. The replay is at the source's original type, even if recovery
selected a different convertible type. -/
theorem erased_nativeIdentityExpansion_descent (hstep : ErasedScopedPrimitiveDescent Step) :
    ErasedScopedPrimitiveDescent (NativeIdentityExpansion Step) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  cases H with
  | intro R =>
    obtain ⟨A, he, EA⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ' W ht rfl R
    have hn : ¬ IsProof Γ e := by
      intro hp
      exact R.ne_proof (by rw [proofErase_eq_proof.2 hp]; rfl)
    refine ⟨_, (nativeIdentityExpansion_equal he).symm.toU.of_l henv hΓ ht, ?_⟩
    rw [proofErase_nativeIdentityExpansion hΓ he hn]
    simp only [ProofShape.liftN, EA, liftVar, Nat.zero_lt_succ, ↓reduceIte]

/-- Exact renaming transports both source and recovered identity annotation. -/
theorem ProofShape.NativeIdentityExpansion.rename
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step' Δ' (a.subst τ) (b.subst τ))
    (H : NativeIdentityExpansion Step Δ a b) (W : ContextRenaming Δ Δ' τ) :
    NativeIdentityExpansion Step' Δ' (a.subst τ) (b.subst τ) := by
  cases H with
  | intro R => exact .intro (R.rename hrename W)

/-- The native annotation guard substitutes using the generic recovery
transport theorem; no endpoint completeness premise is added. -/
theorem ProofShape.NativeIdentityExpansion.subst_typed
    (hrename : ∀ {Δ Δ' a b τ}, ImageStep Δ a b → ContextRenaming Δ Δ' τ →
      ImageStep Δ' (a.subst τ) (b.subst τ))
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hinclude : ∀ {Δ a b}, ImageStep Δ a b → Target Δ a b)
    (hcompute : ∀ {Γ Δ Δ' τ e T source out}, ScopedCompute Source Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source →
      NativeImageTransport.ImageSubstitution ImageStep Δ Δ' τ →
      ScopedCompute Target Δ' (source.subst τ) (out.subst τ))
    (H : NativeIdentityExpansion Source Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : NativeImageTransport.ImageSubstitution ImageStep Δ Δ' τ) :
    NativeIdentityExpansion Target Δ' (source.subst τ) (out.subst τ) := by
  cases H with
  | intro R => exact .intro (NativeImageTransport.recovery_of_compute hrename hstep hinclude hcompute R hΓ ht EΓ Ee W)

end Lean4Lean.VEnv.Strengthening
