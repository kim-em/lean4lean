import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUniverseContext
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeChangePaths
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStableEqComputation

/-! # Two-way checking through primitive computation to a universe

A sound computation to a literal sort supplies actual type equality. Forward
checking uses universe-oracle recovery; backward checking recovers the reduced
annotation from the original variable declaration. The Eq type probe is a
concrete primitive instance, licensed by its future index certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
variable [Params]

private theorem carrier_context_compute_back
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ A B (.sort u))
    (R : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ B))
    (ha : env.HasType univs (B :: Γ) a T) (hb : env.HasType univs (B :: Γ) b T)
    (H : JointCarrierGuard Step (proofEraseCtx (B :: Γ)) (proofErase (B :: Γ) T)
      (proofErase (B :: Γ) a) (proofErase (B :: Γ) b)) :
    JointCarrierGuard Step (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) T)
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, HE.hasType.2⟩
  have W := RecoveringSubstitution.of_domain_compute
    (fun H W => hsubst H W.interpretation) hΓ HE R
  have HC := H.subst_recovering hstep (fun H W => hsubst H W.interpretation)
    (fun H => H) (fun _ _ _ W H => .base (hsubst H W.interpretation))
    hΓB ha hb rfl rfl rfl rfl W
  simp only [ProofShape.subst_id] at HC
  have WC : IsDefEqCtx env univs [] (B :: Γ) (A :: Γ) := .succ (.refl hΓ) HE.symm
  rwa [proofErase_defeqCtx hΓB WC (ha.isType henv hΓB).choose_spec,
    proofErase_defeqCtx hΓB WC ha, proofErase_defeqCtx hΓB WC hb] at HC

/-- Any sound, substitution-closed primitive computation of a typed binder
annotation to a literal sort preserves both joint checking modes in both
directions. The path may contain arbitrary primitive steps and prefixes;
no confluence or beta-only restriction is imposed. -/
theorem proofErase_universe_compute_context_iff
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (R : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ A) (.sort v))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T) :
    (JointCompare Step (proofEraseCtx (A :: Γ)) mode
        (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) ↔
      JointCompare Step (proofEraseCtx (.sort v :: Γ)) mode
        (proofErase (.sort v :: Γ) a) (proofErase (.sort v :: Γ) b)) ∧
    (JointCarrierGuard Step (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) T)
        (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) ↔
      JointCarrierGuard Step (proofEraseCtx (.sort v :: Γ)) (proofErase (.sort v :: Γ) T)
        (proofErase (.sort v :: Γ) a) (proofErase (.sort v :: Γ) b)) := by
  obtain ⟨S, HE, ES⟩ := proofErase_scoped_compute_realize hstep hΓ hA rfl rfl R
  obtain rfl := erase_sort_inv ES
  have R' : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ (.sort v)) := by
    rw [ES]
    exact R
  have W : IsDefEqCtx env univs [] (A :: Γ) (.sort v :: Γ) := .succ (.refl hΓ) HE
  have hf := proofErase_joint_universe_binder (mode := mode) hstep hhead hsubst hΓ HE ha hb
  exact ⟨⟨hf.1, fun H => proofErase_joint_context_compute_back hstep hsubst hΓ HE R'
    (ha.defeqDFC henv W) (hb.defeqDFC henv W) H⟩,
    ⟨hf.2, fun H => carrier_context_compute_back hstep hsubst hΓ HE R'
      (ha.defeqDFC henv W) (hb.defeqDFC henv W) H⟩⟩

/-- A universe-valued Eq probe and its literal-sort minor support exactly the
same typed body comparisons and carrier guards in the certified relation.
The supplied future comparison of proposition indices constructs the primitive
path; the equality major is arbitrary and the indices need not compute to a
common reduct. No general index-certificate coverage is asserted. -/
theorem eqTypeProbe_universe_context_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (HF : BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)
      (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ Q))
    (ha : env.HasType univs (eqTypeProbe (.succ v) (.sort v) P Q q :: Γ) a T)
    (hb : env.HasType univs (eqTypeProbe (.succ v) (.sort v) P Q q :: Γ) b T) :
    (JointCompare (ErasedBetaStableJoint D)
        (proofEraseCtx (eqTypeProbe (.succ v) (.sort v) P Q q :: Γ)) mode
        (proofErase (eqTypeProbe (.succ v) (.sort v) P Q q :: Γ) a)
        (proofErase (eqTypeProbe (.succ v) (.sort v) P Q q :: Γ) b) ↔
      JointCompare (ErasedBetaStableJoint D) (proofEraseCtx (.sort v :: Γ)) mode
        (proofErase (.sort v :: Γ) a) (proofErase (.sort v :: Γ) b)) ∧
    (JointCarrierGuard (ErasedBetaStableJoint D)
        (proofEraseCtx (eqTypeProbe (.succ v) (.sort v) P Q q :: Γ))
        (proofErase (eqTypeProbe (.succ v) (.sort v) P Q q :: Γ) T)
        (proofErase (eqTypeProbe (.succ v) (.sort v) P Q q :: Γ) a)
        (proofErase (eqTypeProbe (.succ v) (.sort v) P Q q :: Γ) b) ↔
      JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx (.sort v :: Γ))
        (proofErase (.sort v :: Γ) T)
        (proofErase (.sort v :: Γ) a) (proofErase (.sort v :: Γ) b)) := by
  have hS : env.HasType univs Γ (.sort v) (.sort (.succ v)) := .sort hv
  have R := eqTypeProbe_compute_certified_of_family heq hs hregistry hΓ hS hP hQ hq HF
  rw [show proofErase Γ (.sort v) = .sort v from if_neg (not_isProof_of_sort hΓ hS)] at R
  exact proofErase_universe_compute_context_iff (erased_beta_stable_joint_descent heq hs)
    erased_beta_stable_joint_head (erased_beta_stable_joint_subst heq hs) hΓ
    (eqTypeProbe_typed heq hΓ hS hP hQ hq) R ha hb

end Lean4Lean.VEnv.Strengthening
