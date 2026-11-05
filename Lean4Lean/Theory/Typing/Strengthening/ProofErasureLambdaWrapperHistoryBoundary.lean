import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaWrapperHistory
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeFreshTypeBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeHeadBeta

/-! # A generated wrapper keeps its origin after exact recovery is lost

The inner argument evolves by beta below a lambda. It remains a literal lambda
with the same domain history, but no longer recovers the outer identity frame's
old annotation. The frame was actually licensed by native recovery before this
evolution; its historical certificate is not an arbitrary type conversion.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

private theorem native_constant_function
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ A)) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam (.sort (.succ .zero)) x.lift))
      (proofErase Γ (.forallE (.sort (.succ .zero)) A.lift)) := by
  have hS : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    .sort (by trivial)
  have hΓS : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) := ⟨hΓ, _, hS⟩
  have hx' := hx.weakN henv (Ctx.LiftN.one (A := .sort (.succ .zero)))
  have hn : ¬ IsProof Γ x := fun hp => RN.ne_proof (proofErase_eq_proof.2 hp)
  have hfx := HasType.lam hS hx'
  have HE : env.IsDefEq univs Γ
      (.app (.lam (.sort (.succ .zero)) x.lift) (.sort .zero)) x A := by
    simpa only [VExpr.inst_lift] using IsDefEq.beta hx' (HasType.sort (l := .zero) (by trivial))
  have hnapp := mt (isProof_congr hΓ HE).1 hn
  have hnf := not_isProof_fn hΓ hfx (HasType.sort (l := .zero) (by trivial)) hnapp
  have hrename : ∀ {Δ Δ' a b τ}, ErasedStaticStructureEtaExpansionUnion D Δ a b →
      ContextRenaming Δ Δ' τ → ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst τ) (b.subst τ) := by
    intro Δ Δ' a b τ ⟨n, H⟩ W
    exact ⟨n, erased_static_structure_eta_expansion_stage_rename heq hs n H W⟩
  have RL := RN.rename hrename (ContextRenaming.of_liftN hΓ hΓS Ctx.LiftN.one)
  simp only [subst_bvar_liftN, proofEraseCtx] at RL
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  have hPi := HasType.forallE hS (hA.weakN henv Ctx.LiftN.one)
  rw [show proofErase Γ (.lam (.sort (.succ .zero)) x.lift) = .lam _ _ from if_neg hnf,
    show proofErase Γ (.forallE (.sort (.succ .zero)) A.lift) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hPi),
    proofErase_liftN hΓ hΓS Ctx.LiftN.one hx,
    proofErase_liftN hΓ hΓS Ctx.LiftN.one hA]
  exact ScopedTypeRecovery.lam RL

private theorem constant_function_native_body
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x A) (hn : ¬ IsProof Γ x)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam (.sort (.succ .zero)) x.lift))
      (proofErase Γ (.forallE (.sort (.succ .zero)) A.lift))) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ A) := by
  have hS : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := .sort (by trivial)
  have hΓS : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) := ⟨hΓ, _, hS⟩
  have hx' := hx.weakN henv (Ctx.LiftN.one (A := .sort (.succ .zero)))
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  have hPi := HasType.forallE hS (hA.weakN henv Ctx.LiftN.one)
  have HE : env.IsDefEq univs Γ
      (.app (.lam (.sort (.succ .zero)) x.lift) (.sort .zero)) x A := by
    simpa only [VExpr.inst_lift] using IsDefEq.beta hx' (HasType.sort (l := .zero) (by trivial))
  have hnapp := mt (isProof_congr hΓ HE).1 hn
  rw [show proofErase Γ (.forallE (.sort (.succ .zero)) A.lift) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi), proofErase_liftN hΓ hΓS Ctx.LiftN.one hA] at RN
  have R := ScopedTypeRecovery.app (a := proofErase Γ (.sort .zero)) RN
  simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
    ProofShape.lift_subst_cons, ProofShape.subst_id] at R
  apply static_structure_constant_beta_native_recovery heq hs hΓ hx (HasType.sort (l := .zero) (by trivial))
  simpa only [show proofErase Γ (.app (.lam (.sort (.succ .zero)) x.lift) (.sort .zero)) = .app _ _ from
    if_neg hnapp] using R

/-- An identity frame generated from an actual native function guard can lose
that guard when its argument beta-reduces under a lambda. Its historical lambda
origin survives, yet contracting the resulting frame is outside NativeHeadBeta.
The same positive empty-structure environment used by the exact-recovery
boundary suffices. This is a strict provenance example, not a counterexample to
strengthening or to common-output recovery. -/
theorem generated_identity_history_outlives_exact_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hix : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ f g Q, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ f Q ∧ env.HasType univs Γ g Q ∧
      VExpr.BetaRed f g ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ f) (proofErase Γ Q) ∧
      NativeIdentityExpansion (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ f) (proofErase Γ (.app (.lam Q (.bvar 0)) f)) ∧
      VExpr.BetaRed (.app (.lam Q (.bvar 0)) f) (.app (.lam Q (.bvar 0)) g) ∧
      LambdaWrapperHistory D Γ (.sort (.succ .zero)) (.app (.lam Q (.bvar 0)) g) ∧
      (¬ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ g) (proofErase Γ Q)) ∧
      ¬ NativeHeadBeta D Γ (.app (.lam Q (.bvar 0)) g) g := by
  obtain ⟨Γ, x, A, hΓ, hx, hn, Hno, _⟩ := descending_native_exact_coverage_failure
    (erased_static_structure_eta_expansion_union_descent heq hs) hi hp hix hz hS
  let w : VExpr := .app (.lam A (.bvar 0)) x
  let f : VExpr := .lam (.sort (.succ .zero)) w.lift
  let g : VExpr := .lam (.sort (.succ .zero)) x.lift
  let Q : VExpr := .forallE (.sort (.succ .zero)) A.lift
  have hW : env.HasType univs Γ w A := (nativeIdentityExpansion_equal hx).hasType.1
  have hsrt : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := .sort (by trivial)
  have hW' := hW.weakN henv (Ctx.LiftN.one (A := .sort (.succ .zero)))
  have hx' := hx.weakN henv (Ctx.LiftN.one (A := .sort (.succ .zero)))
  have hf : env.HasType univs Γ f Q := .lam hsrt hW'
  have hg : env.HasType univs Γ g Q := .lam hsrt hx'
  have RNw : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ w) (proofErase Γ A) := proofErase_identity_wrapper_native hΓ hx hn
  have RNf := native_constant_function heq hs hΓ hW RNw
  have HNg : ¬ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ g) (proofErase Γ Q) := fun H => Hno (constant_function_native_body heq hs hΓ hx hn H)
  have Rfg : VExpr.BetaRed f g := by
    apply VExpr.BetaRed.lam .refl
    change VExpr.BetaRed (.app (.lam A.lift (.bvar 0)) x.lift) x.lift
    simpa only [VExpr.inst, VExpr.instVar_zero] using
      (VExpr.BetaRed.beta (A := A.lift) (b := .bvar 0) (a := x.lift))
  have ES : proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) :=
    if_neg (not_isProof_of_sort hΓ hsrt)
  have HF : LambdaWrapperHistory D Γ (.sort (.succ .zero)) f :=
    .payload hsrt hW' (ES ▸ ScopedCompute.refl)
  have HG : LambdaWrapperHistory D Γ (.sort (.succ .zero)) g :=
    .payload hsrt hx' (ES ▸ ScopedCompute.refl)
  have HI := HF.native_identity heq hs hΓ hf RNf
  have HnF : ¬ IsProof Γ f := fun hp => RNf.ne_proof (proofErase_eq_proof.2 hp)
  have HnG : ¬ IsProof Γ g := by
    intro hp
    exact HnF ((isProof_congr hΓ (beta_eq hΓ hf Rfg)).2 hp)
  refine ⟨Γ, f, g, Q, hΓ, hf, hg, Rfg, RNf, ?_, .app .refl Rfg,
    HI.identity_argument hg HG, HNg, ?_⟩
  · rw [proofErase_nativeIdentityExpansion hΓ hf HnF]
    exact .intro RNf
  · intro H
    exact HNg (H.recovery heq hs hΓ (nativeIdentityExpansion_equal hg).hasType.1
      (proofErase_identity_wrapper_native hΓ hg HnG))

end Lean4Lean.VEnv.Strengthening
