import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureBetaRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaJoinedRecoveryBoundary

/-! # Native histories through identity and constant beta wrappers

Identity recovery starts at the wrapper's stored annotation, even when its
argument cannot recover that annotation. A constant wrapper instead retains
native recovery of its original lower body. Unused-binder certificate descent
removes the intermediate Pi codomain without substituting the actual argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : PureObservation.Definitions}

/-- Every native output of a typed identity wrapper is a forward computation
of its stored annotation. This holds in the full structure/function-eta union,
including arbitrary conversions before and after application. No native
certificate for the argument or confluence hypothesis is required. -/
theorem static_structure_identity_native_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam A (.bvar 0)) x)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) out := by
  have hn : ¬ IsProof Γ x := fun hp =>
    RN.ne_proof (proofErase_eq_proof.2 ((isProof_congr hΓ (nativeIdentityExpansion_equal hx)).2 hp))
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hv : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have hnv : ¬ IsProof (A :: Γ) (.bvar 0) := by
    intro hp
    have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
    exact hn ((isProof_subst hΓ W hv).2 hp)
  obtain ⟨Y, RY, RC⟩ := static_structure_root_beta_native_factor heq hs hΓ hA hv hx RN
  rw [show proofErase (A :: Γ) (.bvar 0) = .bvar 0 from if_neg hnv] at RY
  have RAY : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      ((proofErase Γ A).liftN 1) Y := RY.bvar_compute
  obtain ⟨B, _, RB, EB⟩ := proofErase_scoped_compute_certificate_descend
    (erased_static_structure_eta_expansion_union_certificate_descent heq hs)
    hΓ hΓA Ctx.LiftN.one hA rfl RAY
  rw [← EB] at RC
  simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
    ProofShape.lift_subst_cons, ProofShape.subst_id] at RC
  exact RB.trans RC

/-- Native recovery of an identity wrapper is exactly computation of its
stored annotation. The forward direction gives a history; the reverse direction
uses the wrapper's syntax-directed exact recovery and the given computation. -/
theorem static_structure_identity_native_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x A) (hn : ¬ IsProof Γ x) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam A (.bvar 0)) x)) out ↔
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) out :=
  ⟨static_structure_identity_native_origin heq hs hΓ hx,
    fun R => (proofErase_identity_wrapper_native hΓ hx hn).convert R⟩

/-- A beta wrapper returning a body already typed below its binder preserves
every selected native type on contraction. The discarded argument needs no
native certificate, even when it is retained and the guard uses the full union. -/
theorem static_structure_constant_beta_native_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hb : env.HasType univs Γ b B)
    (hx : env.HasType univs Γ x A)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam A b.lift) x)) out) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ b) out := by
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hb' := hb.weakN henv (Ctx.LiftN.one (A := A))
  obtain ⟨selected, RB, RC⟩ := static_structure_root_beta_native_factor heq hs hΓ hA hb' hx RN
  rw [proofErase_liftN hΓ hΓA Ctx.LiftN.one hb] at RB
  obtain ⟨C, _, RN', EC⟩ := proofErase_scoped_recovery_certificate_descend
    (erased_static_structure_eta_expansion_union_certificate_descent heq hs)
    hΓ hΓA Ctx.LiftN.one hb rfl RB
  rw [← EC] at RC
  simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
    ProofShape.lift_subst_cons, ProofShape.subst_id] at RC
  exact RN'.convert RC

/-- Adding or removing a typed constant beta wrapper leaves the complete set
of selected native outputs unchanged. Proof sources need no special premise:
any native certificate already guarantees that the source is retained. -/
theorem static_structure_constant_beta_native_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hb : env.HasType univs Γ b B)
    (hx : env.HasType univs Γ x A) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam A b.lift) x)) out ↔
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ b) out := by
  refine ⟨static_structure_constant_beta_native_recovery heq hs hΓ hb hx, ?_⟩
  intro RN
  have hn : ¬ IsProof Γ b := fun hp => RN.ne_proof (proofErase_eq_proof.2 hp)
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hb' := hb.weakN henv (Ctx.LiftN.one (A := A))
  have hf := HasType.lam hA hb'
  have HE : env.IsDefEq univs Γ (.app (.lam A b.lift) x) b B := by
    simpa only [VExpr.inst_lift] using IsDefEq.beta hb' hx
  have hne : ¬ IsProof Γ (.app (.lam A b.lift) x) := mt (isProof_congr hΓ HE).1 hn
  have hrename : ∀ {Δ Δ' a b τ}, ErasedStaticStructureEtaExpansionUnion D Δ a b →
      ContextRenaming Δ Δ' τ →
      ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst τ) (b.subst τ) := by
    intro Δ Δ' a b τ ⟨n, H⟩ W
    exact ⟨n, erased_static_structure_eta_expansion_stage_rename heq hs n H W⟩
  have RL := RN.rename hrename (ContextRenaming.of_liftN hΓ hΓA Ctx.LiftN.one)
  simp only [subst_bvar_liftN, proofEraseCtx] at RL
  rw [show proofErase Γ (.app (.lam A b.lift) x) = .app _ _ from if_neg hne,
    show proofErase Γ (.lam A b.lift) = .lam _ _ from if_neg (not_isProof_fn hΓ hf hx hne),
    proofErase_liftN hΓ hΓA Ctx.LiftN.one hb]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
    ProofShape.lift_subst_cons, ProofShape.subst_id] using
    (ScopedTypeRecovery.app (a := proofErase Γ x) (ScopedTypeRecovery.lam RL))

/-- The generated constant-expansion primitive preserves every native output
in both directions, even when recovery uses arbitrary later eta stages. -/
theorem static_structure_constant_expansion_native_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T) (hn : ¬ IsProof Γ e) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (constantExpansion (proofErase Γ e)) out ↔
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ e) out := by
  rw [← proofErase_constantExpansion hΓ ht hn]
  exact static_structure_constant_beta_native_iff heq hs hΓ ht (HasType.sort (l := .zero) (by trivial))

end Lean4Lean.VEnv.Strengthening
