import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCommonApplicationBetaJoin

/-! # Nondependent common application needs no native argument

A codomain typed before an unused binder remains independent of that binder
through every enriched computation. Certificate descent therefore instantiates
its path exactly at any raw argument. This closes the vacuous case of the type
beta joining obligation without any confluence or recovery hypothesis.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Computation of a type lifted through an unused binder instantiates at any
raw argument. Descent removes the binder from the whole path and endpoint;
there is no requirement that the argument have a native certificate. -/
theorem static_structure_vacuous_type_instantiation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) B.lift) out) (arg : ProofShape) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ B) (out.inst arg) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  rw [proofErase_liftN hΓ hΓA Ctx.LiftN.one hB] at RB
  obtain ⟨B', _, RC, EB⟩ := proofErase_scoped_compute_certificate_descend
    (erased_static_structure_eta_expansion_union_certificate_descent heq hs)
    hΓ hΓA Ctx.LiftN.one hB rfl RB
  rw [← EB]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
    ProofShape.lift_subst_cons, ProofShape.subst_id] using RC

/-- An arbitrary typed argument can be applied to a commonly recovered
function with a nondependent codomain. The written domain and the result type
are unrestricted, as are all intermediate enriched computations. No native
argument, type-fork joining or forward-binder hypothesis is required. -/
theorem static_structure_common_nondependent_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B.lift)) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app f x))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) shared)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ (.forallE A B.lift)) shared) :
    ∃ out, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx Γ) (proofErase Γ (.app f x)) out ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx Γ) (proofErase Γ B) out := by
  obtain ⟨_, hA⟩ := hx.isType henv hΓ
  have happ : env.HasType univs Γ (.app f x) B := by
    simpa only [VExpr.inst_lift] using HasType.app hf hx
  obtain ⟨_, hB⟩ := happ.isType henv hΓ
  have HJ {out} (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) B.lift) out) :
      ∃ joined, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ (B.lift.inst x)) joined ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (out.inst (proofErase Γ x)) joined := by
    exact ⟨_, by simpa only [VExpr.inst_lift] using
      static_structure_vacuous_type_instantiation heq hs hΓ hA hB RB (proofErase Γ x), .refl⟩
  simpa only [VExpr.inst_lift] using
    static_structure_common_application_of_type_beta_join heq hs hΓ hf HJ hn RN RC

/-- The nondependent application case in the common-native interface. The
supplied argument is allowed to lack exact recovery at its assigned domain. -/
theorem CommonNativeArgument.app_nondependent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B.lift)) (hx : env.HasType univs Γ x A)
    (HF : CommonNativeArgument D Γ f (.forallE A B.lift)) :
    CommonNativeArgument D Γ (.app f x) B := by
  intro hn
  obtain ⟨_, RN, RC⟩ := HF (not_isProof_fn hΓ hf hx hn)
  exact static_structure_common_nondependent_application heq hs hΓ hf hx hn RN RC

end Lean4Lean.VEnv.Strengthening
