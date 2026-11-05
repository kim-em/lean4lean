import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCommonCallerTelescope
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeInstantiationBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaJoinedRecoveryBoundary

/-! # A changed-domain square repairs the fresh-domain caller boundary

The beta-reduced caller cannot recover the old domain at all. Unit eta supplies
a common native output with a different domain, and the telescope square joins
caller beta with argument reannotation there. The common output is constructed
by the witness, not assumed as a separate joining or coverage hypothesis.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A typed caller beta/reannotation fork has all four forward square edges
despite failure of every native Pi with the old argument domain at its reduced
caller. The shared argument uses a derived one-binder telescope. The only
environment-specific premises are a closed positive empty structure, as in
the boundary; no type-fork joining, common coverage, argument recovery, or
common-output premise is added. This repairs this witness, not all histories. -/
theorem static_structure_fresh_domain_caller_changed_telescope_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hix : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ f g L A es,
      let Q := VExpr.forallE A (.sort (.succ .zero))
      OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ f (.forallE Q (.sort (.succ .zero))) ∧
      env.HasType univs Γ g (.forallE Q (.sort (.succ .zero))) ∧
      env.HasType univs Γ (.lam L (.sort .zero)) Q ∧ es.length = 1 ∧
      BetaRed (proofErase Γ f) (proofErase Γ g) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ f) (proofErase Γ (.forallE Q (.sort (.succ .zero)))) ∧
      (∀ Step, ErasedScopedPrimitiveDescent Step → ∀ selected,
        ¬ ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ g)
          (.forallE (proofErase Γ Q) selected)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f (.lam L (.sort .zero))))
        (proofErase Γ (.app f (.lam A (.sort .zero)))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f (.lam L (.sort .zero))))
        (proofErase Γ (.app g (.lam L (.sort .zero)))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f (.lam A (.sort .zero))))
        (proofErase Γ (.app g (VExpr.wrapLams es (.sort .zero)))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app g (.lam L (.sort .zero))))
        (proofErase Γ (.app g (VExpr.wrapLams es (.sort .zero)))) := by
  obtain ⟨Γ, Q, e, x, _, _, hΓ, hx, he, ⟨A, rfl⟩, ⟨L, rfl⟩,
    ⟨common, RN, RT⟩, _, Hno, _⟩ :=
    static_structure_generic_family_common_domain_instantiation_beta_residual_failure heq hs hi hp hix hz hS
  let Q := VExpr.forallE A (.sort (.succ .zero))
  let F := VExpr.forallE Q (.sort (.succ .zero))
  let f := VExpr.app (.lam F (.bvar 0)) e
  have hne := not_isProof_function_to_sort hΓ he
  have hf : env.HasType univs Γ f F := (nativeIdentityExpansion_equal he).hasType.1
  have RN0 : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ F) := proofErase_identity_wrapper_native hΓ he hne
  have RNU : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ F) := RN0.mono (fun H => ⟨0, H⟩)
  obtain ⟨_, hF⟩ := he.isType henv hΓ
  change env.HasType univs Γ F _ at hF
  change ScopedTypeRecovery _ _ _ (proofErase Γ (.forallE Q (.sort (.succ .zero)))) at RNU
  rw [show proofErase Γ (.forallE Q (.sort (.succ .zero))) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hF)] at RNU
  have RB := proofErase_identity_wrapper_beta hΓ he hne
  obtain ⟨g, es, HE, EG, hlen, R₁, R₂, R₃, R₄⟩ :=
    static_structure_common_caller_reannotation_square (ds := [A]) (written := [L])
      heq hs hΓ hf hx rfl RNU (.beta RB) RN RT
  refine ⟨Γ, f, g, L, A, es, hΓ, hf, HE.hasType.2, hx, hlen.symm, ?_, RN0, ?_, R₁, R₂, R₃, R₄⟩
  · rwa [EG]
  · intro Step hstep selected R
    rw [EG] at R
    exact Hno Step hstep selected R

end Lean4Lean.VEnv.Strengthening
