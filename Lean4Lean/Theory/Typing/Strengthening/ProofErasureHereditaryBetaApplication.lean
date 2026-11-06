import Lean4Lean.Theory.Typing.Strengthening.ProofErasureHereditaryCoreFeedback

/-! # Beta applications of retained body comparisons

The written lambda domains and bodies may differ. One actual argument inhabits
both domains; its identical erased substitution instantiates both body sides.
Typed beta paths prepend the resulting comparison, retaining future arbitrary
substitutions and full-core reductions without an inferred domain certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Instantiation uses the same actual argument at both written domains. The
body certificate is interpreted in the left context, while each erasure law
uses its own genuine typing. No conversion between the two domains is assumed. -/
theorem CoreFamilyCast.Hereditary.instantiate_bodies
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort v))
    (hb : env.HasType univs (A :: Γ) b B) (hc : env.HasType univs (C :: Γ) c E)
    (hx : env.HasType univs Γ x A) (hx' : env.HasType univs Γ x C)
    (H : CoreFamilyCast.Hereditary D n (.compare mode) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) (proofErase (C :: Γ) c)) :
    CoreFamilyCast.Hereditary D n (.compare mode) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (proofErase Γ (c.inst x)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, v, hC⟩
  have W : ContextSubstitution (proofEraseCtx (A :: Γ)) (proofEraseCtx Γ)
      (ProofShape.Subst.one (proofErase Γ x)) :=
    ContextSubstitution.of_typed hΓ (Ctx.InstN.zero.substEq hΓA hx)
      (erasedSubstAgreement_one hΓA hx)
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hb,
    proofErase_instN hΓC hx' Ctx.InstN.zero hc]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one] using H.substitute W

/-- Two displayed beta applications retain comparison when their body history
survives substitution and their common argument has both actual domain typings.
The domains and bodies need not be identical; normalization is not required. -/
theorem CoreFamilyCast.Hereditary.beta_application_same_argument
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort v))
    (hb : env.HasType univs (A :: Γ) b B) (hc : env.HasType univs (C :: Γ) c E)
    (hx : env.HasType univs Γ x A) (hx' : env.HasType univs Γ x C)
    (H : CoreFamilyCast.Hereditary D n (.compare mode) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) (proofErase (C :: Γ) c)) :
    CoreFamilyCast.Hereditary D n (.compare mode) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam A b) x)) (proofErase Γ (.app (.lam C c) x)) := by
  have hleft := (HasType.lam hA hb).app hx
  have hright := (HasType.lam hC hc).app hx'
  exact .prefixes
    (.core hΓ hleft (.beta (proofErase_beta_forward hΓ hleft .beta)))
    (.core hΓ hright (.beta (proofErase_beta_forward hΓ hright .beta)))
    (H.instantiate_bodies hΓ hA hC hb hc hx hx')

omit [Params] in
/-- In an actual canonical-Eq environment the two beta applications keep their
comparison after arbitrary typed substitution and independent full-core paths.
This isolates the application case supported by retained body history. -/
theorem EnvironmentCore.hereditary_beta_application_after
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {n mode Γ u v A C b c B E x Δ' τ left right}, env.HasCanonicalEq →
      OnCtx Γ (env.IsType U) → env.HasType U Γ A (.sort u) → env.HasType U Γ C (.sort v) →
      env.HasType U (A :: Γ) b B → env.HasType U (C :: Γ) c E →
      env.HasType U Γ x A → env.HasType U Γ x C →
      CoreFamilyCast.Hereditary definitions n (.compare mode) (proofEraseCtx (A :: Γ))
        (proofErase (A :: Γ) b) (proofErase (C :: Γ) c) →
      ContextSubstitution (proofEraseCtx Γ) Δ' τ →
      ProofShape.Compute (ErasedLevelCore definitions)
        ((proofErase Γ (.app (.lam A b) x)).subst τ) left →
      ProofShape.Compute (ErasedLevelCore definitions)
        ((proofErase Γ (.app (.lam C c) x)).subst τ) right →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions n) Δ' mode left right := by
  letI := henv.params U
  intro n mode Γ u v A C b c B E x Δ' τ left right heq hΓ hA hC hb hc hx hx' H W RL RR
  exact hereditary_core_family_after henv U heq
    (H.beta_application_same_argument hΓ hA hC hb hc hx hx') W RL RR

end Lean4Lean.VEnv.Strengthening
