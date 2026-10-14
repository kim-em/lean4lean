import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredLambdaDomains

/-! # Typed substitution of recovered comparison still contains the front

Re-synthesizing some output type is weaker than substituting a comparison
certificate. Even one typed binder instantiation of an inferred stage-zero
certificate, allowing any finite output stage, implies PropositionFront.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Missing unrestricted typed instantiation for inferred recovered comparison.
The endpoints share an original type; the argument need only have the declared
type, with no exact recovery premise. This is not a smaller front obligation. -/
def TypedRecoveredInstantiation (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ A u x a b T}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ A (.sort u) →
    env.HasType univs Γ x A → env.HasType univs (A :: Γ) a T →
    env.HasType univs (A :: Γ) b T → ErasedRecoveredComparison D 0 false (A :: Γ) a b →
    ∃ stage, ErasedRecoveredComparison D stage false Γ (a.inst x) (b.inst x)

/-- Substituting a converted constant-body lambda into the recovered eta
certificate of a variable forces inferred comparison of the two domains. -/
theorem TypedRecoveredInstantiation.sort_coverage (H : TypedRecoveredInstantiation D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort u)) (hQ : env.HasType univs Γ Q (.sort u))
    (HPQ : env.IsDefEq univs Γ P Q (.sort u)) :
    ∃ stage, ErasedRecoveredComparison D stage false Γ P Q := by
  let F := VExpr.forallE P (.sort (.succ .zero))
  have hx : env.HasType univs Γ (domainProbe Q) F :=
    (IsDefEq.forallEDF HPQ.symm (HasType.sort (by trivial))).defeq (domainProbe_typed hQ)
  obtain ⟨v, hF⟩ := hx.isType henv hΓ
  have hΓF : OnCtx (F :: Γ) (env.IsType univs) := ⟨hΓ, v, hF⟩
  have hl : Lookup (F :: Γ) 0 (.forallE P.lift (.sort (.succ .zero))) := .zero
  have hf : env.HasType univs (F :: Γ) (.bvar 0) (.forallE P.lift (.sort (.succ .zero))) :=
    .bvar hl
  have HE := IsDefEq.eta hf
  have HC : ErasedRecoveredComparison D 0 false (F :: Γ)
      (.lam P.lift (.app (VExpr.bvar 0).lift (.bvar 0))) (.bvar 0) := by
    rcases proofErase_lookup_eta_forward (Step := ErasedComparedKStage D 0) hΓF hl with E | H
    · unfold ErasedRecoveredComparison
      rw [E]
      exact .base .refl
    · exact H.compare
  obtain ⟨stage, HR⟩ := H hΓ hF hx HE.hasType.1 hf HC
  have EL : (VExpr.lam P.lift (.app (VExpr.bvar 0).lift (.bvar 0))).inst (domainProbe Q) =
      .lam P (.app (domainProbe Q).lift (.bvar 0)) := by
    simp [VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN, liftVar, inst_liftN]
  have ER : (VExpr.bvar 0).inst (domainProbe Q) = domainProbe Q := by simp [VExpr.inst, VExpr.instVar]
  rw [EL, ER] at HR
  have hlong := IsDefEq.eta hx
  have hn := not_isProof_function_to_sort hΓ hlong.hasType.1
  change ¬ IsProof Γ (.lam P (.app (domainProbe Q).lift (.bvar 0))) at hn
  unfold ErasedRecoveredComparison at HR ⊢
  rw [show proofErase Γ (.lam P (.app (domainProbe Q).lift (.bvar 0))) =
      .lam (proofErase Γ P) (proofErase (P :: Γ) (.app (domainProbe Q).lift (.bvar 0)))
      from if_neg hn, proofErase_domainProbe hΓ hQ] at HR
  exact ⟨stage, HR.lam_domains (erased_compared_K_stage_root stage)⟩

/-- Unrestricted typed instantiation, even at one binder and with a flexible
finite output stage, would prove the complete canonical-Eq proposition front. -/
theorem typedRecoveredInstantiation_implies_propositionFront (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (H : TypedRecoveredInstantiation D) : PropositionFront := by
  intro Γ Q P R hΓ hQ hP hR HE
  have hΓ' : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, hQ⟩
  have hP' : env.HasType univs (Q :: Γ) P.lift (.sort .zero) := hP.weak henv
  have hR' : env.HasType univs (Q :: Γ) R.lift (.sort .zero) := hR.weak henv
  obtain ⟨stage, HC⟩ := H.sort_coverage hΓ' hP' hR' (HE.of_l henv hΓ' hP')
  have HC' : ErasedRecoveredComparison D stage false (Q :: Γ)
      (P.lift' (.skip .refl)) (R.lift' (.skip .refl)) := by
    simpa only [← lift_eq_lift'] using HC
  exact (HC'.descend heq hs hΓ hΓ' (.skip .refl) hP hR).2
    rfl (not_isProof_of_sort hΓ hP)

end Lean4Lean.VEnv.Strengthening
