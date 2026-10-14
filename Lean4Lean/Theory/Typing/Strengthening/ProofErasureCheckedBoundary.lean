import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCheckedDomains

/-! # What common-type lambda checking changes

Constant-body lambda probes compare in checking mode without a domain guard.
Inferred comparison continues to expose domains, so unrestricted typed
instantiation in inferred mode still implies PropositionFront.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]


/-- Common-mode probes compare by their bodies, independently of their domains.
Endpoint type conversion remains an external premise when this is replayed. -/
theorem ProofShape.CheckedCompare.probe :
    ProofShape.CheckedCompare Step σ τ true (.lam A (.sort u)) (.lam B (.sort u)) :=
  .lamCommon (.base (.base .refl))

/-- Actual typed probes have a checking certificate at every stage. In
particular the old typed beta-transport probe conclusion needs no domain front. -/
theorem checked_domainProbes (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort u)) (hQ : env.HasType univs Γ Q (.sort v)) :
    ErasedCheckedComparison D stage true Γ (domainProbe P) (domainProbe Q) := by
  unfold ErasedCheckedComparison
  rw [proofErase_domainProbe hΓ hP, proofErase_domainProbe hΓ hQ]
  exact .probe

/-- The enlargement is strict at every stage, even on separately typed original
lambdas. Their types are different, so common-mode replay does not equate them. -/
theorem checked_probes_strict (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (stage : Nat) :
    ErasedCheckedComparison D stage true []
      (domainProbe (.sort .zero)) (domainProbe (.forallE (.sort .zero) (.sort .zero))) ∧
    ¬ ErasedRecoveredComparison D stage true []
      (domainProbe (.sort .zero)) (domainProbe (.forallE (.sort .zero) (.sort .zero))) := by
  have hΓ : OnCtx [] (env.IsType univs) := by trivial
  have hP : env.HasType univs [] (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hQ := HasType.forallE hP (HasType.sort (l := .zero) (Γ := [.sort .zero]) (by trivial))
  refine ⟨checked_domainProbes hΓ hP hQ, ?_⟩
  intro H
  unfold ErasedRecoveredComparison at H
  rw [proofErase_domainProbe hΓ hP, proofErase_domainProbe hΓ hQ] at H
  have HD : ErasedRecoveredComparison D stage false [] (.sort .zero)
      (.forallE (.sort .zero) (.sort .zero)) :=
    H.probe_inv (erased_compared_K_stage_root stage)
  have HD' : ErasedRecoveredComparison D stage false []
      ((VExpr.sort .zero).liftN 0) ((VExpr.forallE (.sort .zero) (.sort .zero)).liftN 0) := by
    simpa only [VExpr.liftN_zero] using HD
  have HE := (HD'.descendN heq hs hΓ hΓ (Ctx.LiftN.zero []) hP hQ).2
    rfl (not_isProof_of_sort hΓ hP)
  exact HE.sort_forallE_inv henv hΓ

/-- Missing unrestricted typed instantiation for inferred recovered comparison.
The endpoints share an original type; the argument need only have the declared
type, with no exact recovery premise. This is not a smaller front obligation. -/
def TypedCheckedInstantiation (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ A u x a b T}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ A (.sort u) →
    env.HasType univs Γ x A → env.HasType univs (A :: Γ) a T →
    env.HasType univs (A :: Γ) b T → ErasedCheckedComparison D 0 false (A :: Γ) a b →
    ∃ stage, ErasedCheckedComparison D stage false Γ (a.inst x) (b.inst x)

/-- Substituting a converted constant-body lambda into the recovered eta
certificate of a variable forces inferred comparison of the two domains. -/
theorem TypedCheckedInstantiation.sort_coverage (H : TypedCheckedInstantiation D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort u)) (hQ : env.HasType univs Γ Q (.sort u))
    (HPQ : env.IsDefEq univs Γ P Q (.sort u)) :
    ∃ stage, ErasedCheckedComparison D stage false Γ P Q := by
  let F := VExpr.forallE P (.sort (.succ .zero))
  have hx : env.HasType univs Γ (domainProbe Q) F :=
    (IsDefEq.forallEDF HPQ.symm (HasType.sort (by trivial))).defeq (domainProbe_typed hQ)
  have hF := HasType.forallE hP (HasType.sort (l := .succ .zero) (Γ := P :: Γ) (by trivial))
  have hΓF : OnCtx (F :: Γ) (env.IsType univs) := ⟨hΓ, _, hF⟩
  have hl : Lookup (F :: Γ) 0 (.forallE P.lift (.sort (.succ .zero))) := .zero
  have hf : env.HasType univs (F :: Γ) (.bvar 0) (.forallE P.lift (.sort (.succ .zero))) :=
    .bvar hl
  have HE := IsDefEq.eta hf
  have HC : ErasedCheckedComparison D 0 false (F :: Γ)
      (.lam P.lift (.app (VExpr.bvar 0).lift (.bvar 0))) (.bvar 0) := by
    rcases proofErase_lookup_eta_forward (Step := ErasedComparedKStage D 0) hΓF hl with E | H
    · unfold ErasedCheckedComparison
      rw [E]
      exact .base (.base .refl)
    · exact .base H.compare
  obtain ⟨stage, HR⟩ := H hΓ hF hx HE.hasType.1 hf HC
  have EL : (VExpr.lam P.lift (.app (VExpr.bvar 0).lift (.bvar 0))).inst (domainProbe Q) =
      .lam P (.app (domainProbe Q).lift (.bvar 0)) := by
    simp [VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN, liftVar, inst_liftN]
  have ER : (VExpr.bvar 0).inst (domainProbe Q) = domainProbe Q := by simp [VExpr.inst, VExpr.instVar]
  rw [EL, ER] at HR
  have hlong := IsDefEq.eta hx
  have hn := not_isProof_function_to_sort hΓ hlong.hasType.1
  change ¬ IsProof Γ (.lam P (.app (domainProbe Q).lift (.bvar 0))) at hn
  unfold ErasedCheckedComparison at HR ⊢
  rw [show proofErase Γ (.lam P (.app (domainProbe Q).lift (.bvar 0))) =
      .lam (proofErase Γ P) (proofErase (P :: Γ) (.app (domainProbe Q).lift (.bvar 0)))
      from if_neg hn, proofErase_domainProbe hΓ hQ] at HR
  exact ⟨stage, HR.lam_domains (erased_compared_K_stage_root stage)⟩

/-- Unrestricted typed instantiation, even at one binder and with a flexible
finite output stage, would prove the complete canonical-Eq proposition front. -/
theorem typedCheckedInstantiation_implies_propositionFront (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (H : TypedCheckedInstantiation D) : PropositionFront := by
  intro Γ Q P R hΓ hQ hP hR HE
  have hΓ' : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, hQ⟩
  have hP' : env.HasType univs (Q :: Γ) P.lift (.sort .zero) := hP.weak henv
  have hR' : env.HasType univs (Q :: Γ) R.lift (.sort .zero) := hR.weak henv
  obtain ⟨stage, HC⟩ := H.sort_coverage hΓ' hP' hR' (HE.of_l henv hΓ' hP')
  exact (HC.descendN heq hs hΓ hΓ' Ctx.LiftN.one hP hR).2
    rfl (not_isProof_of_sort hΓ hP)

end Lean4Lean.VEnv.Strengthening
