import Lean4Lean.Theory.Typing.Strengthening.BidirectionalComposition
import Lean4Lean.Theory.Typing.Strengthening.BidirectionalCertificateDescent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedCompositionBarrier
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRawChecking

/-! # Common normal composition still contains the proposition front

Common-mode lambda checking removes the direct probe obstruction, but composing
that comparison with eta expansion exposes the domains in function position.
Without beta completion, common normal composition would imply full-front
coverage and is actually false on a beta-expanded sort domain. This does not refute the newer erased checking relation, which can
compute the expanded body before checking.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A sort source in bidirectional normal comparison has a literal sort target.
There is no beta contraction hidden in the normal certificate. -/
theorem BiNormal.sort_right_shape (hΓ : OnCtx Γ (env.IsType univs))
    (H : BiNormal mode n Γ (.sort u) e) : ∃ v, e = .sort v := by
  generalize E : VExpr.sort u = a at H
  induction H with
  | refl => exact ⟨_, E.symm⟩
  | sortDF => exact ⟨_, rfl⟩
  | etaR hf _ | etaBoth hf _ _ =>
    cases E
    exact (((HasType.sort (HasType.sort_inv henv.ordered hf)).uniqU henv hΓ hf).sort_forallE_inv henv hΓ).elim
  | proofIrrel hP ha hb =>
    cases E
    exact (not_isProof_of_sort hΓ (HasType.sort (HasType.sort_inv henv.ordered ha)) ⟨_, ha, hP⟩).elim
  | promote _ ih => exact ih hΓ E
  | constDF | appDF | projDF | lamIndependent | lamCommon | forallEDF | etaL => cases E

/-- Inferred lambda comparison retains a common-mode certificate of its domains.
The source's non-proof premise excludes proof irrelevance at the whole lambda. -/
theorem BiNormal.lambda_inferred_domains (hA : env.HasType univs Γ A (.sort u))
    (hn : ¬ IsProof Γ (.lam A b))
    (H : BiNormal false n Γ (.lam A b) (.lam A' b')) :
    ∃ k, BiNormal true k Γ A A' := by
  cases H with
  | refl => exact ⟨0, .refl hA⟩
  | lamIndependent _ HD _ => exact ⟨_, HD⟩
  | proofIrrel hP ha _ => exact (hn ⟨_, ha, hP⟩).elim

/-- Comparing a constant-body probe to another probe's eta expansion normally
forces domain comparison, despite the available common-mode lambda rule. -/
theorem BiNormal.probe_eta_domains (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort u)) (hQ : env.HasType univs Γ Q (.sort v))
    (H : BiNormal true n Γ (domainProbe P)
      (.lam Q (.app (domainProbe Q).lift (.bvar 0)))) :
    ∃ k, BiNormal true k Γ P Q := by
  have hn := not_isProof_function_to_sort hΓ (domainProbe_typed hP)
  have HQ := IsDefEq.eta (domainProbe_typed hQ)
  have HPQ := (H.defeq hΓ).trans henv hΓ ⟨_, HQ⟩
  unfold domainProbe at H hn
  cases H with
  | lamCommon hA _ HB =>
    have hctx : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, hA.hasType.1⟩
    obtain ⟨_, E⟩ := HB.sort_right_shape hctx
    cases E
  | etaL hf HB =>
    obtain ⟨⟨_, hA⟩, _⟩ := (hf.isType henv hΓ).forallE_inv henv
    have hctx : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
    obtain ⟨_, E⟩ := HB.sort_right_shape hctx
    cases E
  | etaR hf HB =>
    have hg := (HPQ.of_l henv hΓ hf).hasType.2
    obtain ⟨k, _, HK⟩ := BiNormal.etaBoth_inferred hΓ hf hg hn HB
    exact HK.lambda_inferred_domains hP hn
  | etaBoth hf hg HB =>
    obtain ⟨k, _, HK⟩ := BiNormal.etaBoth_inferred hΓ hf hg hn HB
    exact HK.lambda_inferred_domains hP hn
  | proofIrrel hP ha _ => exact (hn ⟨_, ha, hP⟩).elim
  | promote H => exact H.lambda_inferred_domains hP hn

/-- Common-mode composition would provide normal certificates for arbitrary
sort-typed domain conversion. Its two inputs are common lambda checking followed
by one actual eta expansion, with fully typed original endpoints. -/
theorem BiCommonComposition.sort_coverage (H : BiCommonComposition)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort u)) (hQ : env.HasType univs Γ Q (.sort u))
    (HPQ : env.IsDefEq univs Γ P Q (.sort u)) :
    ∃ k, BiNormal true k Γ P Q := by
  have H1 : BiNormal true 1 Γ (domainProbe P) (domainProbe Q) :=
    .lamCommon hP HPQ (.refl (HasType.sort (by trivial)))
  have hf := domainProbe_typed hQ
  have hb : env.HasType univs (Q :: Γ) (.app (domainProbe Q).lift (.bvar 0))
      (.sort (.succ .zero)) := by
    simpa only [lift, liftN, inst_liftN_bvar, inst] using HasType.app (hf.weak henv (B := Q)) (.bvar .zero)
  have H2 : BiNormal true 2 Γ (domainProbe Q)
      (.lam Q (.app (domainProbe Q).lift (.bvar 0))) := .etaR hf (.refl hb)
  obtain ⟨_, HC⟩ := H hΓ H1 H2
  exact HC.probe_eta_domains hΓ hP hQ

/-- Normal common-mode composition is at least as strong as PropositionFront.
The reduction needs no canonical-Eq assumption and no normalization theorem. -/
theorem biCommonComposition_implies_propositionFront (H : BiCommonComposition) :
    PropositionFront := by
  intro Γ Q P R hΓ hQ hP hR HE
  have hΓ' : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, hQ⟩
  have hP' : env.HasType univs (Q :: Γ) P.lift (.sort .zero) := hP.weak henv
  have hR' : env.HasType univs (Q :: Γ) R.lift (.sort .zero) := hR.weak henv
  obtain ⟨n, HC⟩ := H.sort_coverage hΓ' hP' hR' (HE.of_l henv hΓ' hP')
  have HC' : BiNormal true n (Q :: Γ) (P.lift' (.skip .refl)) (R.lift' (.skip .refl)) := by
    simpa only [← lift_eq_lift'] using HC
  exact BiNormal.descend n (Ctx.Lift'.skip .refl) hΓ hΓ' hP hR HC' ⟨_, HasType.sort (by trivial)⟩

/-- Common normal composition is in fact false in every well-formed Params
environment. A sort and a beta-expanded copy give convertible probe domains,
but the forced normal domain certificate would have a sort source and app target. -/
theorem not_biCommonComposition : ¬ BiCommonComposition := by
  intro H
  have hΓ : OnCtx [] (env.IsType univs) := by trivial
  have hP : env.HasType univs [] (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hβ : env.IsDefEq univs []
      (.app (.lam (.sort (.succ .zero)) (.sort .zero)) (.sort .zero))
      (.sort .zero) (.sort (.succ .zero)) := by
    simpa only [inst] using IsDefEq.beta
      (HasType.sort (env := env) (Γ := [.sort (.succ .zero)]) (l := .zero) (by trivial)) hP
  obtain ⟨_, HC⟩ := H.sort_coverage hΓ hP hβ.hasType.1 hβ.symm
  obtain ⟨_, E⟩ := HC.sort_right_shape hΓ
  cases E

/-- Beta completion repairs the exact obstructing probe/eta pair in the raw
checking relation. No comparison or conversion of the domains is required. -/
theorem rawChecked_probe_eta (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort u)) (hQ : env.HasType univs Γ Q (.sort v)) :
    ProofShape.RawCheckedCompare Step true (proofErase Γ (domainProbe P))
      (proofErase Γ (.lam Q (.app (domainProbe Q).lift (.bvar 0)))) := by
  have Heta := IsDefEq.eta (domainProbe_typed hQ)
  have RB : VExpr.BetaRed (.lam Q (.app (domainProbe Q).lift (.bvar 0))) (domainProbe Q) :=
    .lam .refl .beta
  apply ProofShape.RawCheckedCompare.compute .refl
    (.beta (proofErase_beta_forward hΓ Heta.hasType.1 RB))
  rw [proofErase_domainProbe hΓ hP, proofErase_domainProbe hΓ hQ]
  exact .lamCommon (.base .refl)

/-- A concrete common-typed nontransitivity witness for normal comparison,
together with its direct repair by computation-aware raw checking. This works
in every Params environment and uses neither declarations nor canonical Eq. -/
theorem bidirectional_typed_nontransitivity :
    ∃ a b c T, env.HasType univs [] a T ∧ env.HasType univs [] b T ∧
      env.HasType univs [] c T ∧ BiNormal true 1 [] a b ∧ BiNormal true 2 [] b c ∧
      (∀ n, ¬ BiNormal true n [] a c) ∧
      ProofShape.RawCheckedCompare Step true (proofErase [] a) (proofErase [] c) := by
  have hΓ : OnCtx [] (env.IsType univs) := by trivial
  have hP : env.HasType univs [] (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hβ : env.IsDefEq univs []
      (.app (.lam (.sort (.succ .zero)) (.sort .zero)) (.sort .zero))
      (.sort .zero) (.sort (.succ .zero)) := by
    simpa only [inst] using IsDefEq.beta
      (HasType.sort (env := env) (Γ := [.sort (.succ .zero)]) (l := .zero) (by trivial)) hP
  let Q := VExpr.app (.lam (.sort (.succ .zero)) (.sort .zero)) (.sort .zero)
  have hQ : env.HasType univs [] Q (.sort (.succ .zero)) := hβ.hasType.1
  have hb := domainProbe_typed hQ
  have ha : env.HasType univs [] (domainProbe (.sort .zero))
      (.forallE Q (.sort (.succ .zero))) :=
    (IsDefEq.forallEDF hβ.symm (HasType.sort (by trivial))).defeq (domainProbe_typed hP)
  have hη := IsDefEq.eta hb
  have hbody : env.HasType univs [Q] (.app (domainProbe Q).lift (.bvar 0))
      (.sort (.succ .zero)) := by
    simpa only [lift, liftN, inst_liftN_bvar, inst] using HasType.app (hb.weak henv (B := Q)) (.bvar .zero)
  refine ⟨_, _, _, _, ha, hb, hη.hasType.1,
    .lamCommon hP hβ.symm (.refl (HasType.sort (by trivial))), .etaR hb (.refl hbody), ?_,
    rawChecked_probe_eta hΓ hP hQ⟩
  intro n H
  obtain ⟨_, HD⟩ := H.probe_eta_domains hΓ hP hQ
  obtain ⟨_, E⟩ := HD.sort_right_shape hΓ
  unfold Q at E
  cases E

end Lean4Lean.VEnv.Strengthening
