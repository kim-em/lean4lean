import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProbe
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRetraction
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEta
import Lean4Lean.Theory.Typing.Strengthening.ReannotationBarrier

/-! # Typed eta/beta composition already implies the proposition front

Requiring a common original type for the intermediate avoids the empty-structure
counterexample to raw transitivity. It does not give a smaller sufficient front:
even transporting a stage-zero comparison across a beta reduction, allowing any
finite output stage, would imply PropositionFront. Constant-body lambda probes
retain the domain conversion encoded by eta expansion followed by beta.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Constant-body probes retain exactly the erased domain and the sort body. -/
theorem proofErase_domainProbe (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) :
    proofErase Γ (domainProbe A) = .lam (proofErase Γ A) (.sort .zero) := by
  have hn := not_isProof_function_to_sort hΓ (domainProbe_typed hA)
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hs := not_isProof_of_sort hΓA (HasType.sort (l := .zero) (by trivial))
  change ¬ IsProof Γ (.lam A (.sort .zero)) at hn
  simp only [domainProbe, proofErase, if_neg hn, if_neg hs]

/-- The missing typed forward-transport rule, restricted to stage-zero input
comparison and beta computation on its right endpoint. All three original terms
share a type. Even with an arbitrary finite output stage this implies the full
proposition front, as proved below; it is not a smaller candidate obligation. -/
def TypedErasedBetaTransport (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ a b c T}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ a T → env.HasType univs Γ b T → env.HasType univs Γ c T →
    ProofShape.Compare (ErasedComparedKStage D 0) true (proofErase Γ a) (proofErase Γ b) →
    ProofShape.BetaRed (proofErase Γ b) (proofErase Γ c) →
    ∃ stage, ProofShape.Compare (ErasedComparedKStage D stage) true (proofErase Γ a) (proofErase Γ c)

/-- A proposed composition rule with a commonly typed original intermediate and
unrestricted finite output stage. Its missing case includes typed beta transport,
so the theorem below shows that it retains the entire proposition front. -/
def TypedErasedComposition (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ a b c T i j}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ a T → env.HasType univs Γ b T → env.HasType univs Γ c T →
    ProofShape.Compare (ErasedComparedKStage D i) true (proofErase Γ a) (proofErase Γ b) →
    ProofShape.Compare (ErasedComparedKStage D j) true (proofErase Γ b) (proofErase Γ c) →
    ∃ stage, ProofShape.Compare (ErasedComparedKStage D stage) true (proofErase Γ a) (proofErase Γ c)

/-- General typed composition includes the particular eta/beta transport case. -/
theorem TypedErasedComposition.betaTransport (H : TypedErasedComposition D) : TypedErasedBetaTransport D := by
  intro Γ a b c T hΓ ha hb hc HC HB
  exact H hΓ ha hb hc HC (j := 0) (.compute (.beta HB) .refl .refl)

/-- Every original domain conversion supplies an eta comparison followed by beta
between the two probes, with a commonly typed original intermediate. Neither
input certificate contains a comparison of the domains. -/
theorem domainProbe_typed_eta_beta (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort u)) (hQ : env.HasType univs Γ Q (.sort u))
    (HPQ : env.IsDefEq univs Γ P Q (.sort u)) :
    ∃ mid T,
      env.HasType univs Γ (domainProbe P) T ∧
      env.HasType univs Γ mid T ∧ env.HasType univs Γ (domainProbe Q) T ∧
      ProofShape.Compare Step true (proofErase Γ (domainProbe P)) (proofErase Γ mid) ∧
      ProofShape.BetaRed (proofErase Γ mid) (proofErase Γ (domainProbe Q)) := by
  have hf : env.HasType univs Γ (domainProbe P) (.forallE Q (.sort (.succ .zero))) :=
    (IsDefEq.forallEDF HPQ (HasType.sort (by trivial))).defeq (domainProbe_typed hP)
  have Heta := IsDefEq.eta hf
  refine ⟨_, _, hf, Heta.hasType.1, domainProbe_typed hQ, ?_, ?_⟩
  · rcases proofErase_eta_forward hΓ hf with H | H
    · rw [H]
      exact .refl
    · exact .etaR H
  · apply proofErase_beta_forward hΓ Heta.hasType.1
    change VExpr.BetaRed (.lam Q (.app (.lam P.lift (.sort .zero)) (.bvar 0)))
      (.lam Q (.sort .zero))
    exact .lam .refl .beta

/-- Typed forward beta transport would give finite inferred certificates for
every definitional equality between sort-typed domains. -/
theorem TypedErasedBetaTransport.sort_coverage (H : TypedErasedBetaTransport D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort u)) (hQ : env.HasType univs Γ Q (.sort u))
    (HPQ : env.IsDefEq univs Γ P Q (.sort u)) :
    ∃ stage, ProofShape.Compare (ErasedComparedKStage D stage) false (proofErase Γ P) (proofErase Γ Q) := by
  obtain ⟨mid, T, hf, hm, hg, HC, HB⟩ :=
    domainProbe_typed_eta_beta (Step := ErasedComparedKStage D 0) hΓ hP hQ HPQ
  obtain ⟨stage, HE⟩ := H hΓ hf hm hg HC HB
  rw [proofErase_domainProbe hΓ hP, proofErase_domainProbe hΓ hQ] at HE
  exact ⟨stage, HE.probe_inv (erased_compared_K_stage_root stage)⟩

/-- Typed eta/beta composition still entails the original proposition front.
The intermediate is commonly typed above the removed binder; finite certificate
extraction and raw retraction would then reflect the two proposition domains. -/
theorem typedErasedBetaTransport_implies_propositionFront (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (H : TypedErasedBetaTransport D) : PropositionFront := by
  intro Γ Q P R hΓ hQ hP hR HE
  have hΓ' : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, hQ⟩
  have hP' : env.HasType univs (Q :: Γ) P.lift (.sort .zero) := hP.weak henv
  have hR' : env.HasType univs (Q :: Γ) R.lift (.sort .zero) := hR.weak henv
  obtain ⟨stage, HC⟩ := H.sort_coverage hΓ' hP' hR' (HE.of_l henv hΓ' hP')
  have HC' : ProofShape.Compare (ErasedComparedKStage D stage) false
      (proofErase (Q :: Γ) (P.lift' (.skip .refl)))
      (proofErase (Q :: Γ) (R.lift' (.skip .refl))) := by
    simpa only [← lift_eq_lift'] using HC
  exact (proofErase_compared_K_thinning heq hs hΓ hΓ' (.skip .refl) hP hR HC').2
    rfl (not_isProof_of_sort hΓ hP)

/-- Supplying the intermediate's common typing avoids the raw counterexample,
but proving finite typed composition would still prove PropositionFront. -/
theorem typedErasedComposition_implies_propositionFront (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (H : TypedErasedComposition D) : PropositionFront :=
  typedErasedBetaTransport_implies_propositionFront heq hs H.betaTransport

end Lean4Lean.VEnv.Strengthening
