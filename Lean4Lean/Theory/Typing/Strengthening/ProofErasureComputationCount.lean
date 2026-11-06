import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveRuleDescent

/-! # Computation certificates with an outer primitive count

Beta computation has count zero; every primitive occurrence adds one. The
count ignores computations inside guards. Removing unused binders preserves
this count exactly when primitive descent returns one primitive per occurrence.
This is quantitative infrastructure, not a termination or confluence theorem.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private ProofShape.liftN_app_inv ProofShape.liftN_proj_inv ProofShape.liftN_lam_inv
  ProofShape.liftN_forallE_inv equality_simAt
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay

namespace ProofShape
/-- A compatible computation with exactly the displayed number of outer
primitive occurrences. Arbitrarily long beta paths have count zero, and no
count is imposed on primitive guard derivations. -/
inductive ScopedComputeCount (Step : List ProofShape → ProofShape → ProofShape → Prop) :
    Nat → List ProofShape → ProofShape → ProofShape → Prop where
  | base : Step Δ e out → ScopedComputeCount Step 1 Δ e out
  | beta : BetaRed e out → ScopedComputeCount Step 0 Δ e out
  | trans : ScopedComputeCount Step m Δ a b → ScopedComputeCount Step n Δ b c →
      ScopedComputeCount Step (m+n) Δ a c
  | app : ScopedComputeCount Step m Δ f f' → ScopedComputeCount Step n Δ a a' →
      ScopedComputeCount Step (m+n) Δ (.app f a) (.app f' a')
  | proj : ScopedComputeCount Step m Δ a a' → ScopedComputeCount Step m Δ (.proj s i a) (.proj s i a')
  | lam : ScopedComputeCount Step m Δ A A' → ScopedComputeCount Step n (A :: Δ) b b' →
      ScopedComputeCount Step (m+n) Δ (.lam A b) (.lam A' b')
  | forallE : ScopedComputeCount Step m Δ A A' → ScopedComputeCount Step n (A :: Δ) B B' →
      ScopedComputeCount Step (m+n) Δ (.forallE A B) (.forallE A' B')

/-- Forgetting the count gives the original computation relation. -/
theorem ScopedComputeCount.forget (H : ScopedComputeCount Step cost Δ a b) : ScopedCompute Step Δ a b := by
  induction H with
  | base H => exact .base H
  | beta H => exact .beta H
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | proj _ ih => exact .proj ih
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂

/-- Every finite computation has some outer primitive count. -/
theorem ScopedCompute.count (H : ScopedCompute Step Δ a b) : ∃ cost, ScopedComputeCount Step cost Δ a b := by
  induction H with
  | base H => exact ⟨1, .base H⟩
  | beta H => exact ⟨0, .beta H⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨m, H₁⟩ := ih₁; obtain ⟨n, H₂⟩ := ih₂
    exact ⟨m+n, .trans H₁ H₂⟩
  | app _ _ ih₁ ih₂ =>
    obtain ⟨m, H₁⟩ := ih₁; obtain ⟨n, H₂⟩ := ih₂
    exact ⟨m+n, .app H₁ H₂⟩
  | proj _ ih => obtain ⟨m, H⟩ := ih; exact ⟨m, .proj H⟩
  | lam _ _ ih₁ ih₂ =>
    obtain ⟨m, H₁⟩ := ih₁; obtain ⟨n, H₂⟩ := ih₂
    exact ⟨m+n, .lam H₁ H₂⟩
  | forallE _ _ ih₁ ih₂ =>
    obtain ⟨m, H₁⟩ := ih₁; obtain ⟨n, H₂⟩ := ih₂
    exact ⟨m+n, .forallE H₁ H₂⟩

/-- Inclusion of primitive relations preserves the exact occurrence count. -/
theorem ScopedComputeCount.mono
    (hstep : ∀ {Δ a b}, Step Δ a b → Target Δ a b)
    (H : ScopedComputeCount Step cost Δ a b) : ScopedComputeCount Target cost Δ a b := by
  induction H with
  | base H => exact .base (hstep H)
  | beta H => exact .beta H
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | proj _ ih => exact .proj ih
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂

/-- Count zero means that the entire computation is pure beta, including
under binders and projections. No normalization assertion is involved. -/
theorem ScopedComputeCount.zero_beta (H : ScopedComputeCount Step 0 Δ a b) : BetaRed a b := by
  generalize E : 0 = cost at H
  induction H with
  | base => omega
  | beta H => exact H
  | trans _ _ ih₁ ih₂ => exact (ih₁ (by omega)).trans (ih₂ (by omega))
  | app _ _ ih₁ ih₂ => exact .app (ih₁ (by omega)) (ih₂ (by omega))
  | proj _ ih => exact .proj (ih E)
  | lam _ _ ih₁ ih₂ => exact .lam (ih₁ (by omega)) (ih₂ (by omega))
  | forallE _ _ ih₁ ih₂ => exact .forallE (ih₁ (by omega)) (ih₂ (by omega))
end ProofShape

variable [Params]
/-- Removing any unused binder block preserves the exact outer primitive
count. Source-typed replay reconstructs each intermediate and changes binder
contexts without adding computational steps. Guard proof sizes are not counted. -/
theorem proofErase_scoped_compute_count_descend
    (hstep : ErasedScopedPrimitiveRuleDescent Step Target)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T)
    (hΔ : proofEraseCtx Γ' = Δ)
    (R : ProofShape.ScopedComputeCount Step cost Δ ((proofErase Γ e).liftN n k) out) :
    ∃ e', env.IsDefEq univs Γ e e' T ∧
      ProofShape.ScopedComputeCount Target cost (proofEraseCtx Γ) (proofErase Γ e) (proofErase Γ e') ∧
      (proofErase Γ e').liftN n k = out := by
  generalize hsrc : (proofErase Γ e).liftN n k = source at R
  induction R generalizing Γ Γ' k e T with
  | base R =>
    obtain ⟨e', HE, HR, Ee⟩ := hstep hΓ hΓ' W ht (hΔ ▸ hsrc ▸ R)
    exact ⟨e', HE, .base HR, Ee⟩
  | beta R =>
    rw [← hsrc, ← proofErase_liftN hΓ hΓ' W ht] at R
    obtain ⟨e', RR, HE⟩ := proofErase_beta_replay hΓ' (ht.weakN henv W) R
    rw [← lift'_consN_skipN] at RR
    obtain ⟨e₀, R₀, rfl⟩ := betaRed_lift_inv RR
    have HH := R₀.simAt henv.orderedStrong henv.betaSubjectReduction hΓ T ht
    rw [lift'_consN_skipN, proofErase_liftN hΓ hΓ' W HH.hasType.2] at HE
    exact ⟨e₀, HH, .beta (proofErase_beta_forward hΓ ht R₀), HE⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨e₁, H₁, R₁, E₁⟩ := ih1 hΓ hΓ' W ht hΔ hsrc
    obtain ⟨e₂, H₂, R₂, E₂⟩ := ih2 hΓ hΓ' W H₁.hasType.2 hΔ E₁
    exact ⟨e₂, H₁.trans H₂, R₁.trans R₂, E₂⟩
  | app _ _ ihf iha =>
    obtain ⟨_, _, hs, Hf, Ha⟩ := ProofShape.liftN_app_inv hsrc
    obtain ⟨f, a, rfl, hn, Ef, Ea⟩ := erase_app_inv hs
    rw [← Ef] at Hf
    rw [← Ea] at Ha
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    obtain ⟨f', HF, RF, EF⟩ := ihf hΓ hΓ' W hf hΔ Hf
    obtain ⟨a', HA, RA, EA⟩ := iha hΓ hΓ' W ha hΔ Ha
    have HH := SimAt.app henv.orderedStrong hΓ (equality_simAt hΓ HF) (equality_simAt hΓ HA) T ht
    refine ⟨_, HH, ?_, ?_⟩
    · simpa only [proofErase, if_neg hn, if_neg (mt (isProof_congr hΓ HH).2 hn)] using
        ProofShape.ScopedComputeCount.app RF RA
    simp only [proofErase, if_neg (mt (isProof_congr hΓ HH).2 hn), ProofShape.liftN, EF, EA]
  | proj _ ihm =>
    obtain ⟨_, hs, Hm⟩ := ProofShape.liftN_proj_inv hsrc
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv hs
    rw [← Em] at Hm
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨m', HM, RM, EM⟩ := ihm hΓ hΓ' W hm.hasType.2 hΔ Hm
    have HH := SimAt.proj henv.orderedStrong hΓ (equality_simAt hΓ HM) T ht
    refine ⟨_, HH, ?_, ?_⟩
    · simpa only [proofErase, if_neg hn, if_neg (mt (isProof_congr hΓ HH).2 hn)] using
        ProofShape.ScopedComputeCount.proj RM
    simp only [proofErase, if_neg (mt (isProof_congr hΓ HH).2 hn), ProofShape.liftN, EM]
  | lam _ _ ihA ihb =>
    obtain ⟨_, _, hs, HA, Hb⟩ := ProofShape.liftN_lam_inv hsrc
    obtain ⟨A, b, rfl, hn, EA, Eb⟩ := erase_lam_inv hs
    rw [← EA] at HA
    rw [← Eb] at Hb
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hΓA' : OnCtx (A.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hA.weakN henv W⟩
    obtain ⟨A', HAA, RAA, EAA⟩ := ihA hΓ hΓ' W hA hΔ HA
    obtain ⟨b', Hbb, Rbb, Ebb⟩ := ihb hΓA hΓA' W.succ hb
      (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA, hΔ, HA]) Hb
    have HH := SimAt.lam henv.orderedStrong hΓ (equality_simAt hΓ HAA)
      (fun _ => equality_simAt hΓA Hbb) T ht
    have Ebb' := proofErase_defeqCtx hΓA (.succ .zero HAA) Hbb.hasType.2
    refine ⟨_, HH, ?_, ?_⟩
    · simpa only [proofErase, if_neg hn, if_neg (mt (isProof_congr hΓ HH).2 hn), ← Ebb'] using
        ProofShape.ScopedComputeCount.lam RAA Rbb
    simp only [proofErase, if_neg (mt (isProof_congr hΓ HH).2 hn), ProofShape.liftN,
      EAA, ← Ebb', Ebb]
  | forallE _ _ ihA ihB =>
    obtain ⟨_, _, hs, HA, HB⟩ := ProofShape.liftN_forallE_inv hsrc
    obtain ⟨A, B, rfl, hn, EA, EB⟩ := erase_forallE_inv hs
    rw [← EA] at HA
    rw [← EB] at HB
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hΓA' : OnCtx (A.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hA.weakN henv W⟩
    obtain ⟨A', HAA, RAA, EAA⟩ := ihA hΓ hΓ' W hA hΔ HA
    obtain ⟨B', HBB, RBB, EBB⟩ := ihB hΓA hΓA' W.succ hB
      (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA, hΔ, HA]) HB
    have HH := SimAt.forallE henv.orderedStrong hΓ (equality_simAt hΓ HAA)
      (fun _ => equality_simAt hΓA HBB) T ht
    have EBB' := proofErase_defeqCtx hΓA (.succ .zero HAA) HBB.hasType.2
    refine ⟨_, HH, ?_, ?_⟩
    · simpa only [proofErase, if_neg hn, if_neg (mt (isProof_congr hΓ HH).2 hn), ← EBB'] using
        ProofShape.ScopedComputeCount.forallE RAA RBB
    simp only [proofErase, if_neg (mt (isProof_congr hΓ HH).2 hn), ProofShape.liftN,
      EAA, ← EBB', EBB]


/-- Full-union computations retain their exact primitive count below unused
binders. In particular descent cannot consume extra outer primitives. -/
theorem proofErase_static_structure_compute_count_descend
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T)
    (R : ProofShape.ScopedComputeCount (ErasedStaticStructureEtaExpansionUnion D) cost
      (proofEraseCtx Γ') ((proofErase Γ e).liftN n k) out) :
    ∃ e', env.IsDefEq univs Γ e e' T ∧
      ProofShape.ScopedComputeCount (ErasedStaticStructureEtaExpansionUnion D) cost
        (proofEraseCtx Γ) (proofErase Γ e) (proofErase Γ e') ∧
      (proofErase Γ e').liftN n k = out :=
  proofErase_scoped_compute_count_descend
    (erased_static_structure_eta_expansion_union_rule_descent heq hs) hΓ hΓ' W ht rfl R

end Lean4Lean.VEnv.Strengthening
