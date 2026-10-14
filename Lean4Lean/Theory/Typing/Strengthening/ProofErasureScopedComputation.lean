import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextSubstitution

/-! # Erased computation indexed by its ambient context

Recursive eta guards carry contextual sort witnesses. This compatible closure
keeps the ambient erased context at each primitive occurrence and extends it by
the source domain beneath binders. Typed descent reconstructs all intermediates.
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
/-- Compatible finite computation retaining each primitive's ambient context.
Binder bodies use the source annotation, even when that annotation computes. -/
inductive ScopedCompute (Step : List ProofShape → ProofShape → ProofShape → Prop) :
    List ProofShape → ProofShape → ProofShape → Prop where
  | base : Step Δ e out → ScopedCompute Step Δ e out
  | beta : BetaRed e out → ScopedCompute Step Δ e out
  | trans : ScopedCompute Step Δ a b → ScopedCompute Step Δ b c → ScopedCompute Step Δ a c
  | app : ScopedCompute Step Δ f f' → ScopedCompute Step Δ a a' →
      ScopedCompute Step Δ (.app f a) (.app f' a')
  | proj : ScopedCompute Step Δ m m' → ScopedCompute Step Δ (.proj s i m) (.proj s i m')
  | lam : ScopedCompute Step Δ A A' → ScopedCompute Step (A :: Δ) b b' →
      ScopedCompute Step Δ (.lam A b) (.lam A' b')
  | forallE : ScopedCompute Step Δ A A' → ScopedCompute Step (A :: Δ) B B' →
      ScopedCompute Step Δ (.forallE A B) (.forallE A' B')

/-- Empty computation is available at every raw context. -/
theorem ScopedCompute.refl : ScopedCompute Step Δ e e := .beta .refl

/-- Context-indexed primitive inclusion lifts through compatible computation. -/
theorem ScopedCompute.mono (hstep : ∀ {Δ a b}, Step Δ a b → Step' Δ a b)
    (H : ScopedCompute Step Δ a b) : ScopedCompute Step' Δ a b := by
  induction H with
  | base H => exact .base (hstep H)
  | beta H => exact .beta H
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | proj _ ih => exact .proj ih
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂
end ProofShape

variable [Params]
/-- A contextual primitive reconstructs an equal original below insertion.
Its context is the actual ambient erasure, not an existential unrelated context. -/
def ErasedScopedPrimitiveDescent (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ Γ' n k e T out}, OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
    Ctx.LiftN n k Γ Γ' → env.HasType univs Γ e T →
    Step (proofEraseCtx Γ') ((proofErase Γ e).liftN n k) out →
    ∃ e', env.IsDefEq univs Γ e e' T ∧ (proofErase Γ e').liftN n k = out

/-- Compatible context-indexed computation descends through arbitrary binder
insertion. Domain conversion preserves the reconstructed body's exact erasure. -/
theorem proofErase_scoped_compute_descend (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T)
    (hΔ : proofEraseCtx Γ' = Δ)
    (R : ProofShape.ScopedCompute Step Δ ((proofErase Γ e).liftN n k) out) :
    ∃ e', env.IsDefEq univs Γ e e' T ∧ (proofErase Γ e').liftN n k = out := by
  generalize hsrc : (proofErase Γ e).liftN n k = source at R
  induction R generalizing Γ Γ' k e T with
  | base R => exact hstep hΓ hΓ' W ht (hΔ ▸ hsrc ▸ R)
  | beta R =>
    rw [← hsrc, ← proofErase_liftN hΓ hΓ' W ht] at R
    obtain ⟨e', RR, HE⟩ := proofErase_beta_replay hΓ' (ht.weakN henv W) R
    rw [← lift'_consN_skipN] at RR
    obtain ⟨e₀, R₀, rfl⟩ := betaRed_lift_inv RR
    have HH := R₀.simAt henv.orderedStrong henv.betaSubjectReduction hΓ T ht
    rw [lift'_consN_skipN, proofErase_liftN hΓ hΓ' W HH.hasType.2] at HE
    exact ⟨e₀, HH, HE⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨e₁, H₁, E₁⟩ := ih1 hΓ hΓ' W ht hΔ hsrc
    obtain ⟨e₂, H₂, E₂⟩ := ih2 hΓ hΓ' W H₁.hasType.2 hΔ E₁
    exact ⟨e₂, H₁.trans H₂, E₂⟩
  | app _ _ ihf iha =>
    obtain ⟨_, _, hs, Hf, Ha⟩ := ProofShape.liftN_app_inv hsrc
    obtain ⟨f, a, rfl, hn, Ef, Ea⟩ := erase_app_inv hs
    rw [← Ef] at Hf
    rw [← Ea] at Ha
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    obtain ⟨f', HF, EF⟩ := ihf hΓ hΓ' W hf hΔ Hf
    obtain ⟨a', HA, EA⟩ := iha hΓ hΓ' W ha hΔ Ha
    have HH := SimAt.app henv.orderedStrong hΓ (equality_simAt hΓ HF) (equality_simAt hΓ HA) T ht
    refine ⟨_, HH, ?_⟩
    simp only [proofErase, if_neg (mt (isProof_congr hΓ HH).2 hn), ProofShape.liftN, EF, EA]
  | proj _ ihm =>
    obtain ⟨_, hs, Hm⟩ := ProofShape.liftN_proj_inv hsrc
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv hs
    rw [← Em] at Hm
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨m', HM, EM⟩ := ihm hΓ hΓ' W hm.hasType.2 hΔ Hm
    have HH := SimAt.proj henv.orderedStrong hΓ (equality_simAt hΓ HM) T ht
    refine ⟨_, HH, ?_⟩
    simp only [proofErase, if_neg (mt (isProof_congr hΓ HH).2 hn), ProofShape.liftN, EM]
  | lam _ _ ihA ihb =>
    obtain ⟨_, _, hs, HA, Hb⟩ := ProofShape.liftN_lam_inv hsrc
    obtain ⟨A, b, rfl, hn, EA, Eb⟩ := erase_lam_inv hs
    rw [← EA] at HA
    rw [← Eb] at Hb
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hΓA' : OnCtx (A.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hA.weakN henv W⟩
    obtain ⟨A', HAA, EAA⟩ := ihA hΓ hΓ' W hA hΔ HA
    obtain ⟨b', Hbb, Ebb⟩ := ihb hΓA hΓA' W.succ hb
      (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA, hΔ, HA]) Hb
    have HH := SimAt.lam henv.orderedStrong hΓ (equality_simAt hΓ HAA)
      (fun _ => equality_simAt hΓA Hbb) T ht
    have Ebb' := proofErase_defeqCtx hΓA (.succ .zero HAA) Hbb.hasType.2
    refine ⟨_, HH, ?_⟩
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
    obtain ⟨A', HAA, EAA⟩ := ihA hΓ hΓ' W hA hΔ HA
    obtain ⟨B', HBB, EBB⟩ := ihB hΓA hΓA' W.succ hB
      (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA, hΔ, HA]) HB
    have HH := SimAt.forallE henv.orderedStrong hΓ (equality_simAt hΓ HAA)
      (fun _ => equality_simAt hΓA HBB) T ht
    have EBB' := proofErase_defeqCtx hΓA (.succ .zero HAA) HBB.hasType.2
    refine ⟨_, HH, ?_⟩
    simp only [proofErase, if_neg (mt (isProof_congr hΓ HH).2 hn), ProofShape.liftN,
      EAA, ← EBB', EBB]


end Lean4Lean.VEnv.Strengthening
