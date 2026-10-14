import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIota

/-! # Typed replay below binder insertion

An erased primitive may reconstruct an original by typed equality instead of a
syntactic pattern computation. Requiring this reconstruction below insertion is
enough for compatible closure and erased-join descent. This interface admits
proof-irrelevant constructor reconstruction once its primitive case is supplied.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives

namespace ProofShape
variable {e : ProofShape}
private theorem liftN_app_inv (H : e.liftN n k = .app f a) :
    ∃ f₀ a₀, e = .app f₀ a₀ ∧ f₀.liftN n k = f ∧ a₀.liftN n k = a := by
  cases e <;> simp_all [liftN]
  exact ⟨_, _, ⟨rfl, rfl⟩, H⟩

private theorem liftN_proj_inv (H : e.liftN n k = .proj s i m) :
    ∃ m₀, e = .proj s i m₀ ∧ m₀.liftN n k = m := by
  cases e <;> simp_all [liftN]

private theorem liftN_lam_inv (H : e.liftN n k = .lam A b) :
    ∃ A₀ b₀, e = .lam A₀ b₀ ∧ A₀.liftN n k = A ∧ b₀.liftN n (k+1) = b := by
  cases e <;> simp_all [liftN]
  exact ⟨_, _, ⟨rfl, rfl⟩, H⟩

private theorem liftN_forallE_inv (H : e.liftN n k = .forallE A B) :
    ∃ A₀ B₀, e = .forallE A₀ B₀ ∧ A₀.liftN n k = A ∧ B₀.liftN n (k+1) = B := by
  cases e <;> simp_all [liftN]
  exact ⟨_, _, ⟨rfl, rfl⟩, H⟩
end ProofShape

variable [Params]

/-- A primitive reconstructs a definitionally equal original below insertion,
with exactly the requested lifted erasure. This does not require a raw reduction
path to the reconstructed term or a scope premise for the erased target. -/
def ErasedPrimitiveDescent (Step : ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ Γ' n k e T out}, OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
    Ctx.LiftN n k Γ Γ' → env.HasType univs Γ e T →
    Step ((proofErase Γ e).liftN n k) out →
    ∃ e', env.IsDefEq univs Γ e e' T ∧ (proofErase Γ e').liftN n k = out

private theorem equality_simAt (hΓ : OnCtx Γ (env.IsType univs))
    (H : env.IsDefEq univs Γ e e' T) : env.SimAt univs Γ e e' :=
  fun _ ht => (show env.IsDefEqU univs Γ e e' from ⟨_, H⟩).of_l henv hΓ ht

/-- Earlier syntactic primitive replay supplies the new typed descent property.
The lifted original is replayed once, then the raw path is inverted and typed
below. No strengthening of the ambient equality is used. -/
theorem ErasedPrimitiveReplay.toDescent (hs : D.Sound env univs)
    (H : ErasedPrimitiveReplay D Step) : ErasedPrimitiveDescent Step := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht R
  rw [← proofErase_liftN hΓ hΓ' W ht] at R
  obtain ⟨e', RR, HE⟩ := H hΓ' (ht.weakN henv W) R
  rw [← lift'_consN_skipN] at RR
  obtain ⟨e₀, R₀, rfl⟩ := RR.lift_inv
  have HH := R₀.simAt hs hΓ T ht
  rw [lift'_consN_skipN, proofErase_liftN hΓ hΓ' W HH.hasType.2] at HE
  exact ⟨e₀, HH, HE⟩

/-- Compatible erased computation preserves typed primitive descent. Original
representatives and their typings are reconstructed below at every intermediate
node, including nodes under changed binder annotations. -/
theorem proofErase_compute_typed_descend (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T)
    (R : ProofShape.Compute Step ((proofErase Γ e).liftN n k) out) :
    ∃ e', env.IsDefEq univs Γ e e' T ∧ (proofErase Γ e').liftN n k = out := by
  generalize hsrc : (proofErase Γ e).liftN n k = source at R
  induction R generalizing Γ Γ' k e T with
  | base R => exact hstep hΓ hΓ' W ht (hsrc ▸ R)
  | beta R =>
    rw [← hsrc, ← proofErase_liftN hΓ hΓ' W ht] at R
    obtain ⟨e', RR, HE⟩ := proofErase_beta_replay hΓ' (ht.weakN henv W) R
    rw [← lift'_consN_skipN] at RR
    obtain ⟨e₀, R₀, rfl⟩ := betaRed_lift_inv RR
    have HH := R₀.simAt henv.orderedStrong henv.betaSubjectReduction hΓ T ht
    rw [lift'_consN_skipN, proofErase_liftN hΓ hΓ' W HH.hasType.2] at HE
    exact ⟨e₀, HH, HE⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨e₁, H₁, E₁⟩ := ih1 hΓ hΓ' W ht hsrc
    obtain ⟨e₂, H₂, E₂⟩ := ih2 hΓ hΓ' W H₁.hasType.2 E₁
    exact ⟨e₂, H₁.trans H₂, E₂⟩
  | app _ _ ihf iha =>
    obtain ⟨_, _, hs, Hf, Ha⟩ := ProofShape.liftN_app_inv hsrc
    obtain ⟨f, a, rfl, hn, Ef, Ea⟩ := erase_app_inv hs
    rw [← Ef] at Hf
    rw [← Ea] at Ha
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    obtain ⟨f', HF, EF⟩ := ihf hΓ hΓ' W hf Hf
    obtain ⟨a', HA, EA⟩ := iha hΓ hΓ' W ha Ha
    have HH := SimAt.app henv.orderedStrong hΓ (equality_simAt hΓ HF) (equality_simAt hΓ HA) T ht
    refine ⟨_, HH, ?_⟩
    simp only [proofErase, if_neg (mt (isProof_congr hΓ HH).2 hn), ProofShape.liftN, EF, EA]
  | proj _ ihm =>
    obtain ⟨_, hs, Hm⟩ := ProofShape.liftN_proj_inv hsrc
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv hs
    rw [← Em] at Hm
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨m', HM, EM⟩ := ihm hΓ hΓ' W hm.hasType.2 Hm
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
    obtain ⟨A', HAA, EAA⟩ := ihA hΓ hΓ' W hA HA
    obtain ⟨b', Hbb, Ebb⟩ := ihb hΓA hΓA' W.succ hb Hb
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
    obtain ⟨A', HAA, EAA⟩ := ihA hΓ hΓ' W hA HA
    obtain ⟨B', HBB, EBB⟩ := ihB hΓA hΓA' W.succ hB HB
    have HH := SimAt.forallE henv.orderedStrong hΓ (equality_simAt hΓ HAA)
      (fun _ => equality_simAt hΓA HBB) T ht
    have EBB' := proofErase_defeqCtx hΓA (.succ .zero HAA) HBB.hasType.2
    refine ⟨_, HH, ?_⟩
    simp only [proofErase, if_neg (mt (isProof_congr hΓ HH).2 hn), ProofShape.liftN,
      EAA, ← EBB', EBB]

/-- Two finite paths satisfying typed primitive descent reflect to an equality
below insertion, even if reconstructed intermediates use proof irrelevance. -/
theorem proofErase_typed_join_descend (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (Ra : ProofShape.Compute Step ((proofErase Γ a).liftN n k) out)
    (Rb : ProofShape.Compute Step ((proofErase Γ b).liftN n k) out) :
    env.IsDefEq univs Γ a b T := by
  obtain ⟨a', HA, EA⟩ := proofErase_compute_typed_descend hstep hΓ hΓ' W ha Ra
  obtain ⟨b', HB, EB⟩ := proofErase_compute_typed_descend hstep hΓ hΓ' W hb Rb
  have HE := ProofShape.liftN_inj.1 (EA.trans EB.symm)
  obtain ⟨_, hT⟩ := ha.isType henv hΓ
  obtain ⟨_, HC⟩ := (proofErase_reflect hΓ HA.hasType.2 HB.hasType.2 HE).1 ⟨_, hT⟩
  exact HA.trans (((HC.defeq hΓ).of_l henv hΓ HA.hasType.2).trans HB.symm)

end Lean4Lean.VEnv.Strengthening
