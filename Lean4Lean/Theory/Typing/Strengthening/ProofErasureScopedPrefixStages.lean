import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrefixOnly

/-! # Finite prefix computation guarded by recursive contextual comparison

The stage index decreases in every guard. Contextual sort witnesses are kept
at their actual ambient contexts and substitute along typed interpretations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Direct reflection of a scoped certificate is descent with zero insertion. -/
theorem proofErase_scoped_compare_reflect (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.ScopedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → ¬ IsProof Γ b → env.IsDefEqU univs Γ a b) := by
  exact proofErase_scoped_compare_descend hstep hΓ hΓ (.zero []) rfl ha hb
    (by simpa only [List.length_nil, ProofShape.liftN_zero] using H)

namespace ProofShape
/-- Recursive contextual endpoint comparison enables the proof-major prefix.
The guard and source share the same erased ambient context. -/
inductive ScopedPrefixKPrimitive
    (Step : List ProofShape → ProofShape → ProofShape → Prop) (Δ : List ProofShape) :
    ProofShape → ProofShape → Prop where
  | intro : ScopedCompare Step Δ true a b →
      ScopedPrefixKPrimitive Step Δ (eqRecBeforeMajor v w α a M m b)
        (.lam (eqProofType w α a b) (m.liftN 1))

/-- Typed context substitution transports both the guard and exact prefix output. -/
theorem ScopedPrefixKPrimitive.subst
    (hstep : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (H : ScopedPrefixKPrimitive Step Δ e out) (W : ContextSubstitution Δ Δ' τ) :
    ScopedPrefixKPrimitive Step Δ' (e.subst τ) (out.subst τ) := by
  cases H with
  | intro HC =>
    simpa only [eqRecBeforeMajor, eqProofType, ProofShape.subst, lift_subst_lift] using
      (ScopedPrefixKPrimitive.intro (v := _) (w := _) (α := _) (M := _) (m := _)
        (HC.subst hstep W))
end ProofShape

/-- Prefix K descends from a typed source. The exact lower proof domain is
recovered from that source, so the new lambda is not an arbitrary eta annotation. -/
theorem erased_scoped_prefix_K_descent
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveDescent Step) :
    ErasedScopedPrimitiveDescent (ProofShape.ScopedPrefixKPrimitive Step) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht R
  generalize hsrc : (proofErase Γ e).liftN n k = source at R
  cases R with
  | @intro a b v w α M m HC =>
    obtain ⟨αs, as, Ms, ms, bs, E, Eα, Ea, EM, Em, Eb⟩ :=
      ProofShape.liftN_eqRecBeforeMajor_inv hsrc
    obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Hα, Ha, HM, Hm, Hb⟩ := proofErase_eqRecBeforeMajor_inv E
    rw [← Hα] at Eα
    rw [← Ha] at Ea
    rw [← HM] at EM
    rw [← Hm] at Em
    rw [← Hb] at Eb
    rw [← Ea, ← Eb] at HC
    obtain ⟨_, hw, hα, ha, _, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
    have hab := (proofErase_scoped_compare_descend hstep hΓ hΓ' W rfl ha hb HC).1 ⟨_, hα⟩
    have HH := eqRecBeforeMajor_simAt henv heq hΓ hab T ht
    have hn : ¬ IsProof Γ (eqRecBeforeMajor v w α₀ a₀ M₀ m₀ b₀) := by
      intro hp
      rw [proofErase_eq_proof.2 hp] at E
      cases E
    have hn' := mt (isProof_congr hΓ HH).2 hn
    have hE := HasType.eqApp heq hw hα ha hb
    have hΓE : OnCtx (eqApp w α₀ a₀ b₀ :: Γ) (env.IsType univs) := ⟨hΓ, _, hE⟩
    refine ⟨_, HH, ?_⟩
    rw [show proofErase Γ (.lam (eqApp w α₀ a₀ b₀) m₀.lift) =
      .lam (proofErase Γ (eqApp w α₀ a₀ b₀)) (proofErase (eqApp w α₀ a₀ b₀ :: Γ) m₀.lift) from if_neg hn',
      proofErase_eqProofType heq hw hΓ hα ha hb,
      proofErase_liftN hΓ hΓE Ctx.LiftN.one hm]
    simp only [ProofShape.liftN, ProofShape.eqProofType,
      ← ProofShape.liftN_comm _ n 1 k 0 (Nat.zero_le _), Eα, Ea, Eb, Em]

/-- A typed prefix with a raw endpoint checking certificate computes to its
canonical lambda in the new primitive relation. Whole-proof sources collapse
to identity; non-proof sources retain the source-derived domain and payload. -/
theorem proofErase_scoped_prefix_K_forward
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (HC : ProofShape.ScopedCompare Step (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompute (ProofShape.ScopedPrefixKPrimitive Step) (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) := by
  obtain ⟨_, hw, hα, ha, _, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have hab := (proofErase_scoped_compare_reflect hstep hΓ ha hb HC).1 ⟨_, hα⟩
  have HH := eqRecBeforeMajor_simAt henv heq hΓ hab T ht
  by_cases hp : IsProof Γ (eqRecBeforeMajor v w α a M m b)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HH).1 hp)]
    exact .refl
  · have hp' := mt (isProof_congr hΓ HH).2 hp
    have HE := proofErase_const_spine hΓ (args := [α, a, M, m, b]) ht hp
    change proofErase Γ (eqRecBeforeMajor v w α a M m b) = _ at HE
    have hE := HasType.eqApp heq hw hα ha hb
    have hΓE : OnCtx (eqApp w α a b :: Γ) (env.IsType univs) := ⟨hΓ, _, hE⟩
    rw [HE, show proofErase Γ (.lam (eqApp w α a b) m.lift) =
      .lam (proofErase Γ (eqApp w α a b)) (proofErase (eqApp w α a b :: Γ) m.lift) from if_neg hp',
      proofErase_eqProofType heq hw hΓ hα ha hb,
      proofErase_liftN hΓ hΓE Ctx.LiftN.one hm]
    exact .base (.intro HC)

/-- Core primitives with finite layers of recursively contextual prefix guards. -/
def ErasedScopedPrefixStage (D : PureObservation.Definitions) :
    Nat → List ProofShape → ProofShape → ProofShape → Prop
  | 0 => fun _ => ErasedIotaPrimitive D
  | stage + 1 => fun Δ a b => ErasedScopedPrefixStage D stage Δ a b ∨
      ProofShape.ScopedPrefixKPrimitive (ErasedScopedPrefixStage D stage) Δ a b

/-- Every finite contextual prefix stage descends below any inserted block. -/
theorem erased_scoped_prefix_stage_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, ErasedScopedPrimitiveDescent (ErasedScopedPrefixStage D stage) := by
  intro stage
  induction stage with
  | zero => exact ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs)
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht R
    rcases R with R | R
    · exact ih hΓ hΓ' W ht R
    · exact erased_scoped_prefix_K_descent heq ih hΓ hΓ' W ht R

/-- Every contextual stage substitutes without increasing its bound, provided
its source and target contexts have a typed substitution interpretation. -/
theorem erased_scoped_prefix_stage_subst : ∀ stage {Δ Δ' a b τ},
    ErasedScopedPrefixStage D stage Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
    ErasedScopedPrefixStage D stage Δ' (a.subst τ) (b.subst τ) := by
  intro stage
  induction stage with
  | zero => exact fun H _ => erased_iota_primitive_subst H
  | succ stage ih =>
    intro Δ Δ' a b τ H W
    rcases H with H | H
    · exact .inl (ih H W)
    · exact .inr (H.subst ih W)

/-- One contextual stage contains every primitive of the preceding stage. -/
theorem erased_scoped_prefix_stage_succ (H : ErasedScopedPrefixStage D stage Δ a b) :
    ErasedScopedPrefixStage D (stage + 1) Δ a b := .inl H

/-- A prefix guarded by recursive eta or sorted comparison computes one stage
later to the literal canonical proof-domain lambda. -/
theorem proofErase_scoped_prefix_stage_forward (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (HC : ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ) true
      (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompute (ErasedScopedPrefixStage D (stage + 1)) (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) :=
  (proofErase_scoped_prefix_K_forward heq (erased_scoped_prefix_stage_descent heq hs stage)
    hΓ ht HC).mono (fun H => .inr H)

/-- Full K with a recursively contextual endpoint guard follows from prefix
unfolding and beta at the same successor stage; it needs no extra primitive. -/
theorem proofErase_scoped_prefix_full_forward
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecApp v w α a M m b p) T)
    (HC : ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ) true
      (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompute (ErasedScopedPrefixStage D (stage + 1)) (proofEraseCtx Γ)
      (proofErase Γ (eqRecApp v w α a M m b p)) (proofErase Γ m) := by
  obtain ⟨_, _, hα, ha, _, _, hb, _⟩ := eqRecApp_typings henv heq hΓ ⟨_, ht⟩
  have hab := (proofErase_scoped_compare_reflect
    (erased_scoped_prefix_stage_descent heq hs stage) hΓ ha hb HC).1 ⟨_, hα⟩
  have HH := eqRecApp_simAt henv heq hΓ hab T ht
  by_cases hp : IsProof Γ (eqRecApp v w α a M m b p)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HH).1 hp)]
    exact .refl
  · have HE := proofErase_const_spine hΓ (args := [α, a, M, m, b, p]) ht hp
    change proofErase Γ (eqRecApp v w α a M m b p) = _ at HE
    rw [HE]
    have HR : ProofShape.ScopedCompute (ErasedScopedPrefixStage D (stage + 1)) (proofEraseCtx Γ)
        (ProofShape.eqRecBeforeMajor v w (proofErase Γ α) (proofErase Γ a)
          (proofErase Γ M) (proofErase Γ m) (proofErase Γ b))
        (.lam (ProofShape.eqProofType w (proofErase Γ α) (proofErase Γ a) (proofErase Γ b))
          ((proofErase Γ m).liftN 1)) := .base (.inr (.intro HC))
    apply ProofShape.ScopedCompute.trans (.app HR (.refl (e := proofErase Γ p)))
    apply ProofShape.ScopedCompute.beta
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id] using
      (ProofShape.BetaRed.beta
        (A := ProofShape.eqProofType w (proofErase Γ α) (proofErase Γ a) (proofErase Γ b))
        (b := (proofErase Γ m).liftN 1) (a := proofErase Γ p))

/-- All earlier prefix-only primitives embed at the same stage and every
ambient context. Their raw guards become scoped guards with identical modes. -/
theorem erased_prefix_only_scoped : ∀ stage {Δ a b},
    ErasedPrefixOnlyStage D stage a b → ErasedScopedPrefixStage D stage Δ a b := by
  intro stage
  induction stage with
  | zero => exact id
  | succ stage ih =>
    intro Δ a b H
    rcases H with H | H
    · exact .inl (ih H)
    · cases H with
      | intro HC => exact .inr (.intro (HC.scoped (fun H => .base (ih H))))

end Lean4Lean.VEnv.Strengthening
