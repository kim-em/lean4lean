import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDisplayedLambdaApplication

/-! # Eq computation from displayed-domain application certificates

A finite extension of the full joint union admits Eq prefixes whose endpoint
comparison reads a lambda domain directly. Every layer retains exact lower
computation certificates. No recovery of the displayed lambda's codomain is
needed, and no completeness or arbitrary substitution theorem is asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- The usual Eq-prefix output, guarded by a displayed-lambda application
certificate instead of full recovery of the endpoint's function type. -/
inductive DisplayedLambdaPrefixPrimitive
    (Step : List ProofShape → ProofShape → ProofShape → Prop) (Δ : List ProofShape) :
    ProofShape → ProofShape → Prop where
  | intro {α a b : ProofShape} {v w : VLevel} {M m : ProofShape} : DisplayedLambdaApplication Step Δ a b →
      DisplayedLambdaPrefixPrimitive Step Δ (ProofShape.eqRecBeforeMajor v w α a M m b)
        (.lam (eqProofType w α a b) (m.liftN 1))

/-- These new primitive sources have the same constant head as ordinary Eq
prefixes. -/
theorem DisplayedLambdaPrefixPrimitive.head (H : DisplayedLambdaPrefixPrimitive Step Δ a b) :
    PrimitiveHead a := by cases H; trivial

/-- The displayed-domain endpoint certificate survives binder removal, so the
Eq prefix retains both its exact lower computation and original semantic replay. -/
theorem erased_displayed_lambda_prefix_certificate_descent
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveCertificateDescent Step Target) :
    ErasedScopedPrimitiveCertificateDescent (DisplayedLambdaPrefixPrimitive Step) (DisplayedLambdaPrefixPrimitive Target) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht R
  generalize hsrc : (proofErase Γ e).liftN n k = source at R
  cases R with
  | @intro α a b v w M m HC =>
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
    obtain ⟨CC, hab⟩ := proofErase_displayed_lambda_application_descend hstep hΓ hΓ' W ha hb HC
    have HH := eqRecBeforeMajor_simAt henv heq hΓ hab T ht
    have hn : ¬ IsProof Γ (eqRecBeforeMajor v w α₀ a₀ M₀ m₀ b₀) := by
      intro hp
      rw [proofErase_eq_proof.2 hp] at E
      cases E
    have hn' := mt (isProof_congr hΓ HH).2 hn
    have hE := HasType.eqApp heq hw hα ha hb
    have hΓE : OnCtx (eqApp w α₀ a₀ b₀ :: Γ) (env.IsType univs) := ⟨hΓ, _, hE⟩
    refine ⟨_, HH, ?_, ?_⟩
    · rw [E, show proofErase Γ (.lam (eqApp w α₀ a₀ b₀) m₀.lift) =
        .lam (proofErase Γ (eqApp w α₀ a₀ b₀)) (proofErase (eqApp w α₀ a₀ b₀ :: Γ) m₀.lift) from if_neg hn',
        proofErase_eqProofType heq hw hΓ hα ha hb,
        proofErase_liftN hΓ hΓE Ctx.LiftN.one hm, ← Hα, ← Ha, ← HM, ← Hm, ← Hb]
      exact .base (.intro CC)
    rw [show proofErase Γ (.lam (eqApp w α₀ a₀ b₀) m₀.lift) =
      .lam (proofErase Γ (eqApp w α₀ a₀ b₀)) (proofErase (eqApp w α₀ a₀ b₀ :: Γ) m₀.lift) from if_neg hn',
      proofErase_eqProofType heq hw hΓ hα ha hb,
      proofErase_liftN hΓ hΓE Ctx.LiftN.one hm]
    simp only [ProofShape.liftN, ProofShape.eqProofType,
      ← ProofShape.liftN_comm _ n 1 k 0 (Nat.zero_le _), Eα, Ea, Eb, Em]



/-- A typed prefix executes from its displayed-domain endpoint guard. -/
theorem proofErase_displayed_lambda_prefix_forward
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (HC : DisplayedLambdaApplication Step (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompute (DisplayedLambdaPrefixPrimitive Step) (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) := by
  obtain ⟨_, hw, hα, ha, _, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have hab := (proofErase_displayed_lambda_application_descend hstep hΓ hΓ
    (show Ctx.LiftN 0 0 Γ Γ from .zero []) ha hb
    (by simpa only [ProofShape.liftN_zero] using HC)).2
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


/-- Finite layers of the new Eq rule, starting with the entire existing joint
union. Recursive ordinary joint comparisons and carriers may use each preceding
layer's computations. This does not assert arbitrary substitution closure. -/
def ErasedDisplayedLambdaStage (D : PureObservation.Definitions) :
    Nat → List ProofShape → ProofShape → ProofShape → Prop
  | 0 => ErasedJointUnion D
  | stage + 1 => fun Δ a b => ErasedDisplayedLambdaStage D stage Δ a b ∨
      DisplayedLambdaPrefixPrimitive (ErasedDisplayedLambdaStage D stage) Δ a b

/-- Every finite added layer retains its exact lower computation certificate.
No new strengthening assumption enters this induction. -/
theorem erased_displayed_lambda_stage_certificate_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, ErasedScopedPrimitiveCertificateDescent
      (ErasedDisplayedLambdaStage D stage) (ErasedDisplayedLambdaStage D stage) := by
  intro stage
  induction stage with
  | zero => exact erased_joint_union_certificate_descent heq hs
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht H
    rcases H with H | H
    · obtain ⟨e', HE, R, E⟩ := ih hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inl H), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_displayed_lambda_prefix_certificate_descent heq ih
        hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inr H), E⟩

/-- The finite extension retains constant/projection-headed primitive sources. -/
theorem erased_displayed_lambda_stage_head : ∀ stage {Δ a b},
    ErasedDisplayedLambdaStage D stage Δ a b → PrimitiveHead a := by
  intro stage
  induction stage with
  | zero => exact erased_joint_union_head
  | succ stage ih =>
    intro Δ a b H
    exact H.elim ih DisplayedLambdaPrefixPrimitive.head

/-- A displayed-domain endpoint guard executes the Eq prefix at the next layer,
without first constructing recovery of the endpoint function's full Pi type. -/
theorem proofErase_displayed_lambda_stage_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (HC : DisplayedLambdaApplication (ErasedDisplayedLambdaStage D stage) (proofEraseCtx Γ)
      (proofErase Γ a) (proofErase Γ b)) :
    ScopedCompute (ErasedDisplayedLambdaStage D (stage + 1)) (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) :=
  (proofErase_displayed_lambda_prefix_forward heq
    (erased_displayed_lambda_stage_certificate_descent heq hs stage) hΓ ht HC).mono
      (fun H => .inr H)

end Lean4Lean.VEnv.Strengthening
