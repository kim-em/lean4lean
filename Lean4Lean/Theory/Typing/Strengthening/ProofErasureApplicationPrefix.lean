import Lean4Lean.Theory.Typing.Strengthening.ProofErasureApplicationComparison

/-! # Eq prefix computation guarded by recursive recovered application checking

The enlarged guard descends and replays as an actual registered Eq prefix.
Substitution is not asserted: it must re-synthesize recovered argument carriers.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (PrefixCompute)
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

namespace ProofShape
/-- Recursive contextual endpoint comparison enables the proof-major prefix.
The guard and source share the same erased ambient context. -/
inductive ApplicationPrefixPrimitive
    (Step : List ProofShape → ProofShape → ProofShape → Prop) (Δ : List ProofShape) :
    ProofShape → ProofShape → Prop where
  | intro : ApplicationCompare Step Δ true a b →
      ApplicationPrefixPrimitive Step Δ (eqRecBeforeMajor v w α a M m b)
        (.lam (eqProofType w α a b) (m.liftN 1))

/-- Enlarging computation enlarges the recovered endpoint guard. -/
theorem ApplicationPrefixPrimitive.mono
    (hstep : ∀ {Δ a b}, Step Δ a b → Step' Δ a b)
    (H : ApplicationPrefixPrimitive Step Δ e out) : ApplicationPrefixPrimitive Step' Δ e out := by
  cases H with
  | intro HC => exact .intro (HC.mono hstep)

/-- The added primitive retains a constant-headed source. -/
theorem ApplicationPrefixPrimitive.head (H : ApplicationPrefixPrimitive Step Δ e out) :
    PrimitiveHead e := by cases H; trivial
end ProofShape

/-- Prefix K descends from a typed source. The exact lower proof domain is
recovered from that source, so the new lambda is not an arbitrary eta annotation. -/
theorem erased_application_prefix_descent
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveDescent Step) :
    ErasedScopedPrimitiveDescent (ProofShape.ApplicationPrefixPrimitive Step) := by
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
    have hab := (proofErase_application_compare_descend hstep hΓ hΓ' W rfl ha hb HC).1 ⟨_, hα⟩
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
theorem proofErase_application_prefix_forward
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (HC : ProofShape.ApplicationCompare Step (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompute (ProofShape.ApplicationPrefixPrimitive Step) (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) := by
  obtain ⟨_, hw, hα, ha, _, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have hab := (proofErase_application_compare_reflect hstep hΓ ha hb HC).1 ⟨_, hα⟩
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

/-- An application-checked prefix replays with its actual original captures
and registered Eq computation. -/
theorem erased_application_prefix_replay (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hstep : ErasedScopedPrimitiveDescent Step)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec) :
    ErasedScopedPrefixReplay D (ProofShape.ApplicationPrefixPrimitive Step) := by
  intro Γ e T out hΓ ht R
  generalize hsrc : proofErase Γ e = source at R
  cases R with
  | @intro a b v w α M m HC =>
    obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Hα, Ha, HM, Hm, Hb⟩ := proofErase_eqRecBeforeMajor_inv hsrc
    rw [← Ha, ← Hb] at HC
    obtain ⟨_, hw, hα, ha, _, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
    have hab := (proofErase_application_compare_reflect hstep hΓ ha hb HC).1 ⟨_, hα⟩
    have HP : PrefixUnfold env univs recursorData Γ ``Eq.rec [v, w]
        [α₀, a₀, M₀, m₀, b₀] (.lam (eqApp w α₀ a₀ b₀) m₀.lift) := by
      obtain ⟨data, hl, hr, hn, _⟩ := heq.recursorRegistration henv
      exact eqRecBeforeMajor_prefix_registered henv heq hΓ hr hn
        (hregistry.trans hl) ⟨_, ht⟩ hab
    have HR : PrefixCompute D Γ (eqRecBeforeMajor v w α₀ a₀ M₀ m₀ b₀)
        (.lam (eqApp w α₀ a₀ b₀) m₀.lift) := .singleton HP
    have HH := HR.simAt hs hΓ T ht
    have hn : ¬ IsProof Γ (eqRecBeforeMajor v w α₀ a₀ M₀ m₀ b₀) := by
      intro hp
      rw [proofErase_eq_proof.2 hp] at hsrc
      cases hsrc
    have hn' := mt (isProof_congr hΓ HH).2 hn
    have hE := HasType.eqApp heq hw hα ha hb
    have hΓE : OnCtx (eqApp w α₀ a₀ b₀ :: Γ) (env.IsType univs) := ⟨hΓ, _, hE⟩
    refine ⟨_, HR, ?_⟩
    rw [show proofErase Γ (.lam (eqApp w α₀ a₀ b₀) m₀.lift) =
      .lam (proofErase Γ (eqApp w α₀ a₀ b₀))
        (proofErase (eqApp w α₀ a₀ b₀ :: Γ) m₀.lift) from if_neg hn',
      proofErase_eqProofType heq hw hΓ hα ha hb,
      proofErase_liftN hΓ hΓE Ctx.LiftN.one hm, Hα, Ha, Hb, Hm]


end Lean4Lean.VEnv.Strengthening
