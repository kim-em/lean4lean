import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureCarrier
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureUnitSingletonStages

/-! # Eq prefixes with an explicit structure carrier

Recursive projection guards certify arbitrary majors at the carrier already
present in Eq.rec. Static proof fields are skipped. The rule descends,
substitutes and replays as an actual registered prefix without type recovery.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (PrefixCompute)
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

namespace ProofShape
/-- A carrier-indexed structure comparison licenses the ordinary Eq prefix. -/
inductive ScopedStructurePrefixPrimitive
    (Step : List ProofShape → ProofShape → ProofShape → Prop) (Δ : List ProofShape) :
    ProofShape → ProofShape → Prop where
  | intro : StructureCarrierGuard Step Δ α a b →
      ScopedStructurePrefixPrimitive Step Δ (eqRecBeforeMajor v w α a M m b)
        (.lam (eqProofType w α a b) (m.liftN 1))

/-- Context substitution preserves the structural carrier and retained-field
comparisons, with unchanged closed proof-field certificates. -/
theorem ScopedStructurePrefixPrimitive.subst
    (hstep : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (H : ScopedStructurePrefixPrimitive Step Δ e out) (W : ContextSubstitution Δ Δ' τ) :
    ScopedStructurePrefixPrimitive Step Δ' (e.subst τ) (out.subst τ) := by
  cases H with
  | intro HC =>
    simpa only [eqRecBeforeMajor, eqProofType, ProofShape.subst, lift_subst_lift] using
      (ScopedStructurePrefixPrimitive.intro (v := _) (w := _) (M := _) (m := _)
        (HC.subst hstep W))

/-- Guard monotonicity preserves the exact prefix source and output. -/
theorem ScopedStructurePrefixPrimitive.mono
    (hstep : ∀ {Δ a b}, Step Δ a b → Step' Δ a b)
    (H : ScopedStructurePrefixPrimitive Step Δ e out) :
    ScopedStructurePrefixPrimitive Step' Δ e out := by
  cases H with
  | intro HC => exact .intro (HC.mono hstep)

/-- Structure-carrier prefixes retain constant-headed primitive sources. -/
theorem ScopedStructurePrefixPrimitive.head (H : ScopedStructurePrefixPrimitive Step Δ e out) :
    PrimitiveHead e := by cases H; trivial

/-- The earlier unit-carrier primitive is the zero-field case, at any stage
and context, without requiring recursive comparisons. -/
theorem UnitPrefixPrimitive.structure (H : UnitPrefixPrimitive e out) :
    ScopedStructurePrefixPrimitive Step Δ e out := by
  cases H with
  | intro hi hx hf hp =>
    exact .intro (.intro hi hx hp (.inr (StructureReplay.ProofFields.of_no_fields hf))
      (by intro i hj; omega))
end ProofShape

/-- The carrier guard reconstructs the lower endpoint equation before the
source-typed prefix lambda is replayed below the inserted block. -/
theorem erased_structure_prefix_descent
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveDescent Step) :
    ErasedScopedPrimitiveDescent (ProofShape.ScopedStructurePrefixPrimitive Step) := by
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
    rw [← Eα, ← Ea, ← Eb] at HC
    obtain ⟨_, hw, hα, ha, _, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
    have hab := proofErase_structure_carrier_descend hstep hΓ hΓ' W ha hb HC
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


/-- Every typed Eq prefix with a carrier certificate computes to its exact
erased proof-domain lambda. Whole-proof sources erase to identity. -/
theorem proofErase_structure_prefix_forward
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (HC : ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ α) (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompute (ProofShape.ScopedStructurePrefixPrimitive Step) (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) := by
  obtain ⟨_, hw, hα, ha, _, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have hab : env.IsDefEqU univs Γ a b := ⟨_, proofErase_structure_carrier_reflect hstep hΓ ha hb HC⟩
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


/-- Every new primitive replays through the actual registered singleton
program. Registry agreement is the existing operational Eq-prefix interface. -/
theorem erased_structure_prefix_replay (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hstep : ErasedScopedPrimitiveDescent Step)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec) :
    ErasedScopedPrefixReplay D (ProofShape.ScopedStructurePrefixPrimitive Step) := by
  intro Γ e T out hΓ ht R
  generalize hsrc : proofErase Γ e = source at R
  cases R with
  | @intro α a b v w M m HC =>
    obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Hα, Ha, HM, Hm, Hb⟩ := proofErase_eqRecBeforeMajor_inv hsrc
    rw [← Hα, ← Ha, ← Hb] at HC
    obtain ⟨_, hw, hα, ha, _, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
    have hab : env.IsDefEqU univs Γ a₀ b₀ := ⟨_, proofErase_structure_carrier_reflect hstep hΓ ha hb HC⟩
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
