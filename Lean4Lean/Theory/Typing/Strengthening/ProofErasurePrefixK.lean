import Lean4Lean.Theory.Typing.Strengthening.EqRecBeforeMajorReplay
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRawCheckedK

/-! # Erased equality computation before the proof major

The raw rule retains the five supplied arguments and reconstructs the canonical
proof domain. Its endpoint guard is oracle-free, so substitution is unrestricted.
Typed descent recovers the original prefix and its literal residual telescope.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_const_inv isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private ProofShape.liftN_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private ProofShape.liftN_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison

namespace ProofShape
/-- Canonical equality type in proof-erased syntax. -/
def eqProofType (w : VLevel) (α a b : ProofShape) : ProofShape :=
  .app (.app (.app (.const ``Eq [w]) α) a) b

/-- The five-argument Eq.rec prefix in proof-erased syntax. -/
def eqRecBeforeMajor (v w : VLevel) (α a M m b : ProofShape) : ProofShape :=
  .app (.app (.app (.app (.app (.const ``Eq.rec [v, w]) α) a) M) m) b

variable [Params]
/-- An endpoint checking guard unfolds the prefix to the canonical proof-domain
lambda returning the lifted minor. No proof major or ambient oracle is needed. -/
inductive RawCheckedPrefixKPrimitive (Step : ProofShape → ProofShape → Prop) :
    ProofShape → ProofShape → Prop where
  | intro : RawCheckedCompare Step true a b →
      RawCheckedPrefixKPrimitive Step (eqRecBeforeMajor v w α a M m b)
        (.lam (eqProofType w α a b) (m.liftN 1))

/-- The exact residual proof domain and lifted minor survive raw substitution. -/
theorem RawCheckedPrefixKPrimitive.subst
    (hstep : ∀ {a b} {σ : Subst}, Step a b → Step (a.subst σ) (b.subst σ))
    (H : RawCheckedPrefixKPrimitive Step e out) :
    RawCheckedPrefixKPrimitive Step (e.subst σ) (out.subst σ) := by
  cases H with
  | intro HC =>
    simpa only [eqRecBeforeMajor, eqProofType, ProofShape.subst, lift_subst_lift] using
      (RawCheckedPrefixKPrimitive.intro (v := _) (w := _) (α := _) (M := _) (m := _)
        (HC.subst hstep (σ := σ)))

/-- Prefix steps weaken with their endpoint checking guards. -/
theorem RawCheckedPrefixKPrimitive.liftN
    (hstep : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (H : RawCheckedPrefixKPrimitive Step e out) :
    RawCheckedPrefixKPrimitive Step (e.liftN n k) (out.liftN n k) := by
  cases H with
  | intro HC =>
    simpa only [eqRecBeforeMajor, eqProofType, ProofShape.liftN,
      ← liftN_comm _ n 1 k 0 (Nat.zero_le _)] using
      (RawCheckedPrefixKPrimitive.intro (v := _) (w := _) (α := _) (M := _) (m := _)
        (HC.liftN hstep (n := n) (k := k)))

/-- A lifted prefix exposes five lower shapes with their exact lifted images. -/
theorem liftN_eqRecBeforeMajor_inv
    (H : e.liftN n k = eqRecBeforeMajor v w α a M m b) :
    ∃ α₀ a₀ M₀ m₀ b₀, e = eqRecBeforeMajor v w α₀ a₀ M₀ m₀ b₀ ∧
      α₀.liftN n k = α ∧ a₀.liftN n k = a ∧ M₀.liftN n k = M ∧
      m₀.liftN n k = m ∧ b₀.liftN n k = b := by
  obtain ⟨f, b₀, rfl, Hf, Hb⟩ := ProofShape.liftN_app_inv H
  obtain ⟨f, m₀, rfl, Hf, Hm⟩ := ProofShape.liftN_app_inv Hf
  obtain ⟨f, M₀, rfl, Hf, HM⟩ := ProofShape.liftN_app_inv Hf
  obtain ⟨f, a₀, rfl, Hf, Ha⟩ := ProofShape.liftN_app_inv Hf
  obtain ⟨f, α₀, rfl, Hf, Hα⟩ := ProofShape.liftN_app_inv Hf
  obtain rfl := ProofShape.liftN_const_inv Hf
  exact ⟨_, _, _, _, _, rfl, Hα, Ha, HM, Hm, Hb⟩
end ProofShape

variable [Params]

/-- Erasure of a visible five-argument prefix retains all its actual arguments. -/
theorem proofErase_eqRecBeforeMajor_inv
    (H : proofErase Γ e = ProofShape.eqRecBeforeMajor v w α a M m b) :
    ∃ α₀ a₀ M₀ m₀ b₀, e = eqRecBeforeMajor v w α₀ a₀ M₀ m₀ b₀ ∧
      proofErase Γ α₀ = α ∧ proofErase Γ a₀ = a ∧ proofErase Γ M₀ = M ∧
      proofErase Γ m₀ = m ∧ proofErase Γ b₀ = b := by
  obtain ⟨f, b₀, rfl, _, Hf, Hb⟩ := erase_app_inv H
  obtain ⟨f, m₀, rfl, _, Hf, Hm⟩ := erase_app_inv Hf
  obtain ⟨f, M₀, rfl, _, Hf, HM⟩ := erase_app_inv Hf
  obtain ⟨f, a₀, rfl, _, Hf, Ha⟩ := erase_app_inv Hf
  obtain ⟨f, α₀, rfl, _, Hf, Hα⟩ := erase_app_inv Hf
  obtain rfl := erase_const_inv Hf
  exact ⟨_, _, _, _, _, rfl, Hα, Ha, HM, Hm, Hb⟩

/-- A typed equality type erases structurally, including proof-valued endpoints. -/
theorem proofErase_eqProofType (heq : env.HasCanonicalEq) (hw : w.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort w))
    (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α) :
    proofErase Γ (eqApp w α a b) =
      ProofShape.eqProofType w (proofErase Γ α) (proofErase Γ a) (proofErase Γ b) := by
  have ht := HasType.eqApp heq hw hα ha hb
  exact proofErase_const_spine hΓ (args := [α, a, b]) ht (not_isProof_of_sort hΓ ht)

/-- Prefix K descends from a typed source. The exact lower proof domain is
recovered from that source, so the new lambda is not an arbitrary eta annotation. -/
theorem erased_rawChecked_prefix_K_descent
    (heq : env.HasCanonicalEq) (hstep : ErasedPrimitiveDescent Step) :
    ErasedPrimitiveDescent (ProofShape.RawCheckedPrefixKPrimitive Step) := by
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
    have hab := (proofErase_rawChecked_compare_descend hstep hΓ hΓ' W ha hb HC).1 ⟨_, hα⟩
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
theorem proofErase_rawChecked_prefix_K_forward
    (heq : env.HasCanonicalEq) (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (HC : ProofShape.RawCheckedCompare Step true (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.Compute (ProofShape.RawCheckedPrefixKPrimitive Step)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) := by
  obtain ⟨_, hw, hα, ha, _, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have hab := (proofErase_rawChecked_compare_reflect hstep hΓ ha hb HC).1 ⟨_, hα⟩
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

end Lean4Lean.VEnv.Strengthening
