import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedOperationalReplay
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary

/-! # Eq prefixes with an explicitly unit-like carrier

An Eq recursor already carries the common type of its endpoints. When that
carrier is a registered empty structure, the original unitLike rule supplies
equality directly. Unlike endpoint type recovery, this syntactic carrier guard
survives arbitrary raw substitution. Source typing reconstructs it below any
inserted block. No endpoint comparison or recovery completeness is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

namespace ProofShape
/-- The displayed Eq carrier licenses unitLike equality of both endpoints.
The generated proof domain and payload are the ordinary K-prefix output. -/
inductive UnitPrefixPrimitive : ProofShape → ProofShape → Prop where
  | intro (hi : env.projections family info) (hx : info.nindices = 0)
      (hf : info.numFields = 0) (hp : ps.length = info.nparams) :
      UnitPrefixPrimitive (eqRecBeforeMajor v w (mkApps (.const family ls) ps) a M m b)
        (.lam (eqProofType w (mkApps (.const family ls) ps) a b) (m.liftN 1))

/-- The carrier guard retains its registry entry and arity under any raw
substitution, even when substituted endpoints cannot recover selected types. -/
theorem UnitPrefixPrimitive.subst (H : UnitPrefixPrimitive e out) (σ : Subst) :
    UnitPrefixPrimitive (e.subst σ) (out.subst σ) := by
  cases H with
  | @intro family info v w ls ps a M m b hi hx hf hp =>
    simpa only [eqRecBeforeMajor, eqProofType, ProofShape.subst, subst_mkApps,
      lift_subst_lift] using
      (UnitPrefixPrimitive.intro (v := v) (w := w) (ls := ls) (ps := ps.map (·.subst σ))
        (a := a.subst σ) (M := M.subst σ) (m := m.subst σ) (b := b.subst σ) hi hx hf
        (by simpa only [List.length_map] using hp))

/-- Unit-carrier prefixes retain the same constant-headed source restriction
as ordinary core and compared-prefix primitives. -/
theorem UnitPrefixPrimitive.head (H : UnitPrefixPrimitive e out) : PrimitiveHead e := by
  cases H
  trivial
end ProofShape

/-- Recovering the displayed carrier from the typed source suffices for exact
prefix descent. No strengthening of its endpoint typings is used. -/
theorem erased_unit_prefix_descent (heq : env.HasCanonicalEq) :
    ErasedPrimitiveDescent ProofShape.UnitPrefixPrimitive := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht R
  generalize hsrc : (proofErase Γ e).liftN n k = source at R
  cases R with
  | @intro family info v w ls ps a M m b hi hx hf hp =>
    obtain ⟨αs, as, Ms, ms, bs, E, Eα, Ea, EM, Em, Eb⟩ :=
      ProofShape.liftN_eqRecBeforeMajor_inv hsrc
    obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Hα, Ha, HM, Hm, Hb⟩ := proofErase_eqRecBeforeMajor_inv E
    rw [← Hα] at Eα
    rw [← Ha] at Ea
    rw [← HM] at EM
    rw [← Hm] at Em
    rw [← Hb] at Eb
    obtain ⟨rawArgs, Es, Eargs⟩ := ProofShape.liftN_const_spine_inv Eα
    obtain ⟨args, rfl, Eoriginal⟩ := proofErase_const_spine_inv Es
    have hlen : args.length = info.nparams := by
      have Hlen := congrArg List.length Eargs
      rw [Eoriginal] at Hlen
      simpa only [List.length_map, hp] using Hlen.symm
    obtain ⟨_, hw, hα, ha, _, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
    have hab : env.IsDefEqU univs Γ a₀ b₀ := ⟨_, IsDefEq.unitLike hi hlen hx hf ha hb⟩
    have HH := eqRecBeforeMajor_simAt henv heq hΓ hab T ht
    have hn : ¬ IsProof Γ (eqRecBeforeMajor v w (mkApps (.const family ls) args) a₀ M₀ m₀ b₀) := by
      intro hp
      rw [proofErase_eq_proof.2 hp] at E
      cases E
    have hn' := mt (isProof_congr hΓ HH).2 hn
    have hE := HasType.eqApp heq hw hα ha hb
    have hΓE : OnCtx (eqApp w (mkApps (.const family ls) args) a₀ b₀ :: Γ)
        (env.IsType univs) := ⟨hΓ, _, hE⟩
    refine ⟨_, HH, ?_⟩
    rw [show proofErase Γ (.lam (eqApp w (mkApps (.const family ls) args) a₀ b₀) m₀.lift) =
      .lam (proofErase Γ (eqApp w (mkApps (.const family ls) args) a₀ b₀))
        (proofErase (eqApp w (mkApps (.const family ls) args) a₀ b₀ :: Γ) m₀.lift) from if_neg hn',
      proofErase_eqProofType heq hw hΓ hα ha hb,
      proofErase_liftN hΓ hΓE Ctx.LiftN.one hm]
    simp only [ProofShape.liftN, ProofShape.eqProofType,
      ← ProofShape.liftN_comm _ n 1 k 0 (Nat.zero_le _), Eα, Ea, Eb, Em]

/-- Typed Eq prefixes over any explicit empty-structure family erase to the
new primitive computation, including distinct neutral endpoints. -/
theorem proofErase_unit_prefix_forward (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hf : info.numFields = 0) (hp : ps.length = info.nparams)
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w (mkApps (.const family ls) ps) a M m b) T) :
    ProofShape.Compute ProofShape.UnitPrefixPrimitive
      (proofErase Γ (eqRecBeforeMajor v w (mkApps (.const family ls) ps) a M m b))
      (proofErase Γ (.lam (eqApp w (mkApps (.const family ls) ps) a b) m.lift)) := by
  obtain ⟨_, hw, hα, ha, _, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have hab : env.IsDefEqU univs Γ a b := ⟨_, IsDefEq.unitLike hi hp hx hf ha hb⟩
  have HH := eqRecBeforeMajor_simAt henv heq hΓ hab T ht
  by_cases hproof : IsProof Γ (eqRecBeforeMajor v w (mkApps (.const family ls) ps) a M m b)
  · rw [proofErase_eq_proof.2 hproof, proofErase_eq_proof.2 ((isProof_congr hΓ HH).1 hproof)]
    exact .refl
  have hn' := mt (isProof_congr hΓ HH).2 hproof
  have HE := proofErase_const_spine hΓ ht hproof
  change proofErase Γ (eqRecBeforeMajor v w (mkApps (.const family ls) ps) a M m b) = _ at HE
  have hE := HasType.eqApp heq hw hα ha hb
  have hΓE : OnCtx (eqApp w (mkApps (.const family ls) ps) a b :: Γ) (env.IsType univs) := ⟨hΓ, _, hE⟩
  rw [HE, show proofErase Γ (.lam (eqApp w (mkApps (.const family ls) ps) a b) m.lift) =
    .lam (proofErase Γ (eqApp w (mkApps (.const family ls) ps) a b))
      (proofErase (eqApp w (mkApps (.const family ls) ps) a b :: Γ) m.lift) from if_neg hn',
    proofErase_eqProofType heq hw hΓ hα ha hb,
    proofErase_liftN hΓ hΓE Ctx.LiftN.one hm,
    proofErase_const_spine hΓ hα (not_isProof_of_sort hΓ hα)]
  simp only [List.map_cons, List.map_nil,
    proofErase_const_spine hΓ hα (not_isProof_of_sort hΓ hα)]
  exact .base (.intro hi hx hf (by simpa only [List.length_map] using hp))

/-- The new unit-carrier step replays through the actual registered singleton
program, with its exact erased target. Its declarative equality is not used as
an opaque replacement for an operational path. -/
theorem erased_unit_prefix_replay (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec) :
    ErasedScopedPrefixReplay D (fun _ => ProofShape.UnitPrefixPrimitive) := by
  intro Γ e T out hΓ ht R
  generalize hsrc : proofErase Γ e = source at R
  cases R with
  | @intro family info v w ls ps a M m b hi hx hf hp =>
    obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Hα, Ha, HM, Hm, Hb⟩ := proofErase_eqRecBeforeMajor_inv hsrc
    obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv Hα
    have hlen : args.length = info.nparams := by
      simpa only [List.length_map] using (congrArg List.length Eargs).symm.trans hp
    obtain ⟨_, hw, hα, ha, _, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
    have hab : env.IsDefEqU univs Γ a₀ b₀ := ⟨_, IsDefEq.unitLike hi hlen hx hf ha hb⟩
    have HP : PrefixUnfold env univs recursorData Γ ``Eq.rec [v, w]
        [mkApps (.const family ls) args, a₀, M₀, m₀, b₀]
        (.lam (eqApp w (mkApps (.const family ls) args) a₀ b₀) m₀.lift) := by
      obtain ⟨data, hl, hr, hn, _⟩ := heq.recursorRegistration henv
      exact eqRecBeforeMajor_prefix_registered henv heq hΓ hr hn
        (hregistry.trans hl) ⟨_, ht⟩ hab
    have HR : PureObservation.PrefixCompute D Γ
        (eqRecBeforeMajor v w (mkApps (.const family ls) args) a₀ M₀ m₀ b₀)
        (.lam (eqApp w (mkApps (.const family ls) args) a₀ b₀) m₀.lift) := .singleton HP
    have HH := HR.simAt hs hΓ T ht
    have hn : ¬ IsProof Γ (eqRecBeforeMajor v w (mkApps (.const family ls) args) a₀ M₀ m₀ b₀) := by
      intro hp
      rw [proofErase_eq_proof.2 hp] at hsrc
      cases hsrc
    have hn' := mt (isProof_congr hΓ HH).2 hn
    have hE := HasType.eqApp heq hw hα ha hb
    have hΓE : OnCtx (eqApp w (mkApps (.const family ls) args) a₀ b₀ :: Γ)
        (env.IsType univs) := ⟨hΓ, _, hE⟩
    refine ⟨_, HR, ?_⟩
    rw [show proofErase Γ (.lam (eqApp w (mkApps (.const family ls) args) a₀ b₀) m₀.lift) =
      .lam (proofErase Γ (eqApp w (mkApps (.const family ls) args) a₀ b₀))
        (proofErase (eqApp w (mkApps (.const family ls) args) a₀ b₀ :: Γ) m₀.lift) from if_neg hn',
      proofErase_eqProofType heq hw hΓ hα ha hb,
      proofErase_liftN hΓ hΓE Ctx.LiftN.one hm, Hα, Ha, Hb, Hm]

end Lean4Lean.VEnv.Strengthening
