import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEqNativeCover
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqCarrierDecode

/-! # Lossless Eq carrier decoding in the full union

Typed Eq recovery uses a temporary anchor cover whose expansion disappears
from the native result type. Arbitrary union computation and comparison can
therefore be decoded without a general primitive substitution theorem.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private eqRaw eq_compute typed_compute
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqCarrierDecode
variable [Params]

private theorem typed_eq_recovery
    (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (HT : TypedSource Δ (eqRaw u α z a))
    (R : ScopedTypeRecovery (ErasedJointUnion D) Δ (.app (.app (.const ``Eq [u]) α) z) (.forallE A B)) :
    ScopedCompute (ErasedJointUnion D) Δ α A := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv (args := [α,z,a]) Ee
  obtain ⟨α₀, z₀, a₀, rfl⟩ : ∃ α₀ z₀ a₀, args = [α₀,z₀,a₀] := by
    have Hlen := congrArg List.length Eargs
    simp only [List.length_map] at Hlen
    cases args with
    | nil => cases Hlen
    | cons x xs => cases xs with
      | nil => cases Hlen
      | cons y ys => cases ys with
        | nil => cases Hlen
        | cons z zs => cases zs with
          | nil => exact ⟨_,_,_,rfl⟩
          | cons => cases Hlen
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at Eargs
  obtain ⟨rfl, rfl, rfl⟩ := Eargs
  obtain ⟨_, hα, hz, _⟩ := eqApp_typings heq hΓ ⟨_, ht⟩
  subst Δ
  exact proofErase_joint_union_eq_domain_compute heq hs hΓ hα hz R

private theorem eq_carrier_decode_raw
    (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (hn : ∀ {Δ ls args out}, ¬ (ErasedJointUnion D) Δ (ProofShape.mkApps (.const ``Eq ls) args) out)
    (H : JointCheck (ErasedJointUnion D) Δ kind sa sb) (hm : kind = .compare false)
    (Ea : sa = eqRaw u α z a) (Eb : sb = eqRaw v β w b)
    (HTa : TypedSource Δ sa) (HTb : TypedSource Δ sb)
    (Rα : ScopedCompute (ErasedJointUnion D) Δ κ α) (Rβ : ScopedCompute (ErasedJointUnion D) Δ κ β) :
    JointCarrierGuard (ErasedJointUnion D) Δ κ a b := by
  induction H generalizing u α z a v β w b κ with
  | leaf H =>
    cases hm
    cases H with
    | refl =>
      have EE := Ea.symm.trans Eb
      exact (ProofShape.app.inj EE).2 ▸ JointCheck.carrierChecked (JointCheck.leaf ScopedLeaf.refl)
    | sort | const => cases Ea
  | app HF HX => cases Ea; cases Eb; exact .carrierChecked HX
  | appCarrier R HF HX =>
    cases Ea
    cases Eb
    exact .carrierCompute (Rα.trans (typed_eq_recovery heq hs HTa R)) HX
  | compute Ra Rb HC ih =>
    obtain ⟨α', z', a', EA, Rα', _, Ra'⟩ := eq_compute hn (Ea ▸ Ra)
    obtain ⟨β', w', b', EB, Rβ', _, Rb'⟩ := eq_compute hn (Eb ▸ Rb)
    exact .carrierReduce Ra' Rb' (ih hm EA EB (typed_compute (erased_joint_union_descent heq hs) HTa Ra)
      (typed_compute (erased_joint_union_descent heq hs) HTb Rb) (Rα.trans Rα') (Rβ.trans Rβ'))
  | symm H ih => exact .carrierSymm (ih hm Eb Ea HTb HTa Rβ Rα)
  | proj | lam | forallE | lamSorted | forallSorted | etaLams => cases Ea
  | lamCommon | etaBodyL | etaBodyR | structFields |
      carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hm

/-- An inferred Eq comparison yields an endpoint guard at any common ancestor
of its two carriers. The original Eq spines must have actual typed realizations;
primitive computation must preserve Eq heads. Recoverable anchor covers
remove the unrestricted substitution premise. -/
theorem ProofShape.JointCompare.union_eq_carrier_decode
    (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (hn : ∀ {Δ ls args out}, ¬ (ErasedJointUnion D) Δ (ProofShape.mkApps (.const ``Eq ls) args) out)
    (HTa : TypedSource Δ (.app (.app (.app (.const ``Eq [u]) α) z) a))
    (HTb : TypedSource Δ (.app (.app (.app (.const ``Eq [v]) β) w) b))
    (Rα : ScopedCompute (ErasedJointUnion D) Δ κ α) (Rβ : ScopedCompute (ErasedJointUnion D) Δ κ β)
    (H : JointCompare (ErasedJointUnion D) Δ false
      (.app (.app (.app (.const ``Eq [u]) α) z) a)
      (.app (.app (.app (.const ``Eq [v]) β) w) b)) :
    JointCarrierGuard (ErasedJointUnion D) Δ κ a b :=
  eq_carrier_decode_raw heq hs hn H rfl rfl rfl HTa HTb Rα Rβ

/-- Either comparison mode between actual Eq propositions reads out a guard at
an arbitrary common supplied carrier. The anchors may differ. -/
theorem proofErase_joint_union_eq_carrier_decode
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hs : D.Sound env univs)
    (hn : ∀ {Δ ls args out}, ¬ (ErasedJointUnion D) Δ (ProofShape.mkApps (.const ``Eq ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α) (hw : env.HasType univs Γ w α)
    (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α)
    (H : JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) mode
      (proofErase Γ (eqApp u α z a)) (proofErase Γ (eqApp u α w b))) :
    JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b) := by
  have HA := HasType.eqApp heq hu hα hz ha
  have HB := HasType.eqApp heq hu hα hw hb
  have HC := proofErase_joint_types_inferred (erased_joint_union_descent heq hs) hΓ HA HB H
  have EA := proofErase_eqProofType heq hu hΓ hα hz ha
  have EB := proofErase_eqProofType heq hu hΓ hα hw hb
  rw [EA, EB] at HC
  exact HC.union_eq_carrier_decode heq hs hn
    ⟨Γ, _, _, hΓ, rfl, HA, EA⟩ ⟨Γ, _, _, hΓ, rfl, HB, EB⟩ .refl .refl

/-- Canonical Eq encodes typed full-union carrier guards without loss, in
either comparison mode, without general union substitution closure. This includes computed carriers and proof-valued endpoints. -/
theorem proofErase_joint_union_carrier_propositions_iff
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hs : D.Sound env univs)
    (hn : ∀ {Δ ls args out}, ¬ (ErasedJointUnion D) Δ (ProofShape.mkApps (.const ``Eq ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α)
    (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α) :
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) mode
      (proofErase Γ (eqApp u α z a)) (proofErase Γ (eqApp u α z b)) ↔
    JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b) :=
  ⟨proofErase_joint_union_eq_carrier_decode heq hu hs hn hΓ hα hz hz ha hb,
    proofErase_joint_carrier_propositions heq hu hΓ hα hz ha hb⟩


end Lean4Lean.VEnv.Strengthening
