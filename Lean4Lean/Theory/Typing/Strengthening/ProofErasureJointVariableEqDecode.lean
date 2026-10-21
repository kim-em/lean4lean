import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointNativeEqRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqCarrierDecode
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary

/-! # Full-union Eq decoding with variable anchors

A variable anchor remains fixed through every computation. Its recovery follows
computed carriers, so typed native Eq recovery suffices throughout comparison.
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
    (HR : ScopedTypeRecovery (ErasedJointUnion D) Δ z α)
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
  exact proofErase_joint_union_eq_prefix_domain_compute heq hs hΓ hα hz (fun _ => HR) R

private theorem eq_carrier_decode_raw
    (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (hn : ∀ {Δ ls args out}, ¬ (ErasedJointUnion D) Δ (ProofShape.mkApps (.const ``Eq ls) args) out)
    (H : JointCheck (ErasedJointUnion D) Δ kind sa sb) (hm : kind = .compare false)
    (Ea : sa = eqRaw u α (.bvar i) a) (Eb : sb = eqRaw v β (.bvar j) b)
    (HTa : TypedSource Δ sa) (HTb : TypedSource Δ sb)
    (HRi : ScopedTypeRecovery (ErasedJointUnion D) Δ (.bvar i) κ)
    (HRj : ScopedTypeRecovery (ErasedJointUnion D) Δ (.bvar j) κ)
    (Rα : ScopedCompute (ErasedJointUnion D) Δ κ α) (Rβ : ScopedCompute (ErasedJointUnion D) Δ κ β) :
    JointCarrierGuard (ErasedJointUnion D) Δ κ a b := by
  induction H generalizing u α i a v β j b κ with
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
    exact .carrierCompute (Rα.trans (typed_eq_recovery heq hs HTa (HRi.convert Rα) R)) HX
  | compute Ra Rb HC ih =>
    obtain ⟨α', z', a', EA, Rα', Rz', Ra'⟩ := eq_compute hn (Ea ▸ Ra)
    obtain ⟨β', w', b', EB, Rβ', Rw', Rb'⟩ := eq_compute hn (Eb ▸ Rb)
    cases Rz'.bvar_fixed erased_joint_union_head
    cases Rw'.bvar_fixed erased_joint_union_head
    exact .carrierReduce Ra' Rb' (ih hm EA EB (typed_compute (erased_joint_union_descent heq hs) HTa Ra)
      (typed_compute (erased_joint_union_descent heq hs) HTb Rb) HRi HRj (Rα.trans Rα') (Rβ.trans Rβ'))
  | symm H ih => exact .carrierSymm (ih hm Eb Ea HTb HTa HRj HRi Rβ Rα)
  | proj | lam | forallE | lamSorted | forallSorted | etaLams => cases Ea
  | lamCommon | etaBodyL | etaBodyR | structFields |
      carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hm

/-- An inferred Eq comparison in the full union reads out a carrier guard
when its variable anchors recover a common ancestor carrier. This requires
neither unrestricted substitution nor general recovery completeness. -/
theorem ProofShape.JointCompare.union_eq_carrier_decode_variables
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (HTa : TypedSource Δ (eqProofType u α (.bvar i) a))
    (HTb : TypedSource Δ (eqProofType v β (.bvar j) b))
    (HRi : ScopedTypeRecovery (ErasedJointUnion D) Δ (.bvar i) κ)
    (HRj : ScopedTypeRecovery (ErasedJointUnion D) Δ (.bvar j) κ)
    (Rα : ScopedCompute (ErasedJointUnion D) Δ κ α)
    (Rβ : ScopedCompute (ErasedJointUnion D) Δ κ β)
    (H : JointCompare (ErasedJointUnion D) Δ false
      (eqProofType u α (.bvar i) a) (eqProofType v β (.bvar j) b)) :
    JointCarrierGuard (ErasedJointUnion D) Δ κ a b := by
  apply eq_carrier_decode_raw heq hs ?_ H rfl rfl rfl HTa HTb HRi HRj Rα Rβ
  intro Δ ls args out H
  exact erased_joint_union_no_rigid heq (heq.rigid henv) hEq H (constHead_mkApps _ _)

end Lean4Lean.VEnv.Strengthening
