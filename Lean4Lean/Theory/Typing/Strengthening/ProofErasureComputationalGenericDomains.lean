import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationalTyping
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureGenericDataDomains

/-! # Generic data domains from computational index typing

Canonical field variables have structural lookup certificates. Computational
certificates for the constructor indices therefore determine their domain
chains by literal lookup uniqueness, without type-fork joining. Supplying the
index certificates from declaration history remains an explicit obligation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PropElim SingletonLayout
variable [Params] {D : PureObservation.Definitions} {params : List VExpr}
  {S : SingletonLayout} {E : PropElim}

/-- A telescope instance retaining computational assignment conversions. -/
def ComputationalTelInst (D : PureObservation.Definitions) (Γ doms args : List VExpr) : Prop :=
  args.length = doms.length ∧ ∀ j (hj : j < args.length) (hd : j < doms.length),
    HasTypeC D Γ args[j] (doms[j].instOuter (args.take j))

/-- Forgetting the certificates gives ordinary telescope typing. -/
theorem ComputationalTelInst.hasType (H : ComputationalTelInst D Γ doms args) :
    TelInst env univs Γ doms args := ⟨H.1, fun j hj hd => (H.2 j hj hd).hasType⟩

/-- Index a computational telescope instance using defaulted list access. -/
theorem ComputationalTelInst.getD (H : ComputationalTelInst D Γ doms args) (hj : j < doms.length) :
    HasTypeC D Γ (args.getD j default) ((doms.getD j default).instOuter (args.take j)) := by
  have ha : j < args.length := H.1.symm ▸ hj
  simpa only [getD_of_lt ha, getD_of_lt hj] using H.2 j ha hj

/-- The identity telescope uses exact variable lookups and no conversion. -/
theorem ComputationalTelInst.ident (Γ : List VExpr) (hcl : ∀ j (h : j < doms.length), (doms[j]).ClosedN j) :
    ComputationalTelInst D (doms.reverse ++ Γ) doms (bvarRange doms.length doms.length) := by
  refine ⟨by simp, fun j hj hj' => ?_⟩
  simp only [bvarRange_length] at hj
  rw [bvarRange_getElem _ _ _ hj, bvarRange_take _ _ _ (Nat.le_of_lt hj),
    VExpr.instOuter_range_bvar' _ _ _ (hcl j hj') (Nat.le_of_lt hj)]
  exact .bvar (Lookup.reverse_append doms Γ j hj')

/-- Constructor index certificates compare the index and field domains of
one literal data slot. The only equality of lookups used here is syntactic. -/
theorem singleton_generic_data_domains_of_computational_indices
    (W : E.WF S params env univs)
    (HI : ComputationalTelInst D (params ++ S.fields).reverse (params ++ S.indices)
      (branchPa S params ++ E.ctorIndices)) (hl : l < S.fields.length)
    (hslot : S.slot.getD l none = some k) :
    TypedComputationEq D (params ++ S.fields).reverse
      ((S.indices.getD k default).instOuter (branchPa S params ++ E.ctorIndices.take k))
      ((S.fields.getD l default).instOuter (branchPa S params ++ bvarRange l S.fields.length))
      (.sort (S.sorts.getD l .zero)) := by
  have hctx := W.typed.fieldsCtx S.fields.length (Nat.le_refl _)
  rw [List.take_length] at hctx
  have hcl := W.typed.prefix_closed (fun i hi => W.typed.scope.fields i hi)
  have hid := ComputationalTelInst.ident (D := D) [] hcl
  simp only [List.append_nil, List.length_append] at hid
  have hsplit : bvarRange (params.length + S.fields.length) (params.length + S.fields.length) =
      branchPa S params ++ bvarRange S.fields.length S.fields.length := by
    rw [bvarRange_append _ _ _ (Nat.le_refl _)]
    simp only [branchPa, Nat.add_sub_cancel_left]
  rw [hsplit] at hid
  have hf := hid.getD (j := params.length + l) (by simp; omega)
  rw [getD_append_right' (by simp [branchPa]), getD_append_right' (by omega)] at hf
  simp only [branchPa, bvarRange_length, Nat.add_sub_cancel_left, List.take_append] at hf
  rw [List.take_of_length_le (by simp only [bvarRange_length]; omega),
    getD_of_lt (by simpa only [bvarRange_length] using hl), bvarRange_getElem _ _ _ hl,
    bvarRange_take _ _ _ (Nat.le_of_lt hl)] at hf
  have hk := W.typed.scope.slot_lt l k hslot
  have hx := HI.getD (j := params.length + k) (by simp; omega)
  rw [getD_append_right' (by simp [branchPa]), getD_append_right' (by omega)] at hx
  simp only [branchPa, bvarRange_length, Nat.add_sub_cancel_left, List.take_append] at hx
  rw [List.take_of_length_le (by simp only [bvarRange_length]; omega), W.slot_literal l k hslot] at hx
  have hp : TelInst env univs (params ++ S.fields).reverse (params ++ S.fields.take l)
      (branchPa S params ++ bvarRange l S.fields.length) := by
    have hsplit : params ++ S.fields = (params ++ S.fields.take l) ++ S.fields.drop l := by
      rw [List.append_assoc, List.take_append_drop]
    rw [hsplit] at hid
    have hp := hid.hasType.take
    rw [← hsplit] at hp
    simpa only [List.length_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt hl),
      List.take_append, branchPa, bvarRange_length, Nat.add_sub_cancel_left,
      List.take_of_length_le (show (bvarRange params.length (params.length + S.fields.length)).length ≤ params.length + l by simp),
      bvarRange_take _ _ _ (Nat.le_of_lt hl)] using hp
  have hY := HasType.closed_instOuter henv (W.typed.fieldsCtx l (Nat.le_of_lt hl))
    (W.typed.fieldSort l hl) hp
  simp only [instOuter_sort, fieldSort, hslot] at hY
  rw [← getD_of_lt hl] at hY
  obtain ⟨_, H⟩ := hx.bvar_uniq hctx hf
  exact (H.symm.at_source_type hctx hY).symm

/-- Computational index typing supplies all previously open generic data
chains. Obtaining this typing from earlier declaration history remains open. -/
theorem ComputationalTelInst.generic_data_domains
    (W : E.WF S params env univs)
    (HI : ComputationalTelInst D (params ++ S.fields).reverse (params ++ S.indices)
      (branchPa S params ++ E.ctorIndices)) : SingletonGenericDataDomainChains D S params E :=
  fun _ _ hl hslot => singleton_generic_data_domains_of_computational_indices W HI hl hslot

end Lean4Lean.VEnv.Strengthening
