import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationTelescope
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationCast
import Lean4Lean.Theory.Typing.Strengthening.SingletonTransportComparison

/-! # Data-field reconstruction from explicit computational alignment

At an aligned constructor occurrence, the remaining cast comparison is between
the declared index domain and the declared field domain at the original fields.
Chains for these domain comparisons, and for the aligned data values, propagate
through the whole dependent reconstruction. This does not derive domain chains
from ordinary type uniqueness.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PropElim SingletonLayout
variable [Params] {D : PureObservation.Definitions} {params : List VExpr}

/-- Appending the next extracted proof extends reconstructed fields by the
corresponding cast (or proof field), with the previous prefix unchanged. -/
theorem transportedFields_succ
    (heq : env.HasCanonicalEq) (W : E.WF S params env univs)
    (hps : ps.length = params.length)
    (hargs : TelInst env univs Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ idx ++ [m])) (hi : i < S.fields.length) :
    transportedFields S params E ps idx m (i + 1) =
      transportedFields S params E ps idx m i ++
        [S.valHat ps idx i (transportedFields S params E ps idx m i)
          (mkApps (stepValue S params E i)
            (ps ++ idx ++ [m] ++ transportedWitnesses S params E ps idx m i))] := by
  have ht := transportedWitnesses_typed henv heq W hps hargs i (Nat.le_of_lt hi)
  have hl := ht.1.trans (S.tel_length ps idx i).1
  simp only [transportedFields, transportedWitnesses, substHat]
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    getD_append_right' (by omega), hl, Nat.sub_self]
  rfl

/-- Explicit data-slot value chains and domain chains suffice for all extracted
fields, including dependent data fields. The domain premise remains missing in
the general singleton case: ordinary uniqueness proves only ordinary equality. -/
theorem transportedFields_chain_of_data_alignment
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : E.WF S params env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hps : ps.length = params.length)
    (hargs : TelInst env univs Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ idx ++ [m]))
    (hf : TelInst env univs Γ (params ++ S.fields) (ps ++ f))
    (halign : ∀ l k, l < S.fields.length → S.slot.getD l none = some k →
      TypedComputationEq D Γ (idx.getD k default) (f.getD l default)
        ((S.fields.getD l default).instOuter (ps ++ f.take l)))
    (hdomains : ∀ l k, l < S.fields.length → S.slot.getD l none = some k →
      TypedComputationEq D Γ
        ((S.indices.getD k default).instOuter (ps ++ idx.take k))
        ((S.fields.getD l default).instOuter (ps ++ f.take l))
        (.sort (S.sorts.getD l .zero))) :
    ∀ i, i ≤ S.fields.length →
      List.Forall₂ (fun a b => ∃ A, TypedComputationEq D Γ a b A)
        (transportedFields S params E ps idx m i) (f.take i) := by
  have hfl : f.length = S.fields.length := by
    have := hf.1; simp only [List.length_append, hps] at this; omega
  have hpa : TelInst env univs Γ params ps := by
    have := hf.take (doms := params) (more := S.fields)
    simpa [hps] using this
  intro i
  induction i with
  | zero => intro _; exact .nil
  | succ i ih =>
    intro hi
    have hi' : i < S.fields.length := hi
    have Hprev := ih (Nat.le_of_lt hi')
    have hc := transportedFields_typed henv heq W hΓ hps hargs (Nat.le_of_lt hi')
    have hcl : (transportedFields S params E ps idx m i).length = i := by
      have := hc.1
      simp only [List.length_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi'), hps] at this
      omega
    have HY := TypedComputationEq.closed_instOuter_congr hΓ
      (W.typed.fieldsCtx i (Nat.le_of_lt hi')) (W.typed.fieldSort i hi') hc
      ((TypedComputationEq.telInst_refl hpa).append Hprev)
    simp only [instOuter_sort] at HY
    have hnext := transportedFields_typed henv heq W hΓ hps hargs hi
    have hstep := transportedFields_succ heq W hps hargs hi'
    let v := S.valHat ps idx i (transportedFields S params E ps idx m i)
      (mkApps (stepValue S params E i)
        (ps ++ idx ++ [m] ++ transportedWitnesses S params E ps idx m i))
    change transportedFields S params E ps idx m (i + 1) =
      transportedFields S params E ps idx m i ++ [v] at hstep
    have hv := hnext.getD (j := params.length + i) (by simp; omega)
    rw [getD_append_right' (by omega), getD_append_right' (by omega), hps,
      Nat.add_sub_cancel_left, getD_take_lt (by omega), getD_of_lt hi',
      List.take_append, List.take_of_length_le (by omega), hps, Nat.add_sub_cancel_left,
      hstep, getD_append_right' (by omega), hcl, Nat.sub_self,
      List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at hv
    simp only [List.getD_cons_zero] at hv
    have hfi : env.HasType univs Γ (f.getD i default)
        (S.fields[i].instOuter (ps ++ f.take i)) := by
      have h := hf.getD (j := params.length + i) (by simp; omega)
      simpa only [getD_append_right' (show ps.length ≤ params.length + i by omega),
        getD_append_right' (show params.length ≤ params.length + i by omega), hps,
        Nat.add_sub_cancel_left, getD_of_lt hi', List.take_append,
        List.take_of_length_le (show ps.length ≤ params.length + i by omega)] using h
    have Hlast : ∃ A, TypedComputationEq D Γ v (f.getD i default) A := by
      cases hslot : S.slot.getD i none with
      | none =>
        have hsort : S.fieldSort i = .zero := by unfold fieldSort; rw [hslot]
        have hY := HY.defeq.hasType.1
        rw [hsort] at hY
        exact ⟨_, .proof_irrel hY hv (HY.defeq.symm.defeq hfi)⟩
      | some k =>
        have hsort : S.fieldSort i = S.sorts.getD i .zero := by unfold fieldSort; rw [hslot]
        rw [hsort] at HY
        have HD := hdomains i k hi' hslot
        rw [getD_of_lt hi'] at HD
        have HC := TypedComputationEq.typeCast heq hs hΓ
          (show env.HasType univs Γ (VExpr.typeCast (S.sorts.getD i .zero)
            ((S.indices.getD k default).instOuter (ps ++ idx.take k))
            (S.fields[i].instOuter (ps ++ transportedFields S params E ps idx m i))
            _ (idx.getD k default)) _ from by simpa only [v, valHat, hslot, getD_of_lt hi'] using hv)
          (HD.trans HY.symm)
        have HA := (halign i k hi' hslot).at_source_type hΓ HC.defeq.hasType.2
        exact ⟨_, by simpa only [v, valHat, hslot, getD_of_lt hi'] using HC.trans HA⟩
    rw [hstep, List.take_add_one, List.getElem?_eq_getElem (show i < f.length by omega)]
    simp only [Option.toList_some]
    apply Hprev.append
    exact .cons (by simpa only [getD_of_lt (show i < f.length by omega)] using Hlast) .nil

end Lean4Lean.VEnv.Strengthening
