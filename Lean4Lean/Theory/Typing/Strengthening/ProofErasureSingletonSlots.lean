import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingleton
import Lean4Lean.Theory.Typing.Strengthening.GuardedSingletonPrefix

/-! # Exact erased slots of checked singleton reconstruction

The actual bare fields erase to selected index values and proof markers. Their
typing is retained as a premise: the always-typed cast-bearing reconstruction
cannot be substituted for the bare generator before family alignment.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PropElim

namespace ProofShape
/-- A bare singleton field is either its selected index or a hidden proof.
Out-of-range raw indices use a proof marker; typed layouts never read them. -/
def singletonSlots (slots : List (Option Nat)) (count : Nat) (idx : List ProofShape) : List ProofShape :=
  (List.range count).map fun j => match slots.getD j none with
    | some k => idx.getD k .proof
    | none => .proof

/-- The raw slot vector commutes with every erased substitution. -/
theorem singletonSlots_subst (σ : Subst) :
    (singletonSlots slots count idx).map (·.subst σ) =
      singletonSlots slots count (idx.map (·.subst σ)) := by
  simp only [singletonSlots, List.map_map]
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_apply]
  cases slots.getD j none with
  | none => rfl
  | some k =>
    by_cases hk : k < idx.length
    · simp only [getD_of_lt hk, getD_of_lt (by simpa using hk : k < (idx.map (·.subst σ)).length),
        List.getElem_map]
    · simp [List.getD, List.getElem?_eq_none (by omega : idx.length ≤ k),
        List.getElem?_map, ProofShape.subst]
end ProofShape

variable [Params] {S : SingletonLayout} {E : PropElim}

/-- A typed field whose layout slot is absent is a proof, even when other
fields in the same telescope retain data. -/
theorem proofErase_singleton_proof_field (W : E.WF S params env univs)
    (hps : ps.length = params.length)
    (hf : TelInst env univs Γ (params ++ S.fields) (ps ++ fields))
    (hj : j < S.fields.length) (hs : S.slot.getD j none = none) :
    proofErase Γ (fields.getD j default) = .proof := by
  have hfl : fields.length = S.fields.length := by
    have := hf.1
    simp only [List.length_append] at this
    omega
  have hprefix : TelInst env univs Γ (params ++ S.fields.take j)
      ((ps ++ fields).take (params.length + j)) := by
    have hf' : TelInst env univs Γ ((params ++ S.fields.take j) ++ S.fields.drop j)
        (ps ++ fields) := by simpa only [List.append_assoc, List.take_append_drop] using hf
    simpa only [List.length_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
      using hf'.take
  have hp := HasType.closed_instOuter henv (W.typed.fieldsCtx j (Nat.le_of_lt hj))
    (W.typed.fieldSort j hj) hprefix
  simp only [SingletonLayout.fieldSort, hs, instOuter_sort] at hp
  have ht := hf.getD (j := params.length + j) (by simp; omega)
  simp only [getD_append_right' (show ps.length ≤ params.length + j by omega),
    getD_append_right' (Nat.le_add_right _ _), hps, Nat.add_sub_cancel_left] at ht
  rw [getD_of_lt hj] at ht
  exact proofErase_eq_proof.2 ⟨_, ht, hp⟩

/-- Every typed bare occurrence has the literal erased slot vector. This
allows arbitrary dependent data fields and proof fields in the same layout. -/
theorem proofErase_singleton_occ_slots (W : E.WF S params env univs)
    (hps : ps.length = params.length) (hidx : idx.length = S.indices.length)
    (hf : TelInst env univs Γ (params ++ S.fields)
      (ps ++ (occ S params E ps idx m S.fields.length).2)) :
    (occ S params E ps idx m S.fields.length).2.map (proofErase Γ) =
      ProofShape.singletonSlots S.slot S.fields.length (idx.map (proofErase Γ)) := by
  have hfl := (occ_length S params E ps idx m S.fields.length).2
  apply List.ext_getElem (by simp [ProofShape.singletonSlots, hfl])
  intro j hj hj'
  have hjf : j < S.fields.length := by simpa only [List.length_map, hfl] using hj
  simp only [ProofShape.singletonSlots, List.getElem_map, List.getElem_range]
  cases hs : S.slot.getD j none with
  | none =>
    have hp := proofErase_singleton_proof_field W hps hf hjf hs
    simpa only [getD_of_lt (by omega : j < (occ S params E ps idx m S.fields.length).2.length)] using hp
  | some k =>
    have hk : k < idx.length := hidx ▸ W.typed.scope.slot_lt j k hs
    have hv := occ_getD_data (S := S) (P := params) (E := E) ps idx m hs hjf
    rw [getD_of_lt (by omega), getD_of_lt hk] at hv
    simp only [getD_of_lt (by simpa using hk : k < (idx.map (proofErase Γ)).length), List.getElem_map]
    exact congrArg (proofErase Γ) hv

end Lean4Lean.VEnv.Strengthening
