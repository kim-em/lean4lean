import Lean4Lean.Theory.Typing.Strengthening.SingletonTransportComparison

/-! # Substitution of transported singleton reconstruction

The proof-producing step functions are closed. The entire reconstruction hence
commutes with arbitrary substitution of its parameters, indices, and major.
This lets a generic propositional motive mention the reconstructed family.
-/
namespace Lean4Lean
open VExpr VEnv SingletonLayout

namespace SingletonLayout

private theorem getD_map_subst (xs : List VExpr) (i : Nat) (τ : Subst) :
    (xs.map (·.subst τ)).getD i default = (xs.getD i default).subst τ := by
  by_cases h : i < xs.length
  · rw [getD_of_lt h, getD_of_lt (by simpa using h : i < (xs.map (·.subst τ)).length),
      List.getElem_map]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : xs.length ≤ i),
      List.getElem?_eq_none (by simpa using (by omega : xs.length ≤ i) :
        (xs.map (·.subst τ)).length ≤ i), default]

/-- Instantiated fields commute with substitution of all their providers. -/
theorem substHat_subst {S : SingletonLayout} (H : S.Scoped pa.length)
    (hia : ia.length = S.indices.length) (τ : Subst) :
    ∀ i t, t.length = i →
      (S.substHat pa ia i t).map (·.subst τ) =
        S.substHat (pa.map (·.subst τ)) (ia.map (·.subst τ)) i (t.map (·.subst τ)) := by
  intro i
  induction i with
  | zero => intro t _; rfl
  | succ i ih =>
    intro t ht
    have hti : (t.take i).length = i := by simp [ht]
    have hslen : (S.substHat pa ia i (t.take i)).length = i := by
      rw [← tel_instOuter H hia i _ hti]
      simp [(S.tel_length pa ia i).2]
    have hY := instOuter_subst_closed (S.fields.getD i default)
      (pa ++ S.substHat pa ia i (t.take i))
      (by simpa [hslen] using H.fields_getD i) τ
    simp only [substHat, List.map_append, List.map_cons, List.map_nil,
      ← List.map_take, ih _ hti]
    congr 2
    unfold valHat
    split
    · rename_i k hk
      have hki := H.slot_lt i k hk
      have hX := instOuter_subst_closed (S.indices.getD k default)
        (pa ++ ia.take k) (by simpa [hia, Nat.min_eq_left (Nat.le_of_lt hki)]
          using H.indices_getD k) τ
      simp only [typeCast_subst, hX, hY, List.map_append, ih _ hti,
        getD_map_subst, List.map_take]
    · exact (getD_map_subst t i τ).symm

end SingletonLayout

namespace PropElim
variable {S : SingletonLayout} {params : List VExpr} {E : PropElim}

/-- Each witness extractor is closed because it is typed in the empty context. -/
theorem stepValue_closed (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hj : j < S.fields.length) :
    (stepValue S params E j).ClosedN 0 :=
  ((stepValue_typed henv heq W hj).closedN' henv.ordered.closed trivial).1

/-- Substitution changes only the occurrence arguments of witness extraction. -/
theorem transportedWitnesses_subst (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (τ : Subst) :
    ∀ i, i ≤ S.fields.length →
      (transportedWitnesses S params E ps idx m i).map (·.subst τ) =
        transportedWitnesses S params E (ps.map (·.subst τ)) (idx.map (·.subst τ))
          (m.subst τ) i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    simp only [transportedWitnesses, List.map_append, List.map_cons, List.map_nil,
      subst_mkApps, (stepValue_closed henv heq W hi).subst_eq .zero,
      ih (Nat.le_of_succ_le hi)]

/-- Transported fields commute with every raw substitution. Typing of the
occurrence is unnecessary; only the closed extractor's declaration is used. -/
theorem transportedFields_subst (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hps : ps.length = params.length)
    (hidx : idx.length = S.indices.length) (hi : i ≤ S.fields.length) (τ : Subst) :
    (transportedFields S params E ps idx m i).map (·.subst τ) =
      transportedFields S params E (ps.map (·.subst τ)) (idx.map (·.subst τ))
        (m.subst τ) i := by
  have hlen : ∀ j, (transportedWitnesses S params E ps idx m j).length = j := by
    intro j; induction j with
    | zero => rfl
    | succ j ih => simp [transportedWitnesses, ih]
  unfold transportedFields
  rw [substHat_subst (W.typed.scope.mono_pa hps) hidx τ i _ (hlen i),
    transportedWitnesses_subst henv heq W τ i hi]

end PropElim
end Lean4Lean
