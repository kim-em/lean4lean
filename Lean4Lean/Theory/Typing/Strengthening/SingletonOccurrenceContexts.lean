import Lean4Lean.Theory.Typing.Strengthening.SingletonTransportNaturality

/-! # Generic and constructor singleton occurrence contexts -/
namespace Lean4Lean.PropElim
open VExpr VEnv SingletonLayout
variable {S : SingletonLayout} {params : List VExpr} {E : PropElim}

/-- The complete generic parameter/index/major telescope is well formed. -/
theorem WF.genericCtx (W : E.WF S params env U) :
    OnCtx (params ++ S.indices ++ [majorTy S params E]).reverse (env.IsType U) := by
  have h := W.typed.indicesCtx S.indices.length (Nat.le_refl _)
  rw [List.take_length] at h
  rw [List.reverse_append]
  exact ⟨h, _, W.majorTy_typed⟩

/-- The generic providers form the identity instance of that telescope. -/
theorem WF.genericArgs (henv : env.WF) (W : E.WF S params env U) :
    TelInst env U (params ++ S.indices ++ [majorTy S params E]).reverse
      (params ++ S.indices ++ [majorTy S params E])
      (genericPa S params ++ genericIa S ++ [.bvar 0]) := by
  have hmcl : (majorTy S params E).ClosedN (params.length + S.indices.length) := by
    have hc := CtxWF.closed henv.ordered (W.typed.indicesCtx S.indices.length (Nat.le_refl _))
    rw [List.take_length] at hc
    have := (W.majorTy_typed.closedN' henv.ordered.closed hc).1
    simpa [Nat.add_comm] using this
  have hcl : ∀ i (h : i < (params ++ S.indices ++ [majorTy S params E]).length),
      (params ++ S.indices ++ [majorTy S params E])[i].ClosedN i := by
    intro i h
    by_cases hi : i < (params ++ S.indices).length
    · rw [List.getElem_append_left hi]
      exact W.typed.prefix_closed (fun l h => W.typed.scope.indices l h) i hi
    · have : i = (params ++ S.indices).length := by simp at h hi ⊢; omega
      subst this
      simpa using hmcl
  have hid := TelInst.ident (env := env) (U := U) [] hcl
  simp only [List.append_nil, List.length_append, List.length_singleton] at hid
  have hsplit : bvarRange (params.length + S.indices.length + 1)
      (params.length + S.indices.length + 1) =
      genericPa S params ++ genericIa S ++ [.bvar 0] := by
    rw [bvarRange_append _ _ _ (Nat.le_refl _), bvarRange_append _ _ _ (by omega)]
    simp only [genericPa, genericIa, List.append_assoc]
    congr 2
    · simp [bvarRange]; intro a ha; omega
    · simp [bvarRange]
  rwa [hsplit] at hid

/-- The major family specializes to the supplied parameter and index spine. -/
theorem majorTy_at (W : E.WF S params env U)
    (hps : ps.length = params.length) (hidx : idx.length = S.indices.length) :
    (majorTy S params E).instOuter (ps ++ idx) = mkApps E.family (ps ++ idx) := by
  exact mkApps_instOuter_heads W.family_closed ps idx _ _ hps hidx

/-- The constructor gives a typed generic occurrence at its own indices. -/
theorem WF.branchArgs (W : E.WF S params env U) :
    TelInst env U (params ++ S.fields).reverse
      (params ++ S.indices ++ [majorTy S params E])
      (branchPa S params ++ E.ctorIndices ++ [ctorApp S params E]) := by
  apply W.ctorIndices_typed.append_one
  rw [majorTy_at W (by simp [branchPa]) W.ctorIndices_length]
  exact W.ctor_typed

/-- Family instances at typed occurrence indices are propositions. -/
theorem WF.family_prop (henv : env.WF) (W : E.WF S params env U)
    (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ idx ++ [m])) :
    env.HasType U Γ (mkApps E.family (ps ++ idx)) (.sort .zero) := by
  have hidx : idx.length = S.indices.length := by
    have := hargs.1; simp only [List.length_append, List.length_singleton] at this; omega
  have hia : TelInst env U Γ (params ++ S.indices) (ps ++ idx) := by
    have := hargs.take (doms := params ++ S.indices) (more := [majorTy S params E])
    simpa [hps, hidx, List.take_append, List.take_of_length_le] using this
  have hctx := W.typed.indicesCtx S.indices.length (Nat.le_refl _)
  rw [List.take_length] at hctx
  have h := HasType.closed_instOuter henv hctx W.majorTy_typed hia
  rwa [majorTy_at W hps hidx, instOuter_sort] at h

/-- The last occurrence argument has the family proposition as its type. -/
theorem WF.major_typed (W : E.WF S params env U) (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ idx ++ [m])) :
    env.HasType U Γ m (mkApps E.family (ps ++ idx)) := by
  have hidx : idx.length = S.indices.length := by
    have := hargs.1; simp only [List.length_append, List.length_singleton] at this; omega
  have h := hargs.getD (j := params.length + S.indices.length) (by simp)
  rw [getD_append_right' (by simp [hps, hidx]), List.take_append_of_le_length (by simp [hps, hidx]),
    List.take_of_length_le (by simp [hps, hidx])] at h
  simpa [hps, hidx, majorTy_at W hps hidx] using h

/-- Generic providers specialize to any actual occurrence. -/
theorem generic_at (hps : ps.length = params.length) (hidx : idx.length = S.indices.length) :
    (genericPa S params).map (·.instOuter (ps ++ idx ++ [m])) = ps ∧
    (genericIa S).map (·.instOuter (ps ++ idx ++ [m])) = idx := by
  have hlen : (ps ++ idx ++ [m]).length = params.length + S.indices.length + 1 := by
    simp [hps, hidx, Nat.add_assoc]
  constructor
  · rw [genericPa, instOuter_bvarRange _ _ _ (by omega) (by rw [hlen]; omega), hlen,
      Nat.sub_self, List.drop_zero, List.append_assoc, List.take_left' hps]
  · rw [genericIa, instOuter_bvarRange _ _ _ (by omega) (by rw [hlen]; omega), hlen,
      show params.length + S.indices.length + 1 - (S.indices.length + 1) = ps.length by omega,
      List.append_assoc, List.drop_left, List.take_left' hidx]

/-- Generic transported fields specialize to the transported occurrence program. -/
theorem transportedFields_at (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hps : ps.length = params.length)
    (hidx : idx.length = S.indices.length) (hi : i ≤ S.fields.length) :
    (transportedFields S params E (genericPa S params) (genericIa S) (.bvar 0) i).map
      (·.instOuter (ps ++ idx ++ [m])) = transportedFields S params E ps idx m i := by
  simp only [instOuter_eq_subst]
  rw [transportedFields_subst henv heq W (by simp [genericPa]) (by simp [genericIa]) hi]
  simp only [← instOuter_eq_subst, (generic_at hps hidx).1, (generic_at hps hidx).2]
  congr 1
  simp [instOuter_eq_subst, Subst.ofList]

end Lean4Lean.PropElim
