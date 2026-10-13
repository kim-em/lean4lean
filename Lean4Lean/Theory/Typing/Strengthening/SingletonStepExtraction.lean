import Lean4Lean.Theory.Typing.Strengthening.SingletonStepWitness

/-! # Closed extraction of every singleton telescope witness

Unlike the aligned occurrence program, these functions eliminate the major into
Prop to obtain data-slot equality witnesses as well as proof fields. They never
supply a reflexivity proof at an unaligned generic occurrence.
-/
namespace Lean4Lean
open VExpr VEnv SingletonLayout

namespace SingletonLayout
/-- The proposition asking for the next witness after all previous ones. -/
def stepBody (S : SingletonLayout) (pa ia : List VExpr) (i : Nat) : VExpr :=
  wrapForalls (S.tel pa ia i).1 (S.step pa ia i (S.tel pa ia i).2).1

/-- This proposition commutes with substitution of its parameter/index providers. -/
theorem stepBody_subst {S : SingletonLayout} (H : S.Scoped pa.length)
    (hia : ia.length = S.indices.length) (i : Nat) (τ : Subst) :
    (S.stepBody pa ia i).subst τ =
      S.stepBody (pa.map (·.subst τ)) (ia.map (·.subst τ)) i := by
  unfold stepBody
  rw [subst_wrapForalls, (S.tel_length pa ia i).1,
    (step_subst H hia i _ (S.tel_length pa ia i).2 τ).1,
    (tel_subst H hia τ i).1, (tel_subst H hia τ i).2]
end SingletonLayout

namespace PropElim
variable (S : SingletonLayout) (params : List VExpr) (E : PropElim)

/-- Constructor branch producing the next telescope witness. -/
def stepBranch (i : Nat) : VExpr :=
  wrapLams (S.tel (branchPa S params) E.ctorIndices i).1
    (S.stepWitness (branchPa S params) E.ctorIndices i)

/-- Closed extraction function for either a proof field or a data-slot equality. -/
def stepValue (i : Nat) : VExpr :=
  valueOf S params E (S.stepBody (genericPa S params) (genericIa S) i)
    (stepBranch S params E i)

variable {S params E}

/-- Every next-step proposition is typed in the generic context. -/
theorem stepBody_prop (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hj : j < S.fields.length) :
    env.HasType U (params ++ S.indices ++ [majorTy S params E]).reverse
      (S.stepBody (genericPa S params) (genericIa S) j) (.sort .zero) := by
  have T := W.typed
  -- the generic context: parameters, indices, major
  have hmcl : (majorTy S params E).ClosedN (params.length + S.indices.length) := by
    have hc := CtxWF.closed henv.ordered (T.indicesCtx S.indices.length (Nat.le_refl _))
    rw [List.take_length] at hc
    have := (W.majorTy_typed.closedN' henv.ordered.closed hc).1
    simpa [Nat.add_comm] using this
  have hΔg : OnCtx (params ++ S.indices ++ [majorTy S params E]).reverse (env.IsType U) := by
    have h1 := T.indicesCtx S.indices.length (Nat.le_refl _)
    rw [List.take_length] at h1
    rw [List.reverse_append]
    exact ⟨h1, _, W.majorTy_typed⟩
  have hgcl : ∀ i (h : i < (params ++ S.indices ++ [majorTy S params E]).length),
      ((params ++ S.indices ++ [majorTy S params E])[i]).ClosedN i := by
    intro i h
    by_cases hi : i < (params ++ S.indices).length
    · rw [List.getElem_append_left hi]
      exact T.prefix_closed (fun l h => T.scope.indices l h) i hi
    · have : i = (params ++ S.indices).length := by simp at h hi ⊢; omega
      subst this
      simpa using hmcl
  have hid := TelInst.ident (env := env) (U := U) [] hgcl
  simp only [List.append_nil, List.length_append, List.length_singleton] at hid
  have hsplit : bvarRange (params.length + S.indices.length + 1)
      (params.length + S.indices.length + 1) =
      genericPa S params ++ genericIa S ++ [.bvar 0] := by
    rw [bvarRange_append _ _ _ (Nat.le_refl _), bvarRange_append _ _ _ (by omega)]
    simp only [genericPa, genericIa, List.append_assoc]
    congr 2
    · simp [bvarRange]; intro a ha; omega
    · simp [bvarRange]
  rw [hsplit] at hid
  have hia : TelInst env U (params ++ S.indices ++ [majorTy S params E]).reverse
      (params ++ S.indices) (genericPa S params ++ genericIa S) := by
    have := hid.take (doms := params ++ S.indices) (more := [majorTy S params E])
    simpa [genericPa, genericIa, List.take_append, List.append_assoc,
      List.take_of_length_le] using this
  have hpa : TelInst env U (params ++ S.indices ++ [majorTy S params E]).reverse
      params (genericPa S params) := by
    have := hia.take (doms := params) (more := S.indices)
    simpa [genericPa] using this
  obtain ⟨hctx, _⟩ := tel_typed henv heq T hΔg hpa hia (by simp [genericIa]) j (Nat.le_of_lt hj)
  have hdom := step_domain_prop henv heq T hΔg hpa hia (by simp [genericIa]) hj
  exact HasType.wrapForalls_prop henv.ordered hctx hdom

/-- Instantiating the generic witness proposition at a constructor gives the
same telescope proposition built directly from the constructor's indices. -/
theorem stepBody_at_constructor (W : E.WF S params env U) :
    (S.stepBody (genericPa S params) (genericIa S) j).instOuter
      (branchPa S params ++ E.ctorIndices ++ [ctorApp S params E]) =
    S.stepBody (branchPa S params) E.ctorIndices j := by
  have hlenb : (branchPa S params ++ E.ctorIndices ++ [ctorApp S params E]).length =
      params.length + S.indices.length + 1 := by
    simp [branchPa, W.ctorIndices_length]; omega
  have hpaτ : (genericPa S params).map
      (fun x : VExpr => x.subst (VExpr.Subst.ofList (branchPa S params ++ E.ctorIndices ++ [ctorApp S params E]))) =
      branchPa S params := by
    have := VExpr.instOuter_bvarRange params.length (params.length + S.indices.length + 1)
      (branchPa S params ++ E.ctorIndices ++ [ctorApp S params E]) (by omega) (by rw [hlenb]; omega)
    simp only [← VExpr.instOuter_eq_subst]
    rw [genericPa, this, hlenb, Nat.sub_self, List.drop_zero, List.append_assoc,
      List.take_left' (by simp [branchPa])]
  have hiaτ : (genericIa S).map
      (fun x : VExpr => x.subst (VExpr.Subst.ofList (branchPa S params ++ E.ctorIndices ++ [ctorApp S params E]))) =
      E.ctorIndices := by
    have := VExpr.instOuter_bvarRange S.indices.length (S.indices.length + 1)
      (branchPa S params ++ E.ctorIndices ++ [ctorApp S params E]) (by omega) (by rw [hlenb]; omega)
    simp only [← VExpr.instOuter_eq_subst]
    rw [genericIa, this, hlenb, show params.length + S.indices.length + 1 - (S.indices.length + 1) =
      (branchPa S params).length by simp [branchPa], List.append_assoc, List.drop_left,
      ← W.ctorIndices_length, List.take_left' rfl]
  rw [instOuter_eq_subst,
    stepBody_subst (by simpa [genericPa] using W.typed.scope) (by simp [genericIa]), hpaτ, hiaτ]

/-- Both proof fields and data equality slots now have a closed, typed extractor.
Its argument telescope has arbitrary indices and a major at those indices; no
occurrence alignment or independently typed constructor fields are assumed. -/
theorem stepValue_typed (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hj : j < S.fields.length) :
    env.HasType U [] (stepValue S params E j)
      (typeOf S params E (S.stepBody (genericPa S params) (genericIa S) j)) := by
  apply valueOf_typed henv W (stepBody_prop henv heq W hj)
  rw [stepBody_at_constructor W]
  have T := W.typed
  have hΔ : OnCtx (params ++ S.fields).reverse (env.IsType U) := by
    simpa using T.fieldsCtx S.fields.length (Nat.le_refl _)
  have hpa : TelInst env U (params ++ S.fields).reverse params (branchPa S params) := by
    have := W.ctorIndices_typed.take (doms := params) (more := S.indices)
    simpa [branchPa] using this
  obtain ⟨hctx, _⟩ := tel_typed henv heq T hΔ hpa W.ctorIndices_typed W.ctorIndices_length j
    (Nat.le_of_lt hj)
  exact HasType.wrapLams_of hctx
    (stepWitness_typed henv heq T W.ctorIndices_typed W.ctorIndices_length W.slot_literal hj)

end PropElim
end Lean4Lean
