import Lean4Lean.Theory.Typing.ProjectionCornerIndexedType

/-! # Substitution identities for an indexed minor premise and motive -/

namespace Lean4Lean
namespace VExpr

/-- A minor premise without induction hypotheses, whose motive is applied to constructor
indices and the constructor application, instantiated at the parameters and the motive. -/
theorem minor_instOuter_idx (F CI ps : List VExpr) (C M : VExpr) :
    (wrapForalls (InductiveSignature.insertBinders F 1)
      (mkApps (.bvar F.length)
        (CI.map (fun e => e.liftN 1 F.length) ++ [C.liftN 1 F.length]))).instOuter (ps ++ [M]) =
    wrapForalls (F.mapIdx (fun i d => d.subst ((Subst.ofList ps).liftN i)))
      (mkApps (M.liftN F.length)
        (CI.map (fun e => e.subst ((Subst.ofList ps).liftN F.length)) ++
          [C.subst ((Subst.ofList ps).liftN F.length)])) := by
  rw [instOuter_eq_subst, subst_wrapForalls, VEnv.insertBinders_eq_mapIdx, List.mapIdx_mapIdx]
  simp only [Function.comp_def, liftN_one_subst_liftN, Subst.ofList_snoc_tail, List.length_mapIdx]
  congr 1
  rw [subst_mkApps, subst_bvar, Subst.liftN_apply, if_neg (Nat.lt_irrefl _), Nat.sub_self,
    Subst.ofList_snoc_zero]
  simp [List.map_append, Function.comp_def, liftN_one_subst_liftN, Subst.ofList_snoc_tail]

/-- Substituting the parameters beneath `k` binders, then instantiating those binders, is
instantiating at the parameters followed by the arguments. -/
theorem subst_liftN_instOuter {d : VExpr} {ps bs : List VExpr}
    (hd : d.ClosedN (ps.length + bs.length)) :
    (d.subst ((Subst.ofList ps).liftN bs.length)).instOuter bs = d.instOuter (ps ++ bs) := by
  rw [instOuter_eq_subst, instOuter_eq_subst, subst_subst]
  apply subst_congr_closedN hd
  intro i hi
  simp only [Subst.comp, Subst.liftN_apply]
  by_cases hib : i < bs.length
  · rw [if_pos hib, subst_bvar, Subst.ofList_lt _ hib, Subst.ofList_lt _ (by simp; omega),
      List.getElem_append_right (by simp; omega)]
    congr 1; simp; omega
  · rw [if_neg hib, Subst.ofList_lt _ (by omega), ← instOuter_eq_subst,
      instOuter_liftN, Subst.ofList_lt _ (by simp; omega), List.getElem_append_left (by simp; omega)]
    congr 1; simp; omega

/-- The motive into `Prop` at the parameters. -/
theorem motive_instOuter_idx (D ps : List VExpr) :
    (wrapForalls D (.sort .zero)).instOuter ps =
      wrapForalls (D.mapIdx fun k d => d.subst ((Subst.ofList ps).liftN k)) (.sort .zero) := by
  rw [instOuter_eq_subst, subst_wrapForalls]
  rfl

end VExpr
end Lean4Lean
