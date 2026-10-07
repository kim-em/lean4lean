import Lean4Lean.Theory.Typing.NativeSingletonTyping

/-! # Substitution identities for instantiating a minor premise at actual parameters

The projection-walk corner applies a recursor to parameters, a motive and a minor premise in an
arbitrary context. These lemmas compute the generated minor premise's type instantiated at the
actual parameters and motive, as a substitution. -/

namespace Lean4Lean
namespace VExpr

theorem Subst.lift_liftN (σ : Subst) : ∀ i, σ.lift.liftN i = σ.liftN (i + 1)
  | 0 => rfl
  | i + 1 => by
    show (σ.lift.liftN i).lift = (σ.liftN (i + 1)).lift
    rw [Subst.lift_liftN σ i]

theorem subst_wrapForalls (σ : Subst) : ∀ (ds : List VExpr) (b : VExpr),
    (wrapForalls ds b).subst σ =
      wrapForalls (ds.mapIdx fun i d => d.subst (σ.liftN i)) (b.subst (σ.liftN ds.length))
  | [], b => rfl
  | d :: ds, b => by
    have ih := subst_wrapForalls σ.lift ds b
    show VExpr.forallE (d.subst σ) ((wrapForalls ds b).subst σ.lift) = _
    rw [ih, List.mapIdx_cons]
    simp only [Subst.lift_liftN, List.length_cons]
    rfl

/-- Substituting under a binder inserted at depth `i` skips the substitution's head. -/
theorem liftN_one_subst_liftN (d : VExpr) (σ : Subst) (i : Nat) :
    (d.liftN 1 i).subst (σ.liftN i) = d.subst (σ.tail.liftN i) := by
  rw [liftN_subst]
  congr 1; funext v
  simp only [Subst.lift_l, Lift.liftVar_consN_skipN, Subst.liftN_apply, Subst.tail, liftVar]
  by_cases hv : v < i
  · simp [hv]
  · rw [if_neg hv, if_neg (by omega), if_neg hv]
    congr 2; omega

theorem liftN_subst_liftN_add (X : VExpr) (τ : Subst) (f h : Nat) :
    (X.liftN h).subst (τ.liftN (f + h)) = (X.subst (τ.liftN f)).liftN h := by
  rw [liftN_eq_subst X h, liftN_eq_subst _ h, subst_subst, subst_subst]
  congr 1; funext v
  simp only [Subst.comp, Subst.shift, subst_bvar, Subst.liftN_apply]
  by_cases hv : v < f
  · rw [if_pos (by omega), if_pos hv]; rfl
  · rw [if_neg (by omega), if_neg hv, ← liftN_eq_subst, liftN_liftN]
    congr 2; omega

theorem Subst.ofList_snoc_zero (ps : List VExpr) (M : VExpr) :
    Subst.ofList (ps ++ [M]) 0 = M := by
  simp [Subst.ofList]

/-- Instantiating the parameters, lifted past `n` new binders, and the first `i` of those
binders, is substituting the parameters beneath `i` binders and lifting past the rest. -/
theorem instOuter_params_bvarRange {X : VExpr} {ps : List VExpr} {i n : Nat}
    (hX : X.ClosedN (ps.length + i)) (hi : i ≤ n) :
    X.instOuter (ps.map (·.liftN n) ++ bvarRange i n) =
      (X.subst ((Subst.ofList ps).liftN i)).liftN (n - i) := by
  rw [instOuter_eq_subst, liftN_eq_subst _ (n - i), subst_subst]
  apply subst_congr_closedN hX
  intro v hv
  have hlen : (ps.map (·.liftN n) ++ bvarRange i n).length = ps.length + i := by simp
  rw [Subst.ofList_lt _ (by omega)]
  simp only [Subst.comp, Subst.liftN_apply, hlen]
  by_cases hvi : v < i
  · rw [if_pos hvi, List.getElem_append_right (by simp; omega)]
    simp only [subst_bvar, Subst.shift, List.length_map]
    rw [bvarRange_getElem _ _ _ (by omega)]
    congr 1; omega
  · rw [if_neg hvi, List.getElem_append_left (by simp; omega), Subst.ofList_lt _ (by omega)]
    simp only [List.getElem_map, ← liftN_eq_subst, liftN_liftN]
    have e1 : i + (n - i) = n := by omega
    have e2 : ps.length + i - 1 - v = ps.length - 1 - (v - i) := by omega
    simp only [e1, e2]

/-- A generated minor premise without constructor indices, instantiated at the parameters and
the motive. -/
theorem minor_instOuter (F Hs ps : List VExpr) (C M : VExpr) :
    (wrapForalls (InductiveSignature.insertBinders F 1 ++ Hs)
      (mkApps (.bvar (F.length + Hs.length))
        [(C.liftN Hs.length).liftN 1 (F.length + Hs.length)])).instOuter (ps ++ [M]) =
    wrapForalls (F.mapIdx (fun i d => d.subst ((Subst.ofList ps).liftN i)) ++
        Hs.mapIdx (fun k d => d.subst ((Subst.ofList (ps ++ [M])).liftN (F.length + k))))
      ((VExpr.app (M.liftN F.length) (C.subst ((Subst.ofList ps).liftN F.length))).liftN
        Hs.length) := by
  rw [instOuter_eq_subst, subst_wrapForalls, VEnv.insertBinders_eq_mapIdx, List.mapIdx_append,
    List.mapIdx_mapIdx]
  simp only [Function.comp_def, liftN_one_subst_liftN, Subst.ofList_snoc_tail, List.length_append,
    List.length_mapIdx]
  congr 1
  · congr 2; funext k d; rw [Nat.add_comm]
  · show (VExpr.app (.bvar (F.length + Hs.length)) _).subst _ = _
    rw [subst_app, subst_bvar, Subst.liftN_apply, if_neg (Nat.lt_irrefl _), Nat.sub_self,
      Subst.ofList_snoc_zero, liftN_one_subst_liftN, Subst.ofList_snoc_tail,
      liftN_subst_liftN_add]
    show _ = VExpr.app _ _
    rw [liftN_liftN]

end VExpr
end Lean4Lean
