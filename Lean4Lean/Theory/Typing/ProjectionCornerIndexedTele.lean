import Lean4Lean.Theory.Typing.ProjectionCornerCase

/-! # Telescope instances under inserted binders, and the shape of a recursor type -/

namespace Lean4Lean
open VExpr

/-- Lifting an instantiation of a closed term at any cutoff lifts the arguments. -/
theorem VExpr.liftN_instOuter_at (X : VExpr) (args : List VExpr) (hX : X.ClosedN args.length)
    (n k : Nat) :
    (X.instOuter args).liftN n k = X.instOuter (args.map (·.liftN n k)) := by
  rw [← lift'_consN_skipN, instOuter_eq_subst, instOuter_eq_subst, lift'_subst]
  apply subst_congr_closedN hX
  intro i hi
  simp only [Subst.lift_r, Subst.ofList_lt _ hi, List.length_map,
    Subst.ofList_lt (args.map _) (by simpa using hi), List.getElem_map, lift'_consN_skipN]

namespace VEnv
variable {env : VEnv} {U : Nat}

/-- Weakening a telescope instance at any cutoff. -/
theorem TelInst.weakAt (henv : env.Ordered) {Γ Γ' doms args : List VExpr} {n k : Nat}
    (hcl : ∀ j (h : j < doms.length), (doms[j]).ClosedN j)
    (W : Ctx.LiftN n k Γ Γ') (H : TelInst env U Γ doms args) :
    TelInst env U Γ' doms (args.map (·.liftN n k)) := by
  refine ⟨by simp [H.1], fun j hj hj' => ?_⟩
  simp only [List.length_map] at hj
  have h := (H.2 j hj hj').weakN henv W
  rw [VExpr.liftN_instOuter_at _ _ (by simpa [Nat.min_eq_left (Nat.le_of_lt hj)] using hcl j hj')]
    at h
  simpa [List.map_take] using h

open InductiveSignature

theorem bvarRange_map_liftN_hi (n total m k : Nat) (h : m + n ≤ total) :
    (bvarRange n total).map (·.liftN k m) = bvarRange n (total + k) := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_map, bvarRange_getElem _ _ _ (by simpa using h1),
    bvarRange_getElem _ _ _ (by simpa using h2), VExpr.liftN, liftVar]
  rw [if_neg (by simp at h1; omega)]
  congr 1; simp at h1; omega

theorem bvarRange_map_liftN_lo (n m k : Nat) (h : n ≤ m) :
    (bvarRange n n).map (·.liftN k m) = bvarRange n n := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_map, bvarRange_getElem _ _ _ (by simpa using h1), VExpr.liftN, liftVar]
  rw [if_pos (by simp at h1; omega)]

private theorem insertBinders_len' (F : List VExpr) (e : Nat) :
    (insertBinders F e).length = F.length := by simp [insertBinders]

private theorem insertBinders_get' (F : List VExpr) (e i : Nat)
    (hi : i < (insertBinders F e).length) :
    (insertBinders F e)[i] = (F[i]'(by simpa [insertBinders_len'] using hi)).liftN e i := by
  simp [insertBinders, List.getElem_zipIdx]

theorem insertBinders_ctxLiftN (F X P : List VExpr) (e : Nat) (hX : X.length = e) :
    ∀ i, i ≤ F.length → Ctx.LiftN e i ((F.take i).reverse ++ P)
      (((insertBinders F e).take i).reverse ++ X ++ P)
  | 0, _ => by simpa using Ctx.LiftN.zero (Γ := P) X hX
  | i + 1, hi => by
    have h1 := insertBinders_ctxLiftN F X P e hX i (by omega)
    have hiF : i < F.length := by omega
    have e1 : (F.take (i + 1)).reverse ++ P = F[i] :: ((F.take i).reverse ++ P) := by
      rw [List.take_add_one, List.getElem?_eq_getElem hiF, Option.toList_some,
        List.reverse_append, List.reverse_singleton, List.singleton_append, List.cons_append]
    have e2 : ((insertBinders F e).take (i + 1)).reverse ++ X ++ P =
        F[i].liftN e i :: (((insertBinders F e).take i).reverse ++ X ++ P) := by
      rw [List.take_add_one, List.getElem?_eq_getElem (show i < (insertBinders F e).length by
        rw [insertBinders_len']; omega), insertBinders_get']
      simp
    rw [e1, e2]
    exact .succ h1

/-- **The shape of a one-family, one-constructor recursor type into `Prop` is a type**, given
that the family telescope is a well-formed context and the minor premise is a type under the
motive. -/
theorem IsType.recursorShape (henv : env.WF) {P I : List VExpr} {Maj Min : VExpr}
    (hidx : OnCtx (P ++ I ++ [Maj]).reverse (env.IsType U))
    (hMin : env.IsType U (VExpr.wrapForalls (I ++ [Maj]) (.sort .zero) :: P.reverse) Min) :
    env.IsType U [] (VExpr.wrapForalls (P ++ [VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] ++
        [Min] ++ insertBinders I 2 ++ [Maj.liftN 2 I.length])
      (VExpr.mkApps (.bvar (I.length + 2)) (vars I.length 1 ++ [.bvar 0]))) := by
  have hP : OnCtx P.reverse (env.IsType U) := by
    have h := hidx
    rw [List.append_assoc, List.reverse_append] at h
    exact OnCtx.of_append h
  have hMotT : env.IsType U P.reverse (VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)) :=
    IsType.wrapForalls_of (by simpa [List.reverse_append, List.append_assoc] using hidx)
      ⟨_, HasType.sort (by trivial)⟩
  have hins : insertBinders (I ++ [Maj]) 2 = insertBinders I 2 ++ [Maj.liftN 2 I.length] := by
    simp [insertBinders, List.zipIdx_append]
  have hC := OnCtx.insert_binders henv.ordered (F := I ++ [Maj])
    (X := [Min, VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)]) (Γ := P.reverse)
    (by simpa [List.reverse_append, List.append_assoc] using hidx) ⟨⟨hP, hMotT⟩, hMin⟩
  have hC' : OnCtx ((insertBinders (I ++ [Maj]) 2).reverse ++
      [Min, VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] ++ P.reverse) (env.IsType U) := hC
  -- the telescope `P ++ I ++ [Maj]` at the variables of the full context
  have hcl := OnCtx.closed_reverse henv.ordered hidx
  have hId := TelInst.ident (env := env) (U := U) [] hcl
  simp only [List.append_nil] at hId
  have hW := insertBinders_ctxLiftN (I ++ [Maj])
    [Min, VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] P.reverse 2 rfl (I ++ [Maj]).length
    (Nat.le_refl _)
  rw [List.take_length,
    List.take_of_length_le (by rw [insertBinders_len']; exact Nat.le_refl _)] at hW
  have hW' : Ctx.LiftN 2 (I.length + 1) (P ++ I ++ [Maj]).reverse
      ((insertBinders (I ++ [Maj]) 2).reverse ++
        [Min, VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] ++ P.reverse) := by
    simpa [List.reverse_append, List.append_assoc] using hW
  have hT := TelInst.weakAt henv.ordered hcl hW' hId
  have hsplit : bvarRange (P ++ I ++ [Maj]).length (P ++ I ++ [Maj]).length =
      bvarRange P.length (P.length + (I.length + 1)) ++ bvarRange (I.length + 1) (I.length + 1) := by
    rw [show (P ++ I ++ [Maj]).length = P.length + (I.length + 1) by simp [Nat.add_assoc]]
    exact CastSpec.bvarRange_split _ _
  rw [hsplit, List.map_append, bvarRange_map_liftN_hi _ _ _ _ (by omega),
    bvarRange_map_liftN_lo _ _ _ (Nat.le_refl _)] at hT
  have hT' : TelInst env U ((insertBinders (I ++ [Maj]) 2).reverse ++
      [Min, VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] ++ P.reverse) (P ++ (I ++ [Maj]))
      (bvarRange P.length (P.length + (I.length + 3)) ++ bvarRange (I.length + 1) (I.length + 1)) := by
    rw [show P.length + (I.length + 3) = P.length + (I.length + 1) + 2 by omega]
    simpa only [List.append_assoc] using hT
  have hDcl : ∀ j (h : j < (I ++ [Maj]).length), ((I ++ [Maj])[j]).ClosedN (P.length + j) := by
    intro j h
    have := hcl (P.length + j) (by simp at h ⊢; omega)
    simpa [List.append_assoc, List.getElem_append_right] using this
  have hU := TelInst.unlift hDcl rfl hT'
  -- the motive variable
  have hlook := Lookup.reverse_append
    (P ++ [VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] ++ [Min] ++ insertBinders (I ++ [Maj]) 2)
    [] P.length (by simp)
  have hctxEq : (P ++ [VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] ++ [Min] ++
      insertBinders (I ++ [Maj]) 2).reverse ++ [] =
      (insertBinders (I ++ [Maj]) 2).reverse ++
        [Min, VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] ++ P.reverse := by simp
  rw [hctxEq] at hlook
  simp only [List.length_append, List.length_singleton, insertBinders_len', List.length_cons,
    List.length_nil] at hlook
  rw [List.getElem_append_left (by simp), List.getElem_append_left (by simp),
    List.getElem_append_right (by simp)] at hlook
  simp only [List.length_singleton, Nat.sub_self, List.getElem_singleton] at hlook
  have hmot : env.HasType U ((insertBinders (I ++ [Maj]) 2).reverse ++
      [Min, VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] ++ P.reverse) (.bvar (I.length + 2))
      (VExpr.wrapForalls ((I ++ [Maj]).mapIdx fun l d => d.liftN (I.length + 3) l) (.sort .zero)) := by
    simp only [Nat.zero_add] at hlook
    have h := HasType.bvar (env := env) (U := U) hlook
    rw [show P.length + 1 + 1 + (I.length + 1) - 1 - P.length = I.length + 2 by omega,
      show P.length + 1 + 1 + (I.length + 1) - P.length = I.length + 3 by omega,
      liftN_wrapForalls] at h
    simpa [VExpr.liftN] using h
  have hbody := HasType.mkApps_of_tel henv hC' hmot hU
  have hv : vars I.length 1 ++ [VExpr.bvar 0] = bvarRange (I.length + 1) (I.length + 1) := by
    rw [vars_eq_bvarRange, CastSpec.bvarRange_append I.length 1 _ (by omega)]
    simp [bvarRange]
  rw [hv, show P ++ [VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] ++ [Min] ++ insertBinders I 2 ++
      [Maj.liftN 2 I.length] = P ++ [VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] ++ [Min] ++
        insertBinders (I ++ [Maj]) 2 by rw [hins]; simp]
  refine IsType.wrapForalls_of (by simpa [List.reverse_append, List.append_assoc] using hC')
    ⟨.zero, ?_⟩
  simpa [List.reverse_append, List.append_assoc] using hbody

end VEnv
end Lean4Lean
