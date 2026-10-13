import Lean4Lean.Theory.Typing.Confluence.SingletonCoverage

/-! # Singleton reconstruction without a pre-existing field instance

When all singleton fields are proofs, extraction can be typed directly from the
major. No independently supplied constructor fields or index alignment are needed
for this part. For an unindexed singleton, this yields the actual constructor
at the major's type and hence a typed reconstruction equation.
-/
namespace Lean4Lean.VEnv.Strengthening.SingletonProof
open _root_.Lean4Lean _root_.Lean4Lean.VExpr SingletonLayout PropElim
variable {S : SingletonLayout} {E : PropElim} {P ps idx t : List VExpr} {env : VEnv}

/-- With no data slots, the instantiated cast substitution is its argument list. -/
theorem substHat_proofs
    (hs : ∀ j, j < S.fields.length → S.slot.getD j none = none)
    (hi : i ≤ S.fields.length) (ht : t.length = i) : S.substHat ps idx i t = t := by
  induction i generalizing t with
  | zero => simp only [List.length_eq_zero_iff] at ht; subst t; rfl
  | succ i ih =>
    simp only [substHat, valHat, hs i (by omega)]
    rw [ih (by omega) (by simp [ht])]
    have hj : i < t.length := by omega
    rw [getD_of_lt hj]
    have htake := List.take_add_one (l := t) (i := i)
    rw [List.getElem?_eq_getElem hj] at htake
    simpa only [← ht, List.take_length, Option.toList_some] using htake.symm

/-- Proof extraction uses the same values as cast arguments and as fields. -/
theorem occ_proofs
    (hs : ∀ j, j < S.fields.length → S.slot.getD j none = none)
    (hi : i ≤ S.fields.length) :
    (occ S P E ps idx m i).1 = (occ S P E ps idx m i).2 := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [occ, hs i (by omega), ih (by omega)]

/-- The extraction typing part of `PropElim.occ_typed` needs no original field
instance when every slot is a proof. The proof specializes its proof-field step,
using the identity cast substitution instead of comparison with supplied fields. -/
theorem occ_typed (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S P env U) (hpsl : ps.length = P.length)
    (hs : ∀ j, j < S.fields.length → S.slot.getD j none = none)
    (hargs : TelInst env U Γ (P ++ S.indices ++ [majorTy S P E]) (ps ++ idx ++ [m])) :
    ∀ i, i ≤ S.fields.length →
      TelInst env U Γ (S.tel ps idx i).1 (occ S P E ps idx m i).1 ∧
      TelInst env U Γ (P ++ S.fields.take i) (ps ++ (occ S P E ps idx m i).2) := by
  have T := W.typed
  have hidxl : idx.length = S.indices.length := by
    have h := hargs.1
    simp only [List.length_append, List.length_singleton] at h
    omega
  have hpsT : TelInst env U Γ P ps := by
    have := (show TelInst env U Γ (P ++ (S.indices ++ [majorTy S P E]))
      (ps ++ (idx ++ [m])) by simpa [List.append_assoc] using hargs).take
    simpa [hpsl] using this
  intro i
  induction i with
  | zero => intro _; exact ⟨by simpa [tel, occ] using TelInst.nil, by simpa [occ] using hpsT⟩
  | succ i ih =>
    intro hi
    have hi' : i < S.fields.length := hi
    obtain ⟨h1, h2⟩ := ih (Nat.le_of_lt hi')
    have hsame := occ_proofs (P := P) (E := E) (ps := ps) (idx := idx) (m := m) hs (Nat.le_of_lt hi')
    rw [← hsame] at h2
    generalize ht : (occ S P E ps idx m i).1 = t at h1 h2 hsame
    have htl : t.length = i := ht ▸ (occ_length S P E ps idx m i).1
    have hσ : S.substHat ps idx i t = t := substHat_proofs hs (Nat.le_of_lt hi') htl
    have hval := value_typed P henv heq W hi' (hs i hi')
    have hvalΓ := hval.weak0 henv.ordered (Γ := Γ)
    unfold valueType at hvalΓ
    rw [← VExpr.wrapForalls_append] at hvalΓ
    have hbl : (ps ++ idx ++ [m]).length = P.length + S.indices.length + 1 := by
      simp [hpsl, hidxl]; omega
    have hpaτ : (genericPa S P).map
        (fun x : VExpr => x.subst (VExpr.Subst.ofList (ps ++ idx ++ [m]))) = ps := by
      have := VExpr.instOuter_bvarRange P.length (P.length + S.indices.length + 1)
        (ps ++ idx ++ [m]) (by omega) (by rw [hbl]; exact Nat.le_refl _)
      simp only [← VExpr.instOuter_eq_subst]
      rw [genericPa, this, hbl, Nat.sub_self, List.drop_zero, List.append_assoc,
        List.take_left' hpsl]
    have hiaτ : (genericIa S).map
        (fun x : VExpr => x.subst (VExpr.Subst.ofList (ps ++ idx ++ [m]))) = idx := by
      have := VExpr.instOuter_bvarRange S.indices.length (S.indices.length + 1)
        (ps ++ idx ++ [m]) (by omega) (by rw [hbl]; omega)
      simp only [← VExpr.instOuter_eq_subst]
      rw [genericIa, this, hbl, show P.length + S.indices.length + 1 - (S.indices.length + 1) =
        ps.length by omega, List.append_assoc, List.drop_left, List.take_left' hidxl]
    have hscope : S.Scoped (genericPa S P).length := by simpa [genericPa] using T.scope
    have hgia : (genericIa S).length = S.indices.length := by simp [genericIa]
    have htelS := (tel_subst hscope hgia (VExpr.Subst.ofList (ps ++ idx ++ [m])) i).1
    rw [hpaτ, hiaτ] at htelS
    have hglen := (S.tel_length (genericPa S P) (genericIa S) i).1
    have hargsT : TelInst env U Γ
        ((P ++ S.indices ++ [majorTy S P E]) ++ (S.tel (genericPa S P) (genericIa S) i).1)
        ((ps ++ idx ++ [m]) ++ t) := by
      apply TelInst.append hargs (by rw [htl, hglen])
      intro j hj
      rw [hglen] at hj
      have hj' := h1.getD (j := j) (by rw [(S.tel_length ps idx i).1]; exact hj)
      rw [instOuter_append_split, show (t.take j).length = j by simp; omega]
      have hd : ((S.tel (genericPa S P) (genericIa S) i).1.getD j default).subst
          ((VExpr.Subst.ofList (ps ++ idx ++ [m])).liftN j) = (S.tel ps idx i).1.getD j default := by
        rw [← htelS, getD_of_lt (by rw [hglen]; omega), getD_of_lt (by rw [List.length_mapIdx, hglen]; omega),
          List.getElem_mapIdx]
      rw [hd]
      exact hj'
    have hci := HasType.mkApps_of_tel hvalΓ hargsT
    rw [instOuter_append_split, htl, target_subst hscope hgia, hpaτ, hiaτ,
      target_instOuter (T.scope.mono_pa hpsl) hidxl i t htl, hσ] at hci
    generalize hcid : VExpr.mkApps (value S P E i) (ps ++ idx ++ [m] ++ t) = ci at hci
    have hocc : occ S P E ps idx m (i + 1) = (t ++ [ci], t ++ [ci]) := by
      simp only [occ, ht, ← hsame, hs i hi', hcid]
    rw [hocc]
    have htel : (S.tel ps idx (i + 1)).1 =
        (S.tel ps idx i).1 ++ [(S.step ps idx i (S.tel ps idx i).2).1] := by simp [tel]
    have hdom : ((S.step ps idx i (S.tel ps idx i).2).1).instOuter t =
        S.domHat ps idx i (S.substHat ps idx i t) := by
      have := tel_dom_instOuter (T.scope.mono_pa hpsl) hidxl (i + 1) i (by omega) t htl
      rwa [htel, getD_append_right' (by rw [(S.tel_length _ _ i).1]; exact Nat.le_refl _),
        (S.tel_length _ _ i).1, Nat.sub_self] at this
    refine ⟨?_, ?_⟩
    · rw [htel]
      apply h1.append_one
      rw [hdom, hσ, domHat, hs i hi']
      exact hci
    · have hfields : P ++ S.fields.take (i + 1) = (P ++ S.fields.take i) ++ [S.fields[i]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi']; simp
      rw [hfields]
      rw [getD_of_lt (l := S.fields) hi'] at hci
      simpa only [List.append_assoc] using h2.append_one hci

/-- An unindexed singleton's well-scoped layout has no data slots. -/
theorem slots_none (W : E.WF S P env U) (hn : S.indices = []) (j : Nat) :
    S.slot.getD j none = none := by
  cases hs : S.slot.getD j none with
  | none => rfl
  | some k => have h := W.typed.scope.slot_lt j k hs; simp [hn] at h

/-- For an unindexed singleton, any typed major reconstructs to its constructor.
No original field instance or alignment premise is supplied. -/
theorem unindexed_eta (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S P env U) (hn : S.indices = [])
    (hΓ : OnCtx Γ (env.IsType U)) (hpsl : ps.length = P.length)
    (hargs : TelInst env U Γ (P ++ S.indices ++ [majorTy S P E]) (ps ++ [] ++ [m])) :
    env.IsDefEq U Γ m
      (VExpr.mkApps E.ctor (ps ++ (occ S P E ps [] m S.fields.length).2))
      ((majorTy S P E).instOuter (ps ++ [])) := by
  have hf := (occ_typed henv heq W hpsl (fun j _ => slots_none W hn j) hargs
    S.fields.length (Nat.le_refl _)).2
  rw [List.take_length] at hf
  exact PropElim.singleton_eta P henv heq W hΓ hpsl hargs hf
    (fun l k hs => by rw [slots_none W hn l] at hs; contradiction)
    (fun k hk => by simp [hn] at hk)

end Lean4Lean.VEnv.Strengthening.SingletonProof
