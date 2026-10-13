import Lean4Lean.Theory.Typing.Strengthening.SingletonPropElimination

/-! # Propositional witnesses for singleton reconstruction steps

Every cast-telescope domain is a proposition, including the equality domains of
data slots. At a constructor occurrence, those domains have canonical witnesses.
These are the motives and branches needed to extract witnesses from an arbitrary
major, without supplying reflexivity at unaligned occurrence endpoints.
-/
namespace Lean4Lean
open VExpr VEnv

namespace VEnv
/-- Any well-formed application of canonical Eq is a proposition, regardless
of its supplied typing. -/
theorem eqApp_prop_of_wf (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (H : VExpr.WF env U Γ (eqApp u A a b)) :
    env.HasType U Γ (eqApp u A a b) (.sort .zero) := by
  have H' : VExpr.WF env U Γ (mkApps (.const ``Eq [u]) [A, a, b]) := H
  obtain ⟨_, hc⟩ := VExpr.WF.of_mkApps henv hΓ H'
  obtain ⟨ci, hci, hw, _⟩ := HasType.const_inv henv hΓ hc
  rw [heq.1] at hci
  cases Option.some.inj hci
  have hh := HasType.const (Γ := Γ) heq.1 hw (by rfl)
  obtain ⟨res, ht, hr⟩ := HasType.mkApps_telescope henv hΓ hh H' (by rfl)
  cases ht with | cons hA ht =>
  cases ht with | cons ha ht =>
  cases ht with | cons hb ht =>
  cases ht
  simpa [eqApp, instL, VLevel.inst, inst, instVar, liftN] using hr
end VEnv

namespace SingletonLayout
variable {S : SingletonLayout}

/-- All domains of the reconstruction telescope are propositions: proof fields
by their declaration sort, and data-slot constraints because they are Eq types. -/
theorem step_domain_prop (henv : env.WF) (heq : env.HasCanonicalEq)
    (T : S.Typed env U params) (hΔ : OnCtx Δ (env.IsType U))
    (hpa : TelInst env U Δ params pa)
    (hia : TelInst env U Δ (params ++ S.indices) (pa ++ ia))
    (hialen : ia.length = S.indices.length) (hi : i < S.fields.length) :
    env.HasType U ((S.tel pa ia i).1.reverse ++ Δ)
      (S.step pa ia i (S.tel pa ia i).2).1 (.sort .zero) := by
  obtain ⟨hctx, hinst⟩ := tel_typed henv heq T hΔ hpa hia hialen i (Nat.le_of_lt hi)
  cases hs : S.slot.getD i none with
  | none =>
    have ht := HasType.closed_instOuter henv (T.fieldsCtx i (Nat.le_of_lt hi)) (T.fieldSort i hi) hinst
    simp only [step, hs]
    simpa only [fieldSort, hs, getD_of_lt hi, instOuter_sort] using ht
  | some k =>
    obtain ⟨hnext, _⟩ := tel_typed henv heq T hΔ hpa hia hialen (i + 1) hi
    simp only [tel, List.reverse_append, List.reverse_singleton, List.cons_append] at hnext
    obtain ⟨_, ht⟩ := hnext.2
    simp only [step, hs] at ht ⊢
    exact eqApp_prop_of_wf henv heq hctx ⟨_, ht⟩

/-- A constructor-branch witness for the next telescope domain. Proof slots
return their field variable; data slots return reflexivity at the index type. -/
def stepWitness (S : SingletonLayout) (pa ia : List VExpr) (i : Nat) : VExpr :=
  match S.slot.getD i none with
  | none => .bvar (S.fields.length - 1)
  | some k => eqReflApp (.succ (S.sorts.getD i .zero)) (.sort (S.sorts.getD i .zero))
      ((S.indices.getD k default).instOuter
        (pa.map (fun x => x.liftN i) ++ (ia.take k).map (fun x => x.liftN i)))

/-- At the constructor's own indices, the next telescope proposition has a
witness below all earlier cast assumptions. Endpoint conversion follows from
two typings of the same literal field variable, not from an occurrence check. -/
theorem stepWitness_typed (henv : env.WF) (heq : env.HasCanonicalEq)
    (T : S.Typed env U params)
    (hci : TelInst env U (params ++ S.fields).reverse (params ++ S.indices)
      (PropElim.branchPa S params ++ ci))
    (hcil : ci.length = S.indices.length)
    (hlit : ∀ l k, S.slot.getD l none = some k →
      ci.getD k default = .bvar (S.fields.length - 1 - l))
    (hi : i < S.fields.length) :
    env.HasType U ((S.tel (PropElim.branchPa S params) ci i).1.reverse ++ (params ++ S.fields).reverse)
      (S.stepWitness (PropElim.branchPa S params) ci i)
      (S.step (PropElim.branchPa S params) ci i (S.tel (PropElim.branchPa S params) ci i).2).1 := by
  have hΔ : OnCtx (params ++ S.fields).reverse (env.IsType U) := by
    simpa using T.fieldsCtx S.fields.length (Nat.le_refl _)
  have hpa : TelInst env U (params ++ S.fields).reverse params (PropElim.branchPa S params) := by
    have := hci.take (doms := params) (more := S.indices)
    simpa [PropElim.branchPa] using this
  obtain ⟨hctx, hinst⟩ := tel_typed henv heq T hΔ hpa hci hcil i (Nat.le_of_lt hi)
  have hfv := tel_branch_target henv heq T hci hcil hlit i hi
  have hvshape : (VExpr.bvar (S.fields.length - 1 - i)).liftN i = .bvar (S.fields.length - 1) := by
    simp only [VExpr.liftN, liftVar_base']; congr 1; omega
  cases hs : S.slot.getD i none with
  | none =>
    simp only [stepWitness, step, hs]
    simpa only [target, hvshape, PropElim.branchPa] using hfv
  | some k =>
    have hk := T.scope.slot_lt i k hs
    have hidx := hci.getD (j := params.length + k) (by simp; omega)
    unfold PropElim.branchPa at hidx
    rw [getD_append_right' (by simp), getD_append_right' (by omega)] at hidx
    simp only [bvarRange_length, Nat.add_sub_cancel_left, List.take_append] at hidx
    rw [List.take_of_length_le (by simp only [bvarRange_length]; omega)] at hidx
    rw [hlit i k hs] at hidx
    have hidx' := hidx.weakN henv.ordered (Ctx.LiftN.zero (S.tel (PropElim.branchPa S params) ci i).1.reverse)
    simp only [List.length_reverse, (S.tel_length _ _ i).1] at hidx'
    have hXlift : ((S.indices.getD k default).instOuter
        (PropElim.branchPa S params ++ ci.take k)).liftN i =
        (S.indices.getD k default).instOuter
          ((PropElim.branchPa S params).map (fun x => x.liftN i) ++
            (ci.take k).map (fun x => x.liftN i)) := by
      rw [VExpr.liftN_instOuter _ _ (by
        simpa [PropElim.branchPa, hcil, Nat.min_eq_left (Nat.le_of_lt hk)] using T.scope.indices_getD k),
        List.map_append]
    simp only [PropElim.branchPa] at hXlift
    rw [hvshape, hXlift] at hidx'
    rw [hvshape] at hfv
    have hY := HasType.closed_instOuter henv (T.fieldsCtx i (Nat.le_of_lt hi)) (T.fieldSort i hi) hinst
    have hsort : S.fieldSort i = S.sorts.getD i .zero := by simp only [fieldSort, hs]
    simp only [instOuter_sort, hsort] at hY
    have hXY := (hidx'.uniqU henv hctx hfv).of_r henv hctx (by
      simpa only [target, getD_of_lt hi, PropElim.branchPa] using hY)
    have hu := T.sortWF i
    have hproof := (IsDefEq.eqApp_r heq (show (VLevel.succ (S.sorts.getD i .zero)).WF U from hu)
      (.sort hu) hXY.hasType.1 hXY).defeq
      (HasType.eqReflApp heq (show (VLevel.succ (S.sorts.getD i .zero)).WF U from hu)
        (.sort hu) hXY.hasType.1)
    simp only [stepWitness, step, hs]
    simpa only [target, PropElim.branchPa] using hproof

end SingletonLayout
end Lean4Lean
