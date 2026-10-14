import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProjectionTemplate
import Lean4Lean.Theory.Typing.Strengthening.ProofShapeRetraction
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageSubstitution

/-! # Raw transport of closed erased templates

Instantiated templates commute with arbitrary raw substitution when their capture
list covers the original scope. This applies even when some captures are proof
markers or deliberately retained raw projection images.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Erased scoped syntax sees only the substitution images in its original scope. -/
theorem proofErase_subst_agree (hc : e.ClosedN k) {σ τ : ProofShape.Subst}
    (H : ∀ i, i < k → σ i = τ i) : (proofErase Γ e).subst σ = (proofErase Γ e).subst τ := by
  induction e generalizing Γ k σ τ with
  | bvar i =>
    simp only [proofErase]
    split
    · rfl
    · exact H i hc
  | sort | const => simp only [proofErase]; split <;> rfl
  | app f a ihf iha =>
    simp only [proofErase]
    split
    · rfl
    · simp only [ProofShape.subst, ihf hc.1 H, iha hc.2 H]
  | proj s i m ih =>
    simp only [proofErase]
    split
    · rfl
    · simp only [ProofShape.subst, ih hc H]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    have HB : ∀ i, i < k+1 → σ.lift i = τ.lift i := by
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp only [ProofShape.Subst.lift, H i (by omega)]
    simp only [proofErase]
    split
    · rfl
    · simp only [ProofShape.subst, ihA hc.1 H, ihb hc.2 HB]

/-- Substitution acts only on the captures of an erased closed telescope body. -/
theorem proofErase_instOuter_subst (hc : e.ClosedN args.length) :
    ((proofErase Γ e).instOuter args).subst σ =
      (proofErase Γ e).instOuter (args.map (·.subst σ)) := by
  simp only [ProofShape.instOuter, ProofShape.subst_subst]
  apply proofErase_subst_agree hc
  intro i hi
  simp only [ProofShape.Subst.comp, ProofShape.Subst.ofList, List.length_map,
    dif_pos hi, List.getElem_map]

/-- General thinning of a template instance renames only its captures. -/
theorem proofErase_instOuter_lift' (hc : e.ClosedN args.length) :
    ((proofErase Γ e).instOuter args).lift' ρ =
      (proofErase Γ e).instOuter (args.map (·.lift' ρ)) := by
  rw [ProofShape.lift'_eq_subst, proofErase_instOuter_subst hc]
  simp only [← ProofShape.lift'_eq_subst]

/-- Block insertion is the corresponding template-capture renaming. -/
theorem proofErase_instOuter_liftN (hc : e.ClosedN args.length) :
    ((proofErase Γ e).instOuter args).liftN n k =
      (proofErase Γ e).instOuter (args.map (·.liftN n k)) := by
  simpa only [ProofShape.lift'_consN_skipN] using
    (proofErase_instOuter_lift' (Γ := Γ) (ρ := .consN (.skipN .refl n) k) hc)

namespace ProofShape
omit [Params] in
/-- Substitution preserves the preceding-field recipe without a proofness mask. -/
theorem projectionArgs_subst :
    (projectionArgs s ps m i).map (·.subst σ) =
      projectionArgs s (ps.map (·.subst σ)) (m.subst σ) i := by
  simp only [projectionArgs, List.map_append, List.map_map, Function.comp_def, subst]

omit [Params] in
/-- Arbitrary thinning preserves the preceding-field recipe. -/
theorem projectionArgs_lift' :
    (projectionArgs s ps m i).map (·.lift' ρ) =
      projectionArgs s (ps.map (·.lift' ρ)) (m.lift' ρ) i := by
  simp only [projectionArgs, List.map_append, List.map_map, Function.comp_def, lift']

omit [Params] in
/-- Block insertion preserves the preceding-field recipe. -/
theorem projectionArgs_liftN :
    (projectionArgs s ps m i).map (·.liftN n k) =
      projectionArgs s (ps.map (·.liftN n k)) (m.liftN n k) i := by
  simp only [projectionArgs, List.map_append, List.map_map, Function.comp_def, liftN]
end ProofShape

namespace ProofShape
/-- The exact erased type recipe of a selected registered projection. Its only
variable inputs are the recovered family arguments and the erased major. -/
noncomputable def projectionType (s : Lean.Name) (info : VProjectionInfo)
    (doms : List VExpr) (j : Nat) (hj : info.nparams + j < doms.length)
    (args : List ProofShape) (m : ProofShape) : ProofShape :=
  (proofErase (doms.take (info.nparams + j)).reverse doms[info.nparams + j]).instOuter
    (projectionArgs s (args.take info.nparams) m j)

/-- All free variables of the selected field template are covered by its raw
parameter and preceding-field images. -/
theorem projectionType_scope {args : List ProofShape} (T : ProjTele env univs s info ls doms result)
    (hj : info.nparams + j < doms.length) (ha : info.nparams ≤ args.length) :
    doms[info.nparams + j].ClosedN (projectionArgs s (args.take info.nparams) m j).length := by
  obtain ⟨u, hdom⟩ := T.doms _ hj
  have hc := (hdom.closedN' henv.ordered.closed (CtxWF.closed henv.ordered (T.ctx _ (Nat.le_of_lt hj)))).1
  simpa only [List.length_reverse, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj),
    projectionArgs, List.length_append, List.length_map, List.length_range,
    Nat.min_eq_left ha] using hc

/-- Arbitrary raw substitution acts on the variable inputs of a field recipe. -/
theorem projectionType_subst (T : ProjTele env univs s info ls doms result)
    (hj : info.nparams + j < doms.length) (ha : info.nparams ≤ args.length) :
    (projectionType s info doms j hj args m).subst σ =
      projectionType s info doms j hj (args.map (·.subst σ)) (m.subst σ) := by
  unfold projectionType
  rw [proofErase_instOuter_subst (projectionType_scope T hj ha), projectionArgs_subst, List.map_take]

/-- Field recipes commute with arbitrary thinning of their inputs. -/
theorem projectionType_lift' (T : ProjTele env univs s info ls doms result)
    (hj : info.nparams + j < doms.length) (ha : info.nparams ≤ args.length) :
    (projectionType s info doms j hj args m).lift' ρ =
      projectionType s info doms j hj (args.map (·.lift' ρ)) (m.lift' ρ) := by
  simp only [lift'_eq_subst]
  exact projectionType_subst T hj ha

/-- Field recipes commute with block insertion of their inputs. -/
theorem projectionType_liftN (T : ProjTele env univs s info ls doms result)
    (hj : info.nparams + j < doms.length) (ha : info.nparams ≤ args.length) :
    (projectionType s info doms j hj args m).liftN n k =
      projectionType s info doms j hj (args.map (·.liftN n k)) (m.liftN n k) := by
  simpa only [lift'_consN_skipN] using
    (projectionType_lift' (ρ := .consN (.skipN .refl n) k) T hj ha)
end ProofShape

end Lean4Lean.VEnv.Strengthening
