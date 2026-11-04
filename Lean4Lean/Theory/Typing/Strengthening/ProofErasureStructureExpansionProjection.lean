import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeStructureExpansion

/-! # Projection cancels masked native structure expansion

A saturated projection selects the field fixed by the closed telescope mask.
Typing identifies that mask with the erasure of the original projection.
This includes proof fields, dependent field types, and arbitrary parameters.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- A raw projection selects the exact masked field of the expanded constructor.
No type or native evidence for parameters or fields is required for this step. -/
theorem ProofShape.nativeStructureExpansion_projection
    (hi : env.projections s info) (hp : ps.length = info.nparams) (hj : j < info.numFields) :
    Compute (Primitive D) (.proj s j (nativeStructureExpansion doms s info ls ps m))
      (structureField doms s info.nparams m j) := by
  apply Compute.base
  apply Primitive.projIota hi
  · simp only [List.length_append, List.length_map, List.length_range, hp]
  · rw [List.getElem?_append_right (by omega), hp, Nat.add_sub_cancel_left]
    simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some]

/-- In an actual typed structure expansion, the raw selection is precisely the
original projection's erasure, whether retained or erased as a proof. -/
theorem proofErase_structure_expansion_projection
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : ps.length = info.nparams) (hj : j < info.numFields)
    (T : ProjTele env univs s info ls doms result)
    (hd : doms.length = info.nparams + info.numFields)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = info.uvars)
    (hexp : env.HasType univs Γ (structExpand s info ls ps m) (mkApps (.const s ls) ps)) :
    Compute (Primitive D)
      (.proj s j (nativeStructureExpansion doms s info ls (ps.map (proofErase Γ)) (proofErase Γ m)))
      (proofErase Γ (.proj s j m)) := by
  have hargs : (ps ++ projsOf s m info.numFields).length = doms.length := by
    simp only [List.length_append, projsOf, List.length_map, List.length_range, hp, hd]
  have hc := HasType.const (Γ := Γ) (henv.ordered.projectionConstructor hi) hw hl
  rw [T.shape] at hc
  have HA : TelInst env univs Γ doms (ps ++ projsOf s m info.numFields) :=
    ⟨hargs, (HasType.mkApps_wrapForalls henv hΓ hc ⟨_, hexp⟩ hargs).1⟩
  have hΔ : OnCtx doms.reverse (env.IsType univs) := by
    simpa only [List.take_length] using T.ctx doms.length (Nat.le_refl _)
  rw [proofErase_structure_field_template hΓ hΔ HA hp hj]
  exact nativeStructureExpansion_projection hi (by simpa only [List.length_map] using hp) hj

/-- A natively recovered structure family supplies both its exact eta expansion
and the projection residual back to the original field. The closed declaration
guard permits general nonempty dependent records, including erased proof fields;
no independent recovery certificate is required for a parameter or field. -/
theorem proofErase_native_structure_projection_residual
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0) (hj : j < info.numFields)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = info.uvars)
    (hm : env.HasType univs Γ m (mkApps (.const s ls) ps)) (hn : ¬ IsProof Γ m)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (RN : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ m)
      (ProofShape.mkApps (.const s ls) (ps.map (proofErase Γ)))) :
    NativeStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m)
        (proofErase Γ (structExpand s info ls ps m)) ∧
      Compute (Primitive D) (.proj s j (proofErase Γ (structExpand s info ls ps m)))
        (proofErase Γ (.proj s j m)) := by
  refine ⟨proofErase_native_structure_expansion hΓ hi hp hx hw hl hm hn hadm RN, ?_⟩
  obtain ⟨doms, result, HT, hd⟩ := projection_expansion_telescope_exists hi hw
  have hexp := (StructureReplay.expansion_typed_iff henv hΓ hi hp hx hm).2 hadm
  have hnexp : ¬ IsProof Γ (structExpand s info ls ps m) := by
    intro H
    have HE := IsDefEq.structEta hi hp hx hm hexp
    exact hn ((isProof_congr hΓ HE).1 H)
  rw [proofErase_structure_expansion_template hΓ hi hp HT hd hw hl hexp hnexp]
  exact proofErase_structure_expansion_projection hΓ hi hp hj HT hd hw hl hexp

end Lean4Lean.VEnv.Strengthening
