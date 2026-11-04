import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureProjectionResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureExpansionTemplate

/-! # Dependent projection type residuals after structure expansion

The native projection recipe contains preceding fields. Expanding its major
creates projections throughout that dependent recipe. Each contracts to the
original field erasure; proof fields are handled through typed capture erasure.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Erasure of a projection of an expanded major computes back to the original
projection erasure. Proof fields are already identical proof markers. -/
theorem proofErase_structure_projected_expansion_compute
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0) (hj : j < info.numFields)
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const s ls) ps))
    (hc : env.HasType univs Γ (structExpand s info ls ps m) (VExpr.mkApps (.const s ls) ps))
    (hn : ¬ IsProof Γ (structExpand s info ls ps m)) :
    Compute (Primitive D) (proofErase Γ (.proj s j (structExpand s info ls ps m)))
      (proofErase Γ (.proj s j m)) := by
  have hc2 := (StructureReplay.expansion_typed_iff henv hΓ hi hp hx hc).2
    ((StructureReplay.expansion_typed_iff henv hΓ hi hp hx hm).1 hc)
  have H := structure_proofField_iff hΓ hi hp hj hc
  have H2 := structure_proofField_iff hΓ hi hp hj hc2
  by_cases h : StructureReplay.ProofField env univs info ls j
  · rw [proofErase_eq_proof.2 (H2.1 h), proofErase_eq_proof.2 (H.1 h)]
    exact .refl
  · rw [show proofErase Γ (.proj s j (structExpand s info ls ps m)) =
        .proj s j (proofErase Γ (structExpand s info ls ps m)) from if_neg (fun h' => h (H2.2 h'))]
    exact proofErase_static_structure_projection_residual hΓ hi hp hj hc hn

/-- Typed expansion supplies any prefix of the closed constructor telescope.
The full field vector may contain arbitrary dependencies on earlier proofs. -/
theorem structure_expansion_prefix_telescope
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : ps.length = info.nparams) (T : ProjTele env univs s info ls doms result)
    (hd : doms.length = info.nparams + info.numFields)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = info.uvars)
    (hc : env.HasType univs Γ (structExpand s info ls ps m) A)
    (hj : j ≤ info.numFields) :
    TelInst env univs Γ (doms.take (info.nparams + j)) (ps ++ projsOf s m j) := by
  have hargs : (ps ++ projsOf s m info.numFields).length = doms.length := by
    simp only [List.length_append, projsOf, List.length_map, List.length_range, hp, hd]
  have hctor := HasType.const (Γ := Γ) (henv.ordered.projectionConstructor hi) hw hl
  rw [T.shape] at hctor
  have HA : TelInst env univs Γ doms (ps ++ projsOf s m info.numFields) :=
    ⟨hargs, (HasType.mkApps_wrapForalls henv hΓ hctor ⟨_, hc⟩ hargs).1⟩
  have HA' : TelInst env univs Γ
      (doms.take (info.nparams + j) ++ doms.drop (info.nparams + j))
      (ps ++ projsOf s m info.numFields) := by simpa only [List.take_append_drop] using HA
  have H := HA'.take
  rw [List.length_take, Nat.min_eq_left (by omega)] at H
  simpa only [projsOf, StructureReplay.projection_args_take hp hj] using H

/-- A dependent projection recipe can use the actual erased capture vector.
This equality removes raw proof projections that do not occur in its template. -/
theorem projectionType_eq_masked_captures
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : ps.length = info.nparams)
    (T : ProjTele env univs s info ls doms result) (hj : info.nparams + j < doms.length)
    (HA : TelInst env univs Γ (doms.take (info.nparams + j)) (ps ++ projsOf s m j)) :
    projectionType s info doms j hj (ps.map (proofErase Γ)) (proofErase Γ m) =
      (proofErase (doms.take (info.nparams + j)).reverse doms[info.nparams + j]).instOuter
        ((ps ++ projsOf s m j).map (proofErase Γ)) := by
  have hΔ := T.ctx (info.nparams + j) (Nat.le_of_lt hj)
  obtain ⟨u, hF⟩ := T.doms _ hj
  have E := (proofErase_projection_template hΓ hΔ hF HA).symm.trans
    (proofErase_instOuter hΓ hΔ hF HA)
  simpa only [projectionType, ← hp, ← List.map_take, List.take_length] using E

/-- Expanding a structure major in its entire dependent projection-type recipe
computes back to the original recipe in the primitive core. This includes
parameters and earlier proof fields, and requires no native field recovery. -/
theorem proofErase_structure_projection_type_residual
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (T : ProjTele env univs s info ls doms result)
    (hd : doms.length = info.nparams + info.numFields) (hj : info.nparams + j < doms.length)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = info.uvars)
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const s ls) ps))
    (hc : env.HasType univs Γ (structExpand s info ls ps m) (VExpr.mkApps (.const s ls) ps))
    (hn : ¬ IsProof Γ (structExpand s info ls ps m)) :
    Compute (Primitive D)
      (projectionType s info doms j hj (ps.map (proofErase Γ))
        (proofErase Γ (structExpand s info ls ps m)))
      (projectionType s info doms j hj (ps.map (proofErase Γ)) (proofErase Γ m)) := by
  have hc2 := (StructureReplay.expansion_typed_iff henv hΓ hi hp hx hc).2
    ((StructureReplay.expansion_typed_iff henv hΓ hi hp hx hm).1 hc)
  have HA := structure_expansion_prefix_telescope hΓ hi hp T hd hw hl hc (j := j) (by omega)
  have HB := structure_expansion_prefix_telescope hΓ hi hp T hd hw hl hc2 (j := j) (by omega)
  rw [projectionType_eq_masked_captures hΓ hp T hj HB,
    projectionType_eq_masked_captures hΓ hp T hj HA]
  have H : List.Forall₂ (Compute (Primitive D))
      ((ps ++ projsOf s (structExpand s info ls ps m) j).map (proofErase Γ))
      ((ps ++ projsOf s m j).map (proofErase Γ)) := by
    simp only [List.map_append, projsOf, List.map_map]
    apply List.Forall₂.append' (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl))
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply Lean4Lean.List.Forall₂.rfl
    intro k hk
    exact proofErase_structure_projected_expansion_compute hΓ hi hp hx
      (by have := List.mem_range.1 hk; omega) hm hc hn
  apply Compute.subst_images (fun H => H.liftN)
  intro i
  unfold ProofShape.Subst.ofList
  have hlen := H.length_eq
  by_cases hi : i < ((ps ++ projsOf s (structExpand s info ls ps m) j).map (proofErase Γ)).length
  · simp only [← hlen, dif_pos hi]
    exact H.getElem_of _ (by omega) (by omega)
  · simp only [← hlen, dif_neg hi]
    exact .refl

/-- Native recovery of the expanded major at the original family suffices to
recover its projected field at the original recipe, then replay every original
conversion tail. The extra alignment computation is entirely primitive core. -/
theorem proofErase_structure_projected_recovery_transport
    (hinclude : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (T : ProjTele env univs s info ls doms result)
    (hd : doms.length = info.nparams + info.numFields) (hj : info.nparams + j < doms.length)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = info.uvars)
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const s ls) ps))
    (hc : env.HasType univs Γ (structExpand s info ls ps m) (VExpr.mkApps (.const s ls) ps))
    (hn : ¬ IsProof Γ (structExpand s info ls ps m))
    (hproj : ¬ IsProof Γ (.proj s j m))
    (RN : ScopedTypeRecovery Step (proofEraseCtx Γ)
      (proofErase Γ (structExpand s info ls ps m))
      (ProofShape.mkApps (.const s ls) (ps.map (proofErase Γ))))
    (RC : ScopedCompute Step (proofEraseCtx Γ)
      (projectionType s info doms j hj (ps.map (proofErase Γ)) (proofErase Γ m)) out) :
    ScopedTypeRecovery Step (proofEraseCtx Γ)
      (proofErase Γ (.proj s j (structExpand s info ls ps m))) out := by
  have hc2 := (StructureReplay.expansion_typed_iff henv hΓ hi hp hx hc).2
    ((StructureReplay.expansion_typed_iff henv hΓ hi hp hx hm).1 hc)
  have H := structure_proofField_iff hΓ hi hp (by omega : j < info.numFields) hc
  have H2 := structure_proofField_iff hΓ hi hp (by omega : j < info.numFields) hc2
  rw [show proofErase Γ (.proj s j (structExpand s info ls ps m)) =
    .proj s j (proofErase Γ (structExpand s info ls ps m)) from
    if_neg (fun h => hproj (H.1 (H2.2 h)))]
  have R : ScopedTypeRecovery Step (proofEraseCtx Γ)
      (.proj s j (proofErase Γ (structExpand s info ls ps m)))
      (projectionType s info doms j hj (ps.map (proofErase Γ))
        (proofErase Γ (structExpand s info ls ps m))) :=
    .proj hi T hj (by simp only [List.length_map, hp, hx, Nat.add_zero]) RN
  exact R.convert (((proofErase_structure_projection_type_residual
    hΓ hi hp hx T hd hj hw hl hm hc hn).scoped hinclude).trans RC)

end Lean4Lean.VEnv.Strengthening
