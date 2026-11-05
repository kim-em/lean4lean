import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTemplateComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureEtaStages

/-! # Computing all occurrences of a major in a dependent field recipe

A dependent projection recipe substitutes parameters and earlier projections
into a closed typed field template. The source substitution agrees with raw
projections at every retained variable. Consequently computation of the major
runs through the whole recipe, even when earlier fields are proofs and the
computed major has lost its native certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Earlier proof fields may remain raw projections in the substitution map:
only retained template variables require erasure agreement. -/
theorem erased_projection_subst_agreement {doms : List VExpr}
    (hΓ : OnCtx Γ (env.IsType univs))
    (W : Ctx.SubstEq env univs Γ (VExpr.Subst.ofList (ps ++ projsOf s m j))
      (VExpr.Subst.ofList (ps ++ projsOf s m j)) doms.reverse)
    (ha : (ps ++ projsOf s m j).length = doms.length) :
    ErasedSubstAgreement doms.reverse Γ (VExpr.Subst.ofList (ps ++ projsOf s m j))
      (ProofShape.Subst.ofList (projectionArgs s (ps.map (proofErase Γ)) (proofErase Γ m) j)) := by
  intro i A hl hn
  have hi : i < (ps ++ projsOf s m j).length := by
    have := hl.lt
    simp only [List.length_reverse] at this
    omega
  have hlen : (projectionArgs s (ps.map (proofErase Γ)) (proofErase Γ m) j).length =
      (ps ++ projsOf s m j).length := by simp [projectionArgs, projsOf]
  simp only [VExpr.Subst.ofList, ProofShape.Subst.ofList, hlen, dif_pos hi]
  let k := (ps ++ projsOf s m j).length - 1 - i
  have hk : k < (ps ++ projsOf s m j).length := by dsimp [k]; omega
  change proofErase Γ (ps ++ projsOf s m j)[k] =
    (projectionArgs s (ps.map (proofErase Γ)) (proofErase Γ m) j)[k]
  by_cases hkp : k < ps.length
  · have hkp' : k < (ps.map (proofErase Γ)).length := by simpa using hkp
    simp only [projectionArgs, List.getElem_append_left hkp,
      List.getElem_append_left hkp', List.getElem_map]
  · have hnp : ¬ IsProof Γ (.proj s (k - ps.length) m) := by
      have H := mt (isProof_subst hΓ W (HasType.bvar hl)).1 hn
      simp only [VExpr.subst, VExpr.Subst.ofList, dif_pos hi] at H
      change ¬ IsProof Γ ((ps ++ projsOf s m j)[k]) at H
      simpa only [List.getElem_append_right (Nat.le_of_not_gt hkp), projsOf,
        List.getElem_map, List.getElem_range] using H
    have hkp' : (ps.map (proofErase Γ)).length ≤ k := by simp only [List.length_map]; omega
    simp only [projectionArgs, List.getElem_append_right (Nat.le_of_not_gt hkp),
      List.getElem_append_right hkp', List.length_map, projsOf,
      List.getElem_map, List.getElem_range]
    exact if_neg hnp

omit [Params] in
/-- The entire raw capture vector follows a major computation. All parameters
stay fixed and every preceding projection uses the same path. -/
theorem ProofShape.projectionArgs_compute_major
    (R : ScopedCompute Step Δ m m') :
    List.Forall₂ (ScopedCompute Step Δ) (projectionArgs s ps m j) (projectionArgs s ps m' j) := by
  unfold projectionArgs
  apply List.Forall₂.append' (List.Forall₂.rfl (fun _ _ => ScopedCompute.refl))
  apply List.forall₂_map_left_iff.2
  apply List.forall₂_map_right_iff.2
  exact List.Forall₂.rfl (fun _ _ => ScopedCompute.proj R)

/-- A typed closed template permits arbitrary computed outputs of its major.
No native evidence for the major, parameters or preceding fields is required. -/
theorem proofErase_projection_template_compute_major_of_subst {doms : List VExpr}
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs doms.reverse e T)
    (W : Ctx.SubstEq env univs Γ (VExpr.Subst.ofList (ps ++ projsOf s m j))
      (VExpr.Subst.ofList (ps ++ projsOf s m j)) doms.reverse)
    (ha : (ps ++ projsOf s m j).length = doms.length)
    (R : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ m) out) :
    ScopedCompute Step (proofEraseCtx Γ)
      ((proofErase doms.reverse e).instOuter (projectionArgs s (ps.map (proofErase Γ)) (proofErase Γ m) j))
      ((proofErase doms.reverse e).instOuter (projectionArgs s (ps.map (proofErase Γ)) out j)) := by
  have E : ErasedSubstAgreement doms.reverse Γ (VExpr.Subst.ofList (ps ++ projsOf s m j))
      (ProofShape.Subst.ofList (projectionArgs s (ps.map (proofErase Γ)) (proofErase Γ m) j)) := by
    intro i A hl hn
    exact erased_projection_subst_agreement hΓ W ha hl hn
  have RC := projectionArgs_compute_major (s := s) (ps := ps.map (proofErase Γ)) (j := j) R
  apply proofErase_compute_subst_images_of_renaming hrename hΓ W he E
  intro i
  unfold ProofShape.Subst.ofList
  have hlen := RC.length_eq
  by_cases hi : i < (projectionArgs s (ps.map (proofErase Γ)) (proofErase Γ m) j).length
  · simp only [← hlen, dif_pos hi]
    exact RC.getElem_of _ (by omega) (by omega)
  · simp only [← hlen, dif_neg hi]
    exact .refl

/-- Telescope argument typing supplies the source substitution for the same
major-path theorem. The output may be raw and have no native certificate. -/
theorem proofErase_projection_template_compute_major
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hΔ : OnCtx doms.reverse (env.IsType univs))
    (he : env.HasType univs doms.reverse e T)
    (ha : TelInst env univs Γ doms (ps ++ projsOf s m j))
    (R : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ m) out) :
    ScopedCompute Step (proofEraseCtx Γ)
      ((proofErase doms.reverse e).instOuter (projectionArgs s (ps.map (proofErase Γ)) (proofErase Γ m) j))
      ((proofErase doms.reverse e).instOuter (projectionArgs s (ps.map (proofErase Γ)) out j)) :=
  proofErase_projection_template_compute_major_of_subst hrename hΓ he
    (erasedTemplate_substEq hΔ ha) ha.1 R

/-- Every selected dependent projection recipe follows a full-union major
path, including every preceding data-field occurrence. Only the initial
parameter/projection telescope needs ordinary typing. -/
theorem projectionType_compute_major
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HT : ProjTele env univs s info ls doms result)
    (hj : info.nparams + j < doms.length) (hp : ps.length = info.nparams)
    (ha : TelInst env univs Γ (doms.take (info.nparams + j)) (ps ++ projsOf s m j))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ m) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (projectionType s info doms j hj (ps.map (proofErase Γ)) (proofErase Γ m))
      (projectionType s info doms j hj (ps.map (proofErase Γ)) out) := by
  obtain ⟨_, hF⟩ := HT.doms _ hj
  have HC := proofErase_projection_template_compute_major
    (fun {Δ Δ' a b τ} ⟨stage, H⟩ W =>
      ⟨stage, erased_static_structure_eta_expansion_stage_rename heq hs stage H W⟩)
    hΓ (HT.ctx _ (Nat.le_of_lt hj)) hF ha R
  simpa only [projectionType, ← hp, ← List.map_take, List.take_length] using HC

end Lean4Lean.VEnv.Strengthening
