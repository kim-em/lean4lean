import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFamilySpines
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointFieldRealization

/-! # Future constructor comparisons from retained field certificates

Independent beta paths split the constructor spine into parameters and fields.
Retained field certificates compare the reduced fields with projections of the
reduced major. Proof markers remain hidden through both beta and substitution.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

private theorem constructor_beta
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams) (hf : fields.length = info.numFields)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (H : ∀ i (hj : i < fields.length), fields[i] ≠ .proof →
      BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ fields[i] (.proj family i m))
    (RC : ProofShape.BetaRed (mkApps (.const info.ctorName ls) (ps ++ fields)) c)
    (RM : ProofShape.BetaRed m n) : JointCompare Step Δ true c n := by
  obtain ⟨args, rfl, HR⟩ := RC.const_spine
  have RP := Lean4Lean.List.forall₂_take HR ps.length
  have RF := Lean4Lean.List.forall₂_drop HR ps.length
  simp only [List.take_left] at RP
  simp only [List.drop_left] at RF
  rw [← List.take_append_drop ps.length args]
  apply JointCheck.structFields hi hx (RP.length_eq.symm.trans hp) (RF.length_eq.symm.trans hf) hadm
  intro i hj hn
  have hi' : i < fields.length := by rw [RF.length_eq]; exact hj
  have RB := RF.getElem_of i hi' hj
  have hn' : fields[i] ≠ .proof := by
    intro E
    rw [E] at RB
    exact hn (RB.fixed_of_normal (Step := fun _ _ => False) ⟨fun _ H => H, trivial⟩)
  exact (H i hi' hn').1 RB (.proj RM)

/-- Future comparisons of retained constructor fields provide a full future
constructor-to-major comparison. Fields that erase after substitution are
skipped; an originally erased field can never become retained. -/
theorem BetaStableFamily.struct_fields
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams) (hf : fields.length = info.numFields)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (H : ∀ i (hj : i < fields.length), fields[i] ≠ .proof →
      BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ fields[i] (.proj family i m)) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ
      (mkApps (.const info.ctorName ls) (ps ++ fields)) m := by
  refine ⟨fun RC RM => constructor_beta hi hx hp hf hadm H RC RM, ?_⟩
  intro Δ' τ c n W RC RM
  simp only [ProofShape.subst_mkApps, ProofShape.subst, List.map_append] at RC
  apply constructor_beta hi hx (by simpa only [List.length_map] using hp)
    (by simpa only [List.length_map] using hf) hadm ?_ RC RM
  intro i hj hn
  have hi' : i < fields.length := by simpa only [List.length_map] using hj
  have hn' : fields[i] ≠ .proof := by
    intro E
    simp only [List.getElem_map, E, ProofShape.subst] at hn
    exact hn rfl
  simpa only [List.getElem_map, ProofShape.subst] using (H i hi' hn').subst W

/-- Every typed structure-eta expansion has a future family certificate. Each
retained field is an actual typed projection, so typed beta confluence supplies
its reflexive future certificate. Proof-valued whole structures are handled by
the common proof erasure. No primitive confluence or transport law is needed. -/
theorem proofErase_structure_eta_family
    (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : ps.length = info.nparams)
    (hx : info.nindices = 0)
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const family ls) ps))
    (hexp : env.HasType univs Γ (structExpand family info ls ps m)
      (VExpr.mkApps (.const family ls) ps)) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ)
      (proofErase Γ (structExpand family info ls ps m)) (proofErase Γ m) := by
  by_cases hproof : IsProof Γ m
  · have HE := IsDefEq.structEta hi hp hx hm hexp
    have E := (proofErase_eq_proof.2 ((isProof_congr hΓ HE).2 hproof)).trans
      (proofErase_eq_proof.2 hproof).symm
    exact proofErase_beta_join_family hΓ hexp hm (E ▸ ProofShape.BetaRed.refl) .refl
  have hn := mt (isProof_congr hΓ (IsDefEq.structEta hi hp hx hm hexp)).1 hproof
  rw [show structExpand family info ls ps m = VExpr.mkApps (.const info.ctorName ls)
    (ps ++ (List.range info.numFields).map (fun i => .proj family i m)) from rfl]
  rw [proofErase_const_spine hΓ hexp hn, List.map_append]
  apply BetaStableFamily.struct_fields hi hx (by simp [hp]) (by simp)
    ((StructureReplay.expansion_typed_iff henv hΓ hi hp hx hm).1 hexp)
  intro i hj hnfield
  simp only [List.length_map, List.length_range] at hj
  simp only [List.getElem_map, List.getElem_range] at hnfield ⊢
  obtain ⟨F, hproj, _⟩ := structure_equal_projection_typings hΓ hm hexp hj
  have hnp : ¬ IsProof Γ (.proj family i m) := fun H => hnfield (proofErase_eq_proof.2 H)
  have Eproj : proofErase Γ (.proj family i m) = .proj family i (proofErase Γ m) := if_neg hnp
  rw [← Eproj]
  exact proofErase_beta_join_family hΓ hproj hproj .refl .refl

end Lean4Lean.VEnv.Strengthening
