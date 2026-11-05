import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedTemplateCongruence

/-! # Expose record fields with their own dependent identity annotations

Structure eta opens an identity-wrapped major. Each retained projection first
writes its exact native type, then contracts the major wrapper underneath it.
The left and right field recipes remain distinct; field exposure is not
silently asked to join or identify those recipes.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Inferred comparisons of the preceding actual fields compare the two
dependent projection recipes at the same stage. Each major retains its own
typed telescope instance. Proof-valued captures are erased before comparison;
the projection-template theorem justifies their raw appearances in the recipes.
This gives a comparison, not a common reduct or native-type conversion. -/
theorem proofErase_projectionType_compare_fields
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (HT : ProjTele env univs family info ls doms result)
    (hj : info.nparams + j < doms.length) (hp : ps.length = info.nparams)
    (ha : TelInst env univs Γ (doms.take (info.nparams + j)) (ps ++ projsOf family a j))
    (hb : TelInst env univs Γ (doms.take (info.nparams + j)) (ps ++ projsOf family b j))
    (H : ∀ i < j, ComputedJointCompare Step (proofEraseCtx Γ) false
      (proofErase Γ (.proj family i a)) (proofErase Γ (.proj family i b))) :
    ComputedJointCompare Step (proofEraseCtx Γ) false
      (projectionType family info doms j hj (ps.map (proofErase Γ)) (proofErase Γ a))
      (projectionType family info doms j hj (ps.map (proofErase Γ)) (proofErase Γ b)) := by
  obtain ⟨u, hF⟩ := HT.doms _ hj
  have hΔ := HT.ctx _ (Nat.le_of_lt hj)
  have EA := (proofErase_projection_template hΓ hΔ hF ha).symm.trans
    (proofErase_instOuter hΓ hΔ hF ha)
  have EB := (proofErase_projection_template hΓ hΔ hF hb).symm.trans
    (proofErase_instOuter hΓ hΔ hF hb)
  unfold projectionType
  have hp' : (ps.map (proofErase Γ)).take info.nparams = ps.map (proofErase Γ) :=
    List.take_of_length_le (by simp only [List.length_map, hp]; omega)
  rw [hp', EA, EB]
  apply proofErase_computed_template_compare_captures hrename hΓ hΔ hF ha
  simp only [List.map_append]
  apply List.Forall₂.append' (Lean4Lean.List.Forall₂.rfl (fun _ _ => .leaf .refl))
  simp only [projsOf, List.map_map, Function.comp_def]
  apply List.forall₂_map_left_iff.2
  apply List.forall₂_map_right_iff.2
  exact Lean4Lean.List.Forall₂.rfl (fun i hi => H i (List.mem_range.1 hi))

/-- Masked record fields retain their exact dependent projection type in an
identity annotation. Out-of-range entries are proof markers and never occur
in a structure output's field vector. -/
noncomputable def identityStructureField (family : Name) (info : VProjectionInfo)
    (ls : List VLevel) (doms : List VExpr) (ps : List ProofShape) (m : ProofShape) (j : Nat) : ProofShape := by
  classical
  exact if hj : info.nparams + j < doms.length then
    if StructureReplay.ProofField env univs info ls j then .proof
    else .app (.lam (projectionType family info doms j hj ps m) (.bvar 0)) (.proj family j m)
  else .proof

/-- A projection of the identity-wrapped major can write its original major's
exact field recipe before discarding the major wrapper. The recipe conversion
is beta only and therefore already belongs to stage zero. -/
theorem first_stage_identity_record_projection
    (hi : env.projections family info) (hx : info.nindices = 0) (hp : ps.length = info.nparams)
    (HT : ProjTele env univs family info ls doms result) (hj : info.nparams + j < doms.length) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ
      (.proj family j (.app (.lam (ProofShape.mkApps (.const family ls) ps) (.bvar 0)) m))
      (.app (.lam (projectionType family info doms j hj ps m) (.bvar 0)) (.proj family j m)) := by
  let Q := ProofShape.mkApps (.const family ls) ps
  let covered := ProofShape.app (.lam Q (.bvar 0)) m
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) Δ covered Q :=
    raw_identity_native _ _
  have RP := ScopedTypeRecovery.proj hi HT hj (by omega) RN
  have RB := projectionType_beta (s := family) (info := info) (doms := doms) (j := j) (hj := hj)
    (Lean4Lean.List.Forall₂.rfl (l := ps) (fun _ _ => BetaRed.refl)) (raw_identity_beta Q m)
  have RT := RP.convert (.beta RB)
  have RI : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ (.proj family j covered)
      (.app (.lam (projectionType family info doms j hj ps m) (.bvar 0)) (.proj family j covered)) :=
    .base (.inr (.inr (.inr (.inl (.intro RT)))))
  exact RI.trans (.beta (.app .refl (.proj (raw_identity_beta Q m))))

/-- Structure expansion transfers the outer identity annotation to every
retained field at stage one. Parameters stay fixed and dependent recipes use
the original major. Proof fields retain their static erased mask. -/
theorem first_stage_identity_record_fields
    (hi : env.projections family info) (hx : info.nindices = 0) (hp : ps.length = info.nparams)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (HT : ProjTele env univs family info ls doms result) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ
      (.app (.lam (ProofShape.mkApps (.const family ls) ps) (.bvar 0)) m)
      (ProofShape.mkApps (.const info.ctorName ls)
        (ps ++ (List.range info.numFields).map (identityStructureField family info ls doms ps m))) := by
  classical
  let Q := ProofShape.mkApps (.const family ls) ps
  let covered := ProofShape.app (.lam Q (.bvar 0)) m
  have RE : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ covered
      (nativeStructureOutput family info ls ps covered) :=
    .base (.inr (.inr (.inr (.inr (.inr (.intro hi hx hadm hp (raw_identity_native _ _)))))))
  apply RE.trans
  unfold nativeStructureOutput
  apply ScopedCompute.mkApps .refl
  apply List.Forall₂.append' (Lean4Lean.List.Forall₂.rfl (fun _ _ => ScopedCompute.refl))
  apply List.forall₂_map_left_iff.2
  apply List.forall₂_map_right_iff.2
  apply Lean4Lean.List.Forall₂.rfl
  intro j hj
  have hj' : info.nparams + j < doms.length := by
    have := List.mem_range.1 hj
    have := HT.numFields
    omega
  unfold nativeStructureField identityStructureField
  rw [dif_pos hj']
  split
  · exact .refl
  · exact first_stage_identity_record_projection hi hx hp HT hj'

/-- Inferred head comparison and common argument comparisons assemble an
inferred comparison of the full application spine in the same checker. -/
theorem ProofShape.ComputedJointCompare.mkApps
    (HF : ComputedJointCompare Step Δ false f g)
    (HA : List.Forall₂ (ComputedJointCompare Step Δ true) args args') :
    ComputedJointCompare Step Δ false (ProofShape.mkApps f args) (ProofShape.mkApps g args') := by
  induction HA generalizing f g with
  | nil => exact HF
  | cons H _ ih => exact ih (.app HF H)

/-- Exposing the separately annotated field vectors closes record exposure.
Each field starts at its own major's exact dependent recipe. No equality or
common reduct of those two recipes is presumed; producing these paired field
paths and final common comparisons is the remaining field obligation. -/
theorem IdentityCarrierExposure.record_fields
    (hi : env.projections family info) (hx : info.nindices = 0) (hp : ps.length = info.nparams)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (HT : ProjTele env univs family info ls doms result)
    (HA : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ)
      ((List.range info.numFields).map (identityStructureField family info ls doms ps a)) fieldsA)
    (HB : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ)
      ((List.range info.numFields).map (identityStructureField family info ls doms ps b)) fieldsB)
    (HG : List.Forall₂ (ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) Δ true) fieldsA fieldsB) :
    IdentityCarrierExposure D Δ (ProofShape.mkApps (.const family ls) ps) a b := by
  have RA := first_stage_identity_record_fields (D := D) (Δ := Δ) (m := a) hi hx hp hadm HT
  have RB := first_stage_identity_record_fields (D := D) (Δ := Δ) (m := b) hi hx hp hadm HT
  have HC : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) Δ false
      (ProofShape.mkApps (.const info.ctorName ls) (ps ++ fieldsA))
      (ProofShape.mkApps (.const info.ctorName ls) (ps ++ fieldsB)) :=
    ComputedJointCompare.mkApps (.leaf .refl)
      (List.Forall₂.append' (Lean4Lean.List.Forall₂.rfl (fun _ _ => .leaf .refl)) HG)
  exact ⟨_, _, _, .refl,
    RA.trans (.mkApps .refl (List.Forall₂.append' (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl)) HA)),
    RB.trans (.mkApps .refl (List.Forall₂.append' (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl)) HB)),
    .carrierChecked HC.common⟩

end Lean4Lean.VEnv.Strengthening
