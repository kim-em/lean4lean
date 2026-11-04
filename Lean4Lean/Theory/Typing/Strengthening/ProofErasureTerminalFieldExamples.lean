import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalFieldInstantiation

/-! # Retained type and dependent data fields beyond terminal-image coverage

A record with a type field and a rigid data field depending on that type has a
terminal-field certificate. Its first projection is actually typed and retained,
so its major cannot have the old TerminalImage certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A dependent two-field telescope, like a type together with a list over it,
satisfies the field condition whenever the data family is rigid and has no
projections. The data-field type contains the preceding field. -/
theorem StructureReplay.TerminalFields.dependent_type_data
    (hshape : info.ctorType = wrapForalls
      [.sort (.succ .zero), VExpr.mkApps (.const d us) [.bvar 0]] result)
    (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hr : env.Rigid d) (hn : ∀ info, ¬ env.projections d info) :
    TerminalFields env info := by
  apply TerminalFields.of_telescope hshape (by simp [hp, hf])
  intro j hj _
  have hjcases : j = 0 ∨ j = 1 := by simp only [List.length_cons, List.length_nil] at hj; omega
  rcases hjcases with rfl | rfl
  · exact .sort
  · exact .data hr hn

/-- This constructor certificate supplies actual image coverage for any typed
major, without inspecting its computation or normal form. -/
theorem ProjectionTerminalImage.of_dependent_type_data
    (hm : env.HasType univs Γ m (.const family ls))
    (hi : env.projections family info)
    (hshape : info.ctorType = wrapForalls
      [.sort (.succ .zero), VExpr.mkApps (.const d us) [.bvar 0]] result)
    (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hr : env.Rigid d) (hn : ∀ info, ¬ env.projections d info) :
    ProjectionTerminalImage Γ m :=
  .fields (args := []) hm hi (StructureReplay.TerminalFields.dependent_type_data hshape hp hf hr hn)

/-- A positive registered record with this telescope has a retained type
projection. It lies outside TerminalImage, so the extension covers new typed
images rather than merely restating the earlier proof-only structure case. -/
theorem terminal_fields_retained_projection
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family ls))
    (hi : env.projections family info)
    (hshape : info.ctorType = wrapForalls
      [.sort (.succ .zero), VExpr.mkApps (.const d us) [.bvar 0]] result)
    (hp : info.nparams = 0) (hx : info.nindices = 0) (hf : info.numFields = 2)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = info.uvars)
    (hpos : (info.resultLevel.inst ls).IsNeverZero)
    (hr : env.Rigid d) (hn : ∀ info, ¬ env.projections d info) :
    ProjectionTerminalImage Γ m ∧
    env.HasType univs Γ (.proj family 0 m) (.sort (.succ .zero)) ∧
    ¬ IsProof Γ (.proj family 0 m) ∧ ¬ TerminalImage Γ m := by
  have hfield : info.fieldType family ls [] 0 m = some (.sort (.succ .zero)) := by
    have H := info.fieldType_eq_instOuter (typeName := family) (major := m) hshape hl
      (params := []) (by simp [hp]) (index := 0) (by simp [hp])
    simpa only [hp, Nat.zero_add, List.getElem_cons_zero, VExpr.instL, VLevel.inst,
      VExpr.instOuter_sort] using H
  obtain ⟨_, hc⟩ := henv.ordered.constWF (henv.ordered.projectionConstructor hi)
  have hclosed := hc.closedN henv.ordered (show OnCtx ([] : List VExpr) (env.IsType info.uvars) from trivial)
  have ht : env.HasType univs Γ (.proj family 0 m) (.sort (.succ .zero)) :=
    .projDF (indexArgs := []) hi hw hl (by simp [hp]) (by simp [hx]) hfield
      (HasType.sort (by trivial)) hm hm hclosed (.inl hpos)
  have hnp := not_isProof_of_sort hΓ ht
  exact ⟨ProjectionTerminalImage.of_dependent_type_data hm hi hshape hp hf hr hn,
    ht, hnp, fun H => H.not_projection hΓ ht hnp⟩

/-- The concrete dependent telescope instantiates all common-typed body
comparisons, including bodies that use its retained projections. -/
theorem proofErase_computed_joint_zero_compare_inst_dependentTypeData
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ m P) (hm : env.HasType univs Γ m (.const family ls))
    (hi : env.projections family info)
    (hshape : info.ctorType = wrapForalls
      [.sort (.succ .zero), VExpr.mkApps (.const d us) [.bvar 0]] result)
    (hparams : info.nparams = 0) (hf : info.numFields = 2)
    (hr : env.Rigid d) (hn : ∀ info, ¬ env.projections d info)
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (P :: Γ)) mode
      (proofErase (P :: Γ) a) (proofErase (P :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst m)) (proofErase Γ (b.inst m)) :=
  proofErase_computed_joint_zero_compare_inst_projectable hs hΓ hp
    (ProjectionTerminalImage.of_dependent_type_data hm hi hshape hparams hf hr hn) ha hb H

end Lean4Lean.VEnv.Strengthening
