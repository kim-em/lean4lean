import Lean4Lean.Theory.Typing.AnchoredSortableHeadDepth

/-! Constant-only relocation changes no closed payload or named-head policy.
The actual destination endpoint is supplied independently in the same original
environment; no assigned types or original proof roots are identified. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

mutual
theorem Obs.relocateConstant
    (query : Obs env U registry target locals σ (.const name levels) profile footprint)
    (newLocals : List Nat) (τ : Subst) :
    ∃ result : Obs env U registry target newLocals τ (.const name levels) profile footprint, ∀ policy, result.headDepth policy = query.headDepth policy := by
  match query with
  | .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body =>
    exact ⟨.delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body, fun policy => by simp only [Obs.headDepth]⟩
  | .native lookup notDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed certificate typed tree =>
    exact ⟨.native lookup notDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed certificate typed tree, fun policy => by simp only [Obs.headDepth]⟩
  | .family lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    exact ⟨.family lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree, fun policy => by simp only [Obs.headDepth]⟩
  | .constructor lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    exact ⟨.constructor lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree, fun policy => by simp only [Obs.headDepth]⟩
  | .empty => exact ⟨.empty, fun policy => by simp only [Obs.headDepth]⟩
  | .union first second =>
    obtain ⟨first, hf⟩ := first.relocateConstant newLocals τ
    obtain ⟨second, hs⟩ := second.relocateConstant newLocals τ
    exact ⟨.union first second, fun policy => by simp only [Obs.headDepth, hf, hs]⟩
  | .view child change =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.view child change, fun policy => by simp only [Obs.headDepth, depth]⟩
  | .pad child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.pad child, fun policy => by simp only [Obs.headDepth, depth]⟩
  | .unpad child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.unpad child, fun policy => by simp only [Obs.headDepth, depth]⟩
  | .rowShift child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.rowShift child, fun policy => by simp only [Obs.headDepth, depth]⟩
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

theorem CodeCert.relocateConstant
    (query : CodeCert env U registry target locals σ (.const name levels) profile footprint)
    (newLocals : List Nat) (τ : Subst) :
    ∃ result : CodeCert env U registry target newLocals τ (.const name levels) profile footprint, ∀ policy, result.headDepth policy = query.headDepth policy := by
  match query with
  | .seed child formed =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.seed child formed, fun policy => by simp only [CodeCert.headDepth, depth]⟩
  | .union first second =>
    obtain ⟨first, hf⟩ := first.relocateConstant newLocals τ
    obtain ⟨second, hs⟩ := second.relocateConstant newLocals τ
    exact ⟨.union first second, fun policy => by simp only [CodeCert.headDepth, hf, hs]⟩
  | .pad child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.pad child, fun policy => by simp only [CodeCert.headDepth, depth]⟩
  | .familyPad child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.familyPad child, fun policy => by simp only [CodeCert.headDepth, depth]⟩
  | .unpad child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.unpad child, fun policy => by simp only [CodeCert.headDepth, depth]⟩
  | .down child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.down child, fun policy => by simp only [CodeCert.headDepth, depth]⟩
  | .map change child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.map change child, fun policy => by simp only [CodeCert.headDepth, depth]⟩
  | .select child member =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.select child member, fun policy => by simp only [CodeCert.headDepth, depth]⟩
  | .focusMinimal child minimal bound =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.focusMinimal child minimal bound, fun policy => by simp only [CodeCert.headDepth, depth]⟩
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

theorem SortableObs.relocateConstant
    (query : SortableObs env U registry target locals σ (.const name levels) profile footprint)
    (newLocals : List Nat) (τ : Subst) :
    ∃ result : SortableObs env U registry target newLocals τ (.const name levels) profile footprint, ∀ policy, result.headDepth policy = query.headDepth policy := by
  match query with
  | .family lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    exact ⟨.family lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree, fun policy => by simp only [SortableObs.headDepth]⟩
  | .legacy child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.legacy child, fun policy => by simp only [SortableObs.headDepth, depth]⟩
  | .code relevant child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.code relevant child, fun policy => by simp only [SortableObs.headDepth, depth]⟩
  | .union first second =>
    obtain ⟨first, hf⟩ := first.relocateConstant newLocals τ
    obtain ⟨second, hs⟩ := second.relocateConstant newLocals τ
    exact ⟨.union first second, fun policy => by simp only [SortableObs.headDepth, hf, hs]⟩
  | .view child change =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.view child change, fun policy => by simp only [SortableObs.headDepth, depth]⟩
  | .action child change =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.action child change, fun policy => by simp only [SortableObs.headDepth, depth]⟩
  | .pad child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.pad child, fun policy => by simp only [SortableObs.headDepth, depth]⟩
  | .unpad child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.unpad child, fun policy => by simp only [SortableObs.headDepth, depth]⟩
  | .rowShift child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.rowShift child, fun policy => by simp only [SortableObs.headDepth, depth]⟩
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

theorem SortableCert.relocateConstant
    (query : SortableCert env U registry target locals σ (.const name levels) relevant profile footprint)
    (newLocals : List Nat) (τ : Subst) :
    ∃ result : SortableCert env U registry target newLocals τ (.const name levels) relevant profile footprint, ∀ policy, result.headDepth policy = query.headDepth policy := by
  match query with
  | .ofCode child formed =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.ofCode child formed, fun policy => by simp only [SortableCert.headDepth, depth]⟩
  | .observe child formed =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.observe child formed, fun policy => by simp only [SortableCert.headDepth, depth]⟩
  | .seed child formed =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.seed child formed, fun policy => by simp only [SortableCert.headDepth, depth]⟩
  | .union first second =>
    obtain ⟨first, hf⟩ := first.relocateConstant newLocals τ
    obtain ⟨second, hs⟩ := second.relocateConstant newLocals τ
    exact ⟨.union first second, fun policy => by simp only [SortableCert.headDepth, hf, hs]⟩
  | .pad child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.pad child, fun policy => by simp only [SortableCert.headDepth, depth]⟩
  | .sortPad child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.sortPad child, fun policy => by simp only [SortableCert.headDepth, depth]⟩
  | .familyPad child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.familyPad child, fun policy => by simp only [SortableCert.headDepth, depth]⟩
  | .unpad child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.unpad child, fun policy => by simp only [SortableCert.headDepth, depth]⟩
  | .down child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.down child, fun policy => by simp only [SortableCert.headDepth, depth]⟩
  | .map change child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.map change child, fun policy => by simp only [SortableCert.headDepth, depth]⟩
  | .support change child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.support change child, fun policy => by simp only [SortableCert.headDepth, depth]⟩
  | .select child member =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.select child member, fun policy => by simp only [SortableCert.headDepth, depth]⟩
  | .focusMinimal child minimal bound =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.focusMinimal child minimal bound, fun policy => by simp only [SortableCert.headDepth, depth]⟩
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

end

end Lean4Lean.AnchoredSource.Adapted
