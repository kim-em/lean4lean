import Lean4Lean.Theory.Typing.AnchoredSortableConstantRelocation
import Lean4Lean.Theory.Typing.AnchoredOriginalRichHeadDepth

/-! Constant-only relocation changes no closed payload or named-head policy.
The actual destination endpoint is supplied independently in the same original
environment; no assigned types or original proof roots are identified. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalRecordSource OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

mutual
theorem OriginalRecordSource.RichObs.relocateConstant
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (destination : EndpointState sourceEnv U nextSource (.const name levels) nextAssigned)
    (newLocals : List Nat) (τ : Subst) :
    ∃ result : RichObs sourceEnv env U registry target destination newLocals τ profile footprint, ∀ policy, result.headDepth policy = query.headDepth policy := by
  match query with
  | .rigidFamily origin lookup inert seedWF seedLength frozenWF levelsWF seedFrozen frozenLevelsEq typeClosed plan certificate ready typed =>
    exact ⟨.rigidFamily origin lookup inert seedWF seedLength frozenWF levelsWF seedFrozen frozenLevelsEq typeClosed plan certificate ready typed, fun policy => by simp only [RichObs.headDepth]⟩
  | .family origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    exact ⟨.family origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree, fun policy => by simp only [RichObs.headDepth]⟩
  | .constructor origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    exact ⟨.constructor origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree, fun policy => by simp only [RichObs.headDepth]⟩
  | .canonicalDelta (strata := strata) lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body =>
    exact ⟨.canonicalDelta (strata := strata) lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body, fun policy => by simp only [RichObs.headDepth]⟩
  | .legacy child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.legacy child, fun policy => by simp only [RichObs.headDepth, depth]⟩
  | .code child =>
    obtain ⟨child, depth⟩ := child.relocateConstant destination newLocals τ
    exact ⟨.code child, fun policy => by simp only [RichObs.headDepth, depth]⟩
  | .route path child =>
    obtain ⟨child, depth⟩ := child.relocateConstant destination newLocals τ
    exact ⟨child, fun policy => by simp only [RichObs.headDepth, depth]⟩
  | .union first second =>
    obtain ⟨first, hf⟩ := first.relocateConstant destination newLocals τ
    obtain ⟨second, hs⟩ := second.relocateConstant destination newLocals τ
    exact ⟨.union first second, fun policy => by simp only [RichObs.headDepth, hf, hs]⟩
  | .view child change =>
    obtain ⟨child, depth⟩ := child.relocateConstant destination newLocals τ
    exact ⟨.view child change, fun policy => by simp only [RichObs.headDepth, depth]⟩
  | .action child change =>
    obtain ⟨child, depth⟩ := child.relocateConstant destination newLocals τ
    exact ⟨.action child change, fun policy => by simp only [RichObs.headDepth, depth]⟩
  | .select child member =>
    obtain ⟨child, depth⟩ := child.relocateConstant destination newLocals τ
    exact ⟨.select child member, fun policy => by simp only [RichObs.headDepth, depth]⟩
  | .pad child =>
    obtain ⟨child, depth⟩ := child.relocateConstant destination newLocals τ
    exact ⟨.pad child, fun policy => by simp only [RichObs.headDepth, depth]⟩
  | .unpad child =>
    obtain ⟨child, depth⟩ := child.relocateConstant destination newLocals τ
    exact ⟨.unpad child, fun policy => by simp only [RichObs.headDepth, depth]⟩
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

theorem OriginalRecordSource.RichCert.relocateConstant
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (destination : EndpointState sourceEnv U nextSource (.const name levels) nextAssigned)
    (newLocals : List Nat) (τ : Subst) :
    ∃ result : RichCert sourceEnv env U registry target destination newLocals τ relevant profile footprint, ∀ policy, result.headDepth policy = query.headDepth policy := by
  match query with
  | .legacy child =>
    obtain ⟨child, depth⟩ := child.relocateConstant newLocals τ
    exact ⟨.legacy child, fun policy => by simp only [RichCert.headDepth, depth]⟩
  | .observe child formed =>
    obtain ⟨child, depth⟩ := child.relocateConstant destination newLocals τ
    exact ⟨.observe child formed, fun policy => by simp only [RichCert.headDepth, depth]⟩
  | .route path child =>
    obtain ⟨child, depth⟩ := child.relocateConstant destination newLocals τ
    exact ⟨child, fun policy => by simp only [RichCert.headDepth, depth]⟩
  | .union first second =>
    obtain ⟨first, hf⟩ := first.relocateConstant destination newLocals τ
    obtain ⟨second, hs⟩ := second.relocateConstant destination newLocals τ
    exact ⟨.union first second, fun policy => by simp only [RichCert.headDepth, hf, hs]⟩
  | .pad child =>
    obtain ⟨child, depth⟩ := child.relocateConstant destination newLocals τ
    exact ⟨.pad child, fun policy => by simp only [RichCert.headDepth, depth]⟩
  | .down child =>
    obtain ⟨child, depth⟩ := child.relocateConstant destination newLocals τ
    exact ⟨.down child, fun policy => by simp only [RichCert.headDepth, depth]⟩
  | .map change child =>
    obtain ⟨child, depth⟩ := child.relocateConstant destination newLocals τ
    exact ⟨.map change child, fun policy => by simp only [RichCert.headDepth, depth]⟩
  | .support change child =>
    obtain ⟨child, depth⟩ := child.relocateConstant destination newLocals τ
    exact ⟨.support change child, fun policy => by simp only [RichCert.headDepth, depth]⟩
  | .select child member =>
    obtain ⟨child, depth⟩ := child.relocateConstant destination newLocals τ
    exact ⟨.select child member, fun policy => by simp only [RichCert.headDepth, depth]⟩
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

end
end Lean4Lean.AnchoredSource.Adapted
