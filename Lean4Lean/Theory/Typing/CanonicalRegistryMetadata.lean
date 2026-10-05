import Lean4Lean.Theory.Typing.CanonicalDataRegistryScope
import Lean4Lean.Theory.Typing.InductiveLemmas

/-! Concrete selectors for the functional environment metadata. Case entries
retain precisely the closed-header eligibility already required by `elimDF`.
No abstract schema is added to an ordinary native installation. -/
namespace Lean4Lean.VEnv
open VExpr
variable {env : VEnv} {leftName rightName : Name} {leftInfo rightInfo : VProjectionInfo}
set_option Elab.async false

/-- The literal target of a constructor telescope fixes its structure family.
This uses raw constructor shape and constant lookup, not type injectivity. -/
theorem Ordered.projectionConstructor_family (ordered : env.Ordered)
    (left : env.projections leftName leftInfo) (right : env.projections rightName rightInfo)
    (same : leftInfo.ctorName = rightInfo.ctorName) :
    leftName = rightName ∧ leftInfo = rightInfo := by
  have leftLookup := ordered.projectionConstructor left
  have rightLookup := ordered.projectionConstructor right
  rw [same, rightLookup] at leftLookup
  have typeEq := congrArg VConstant.type (Option.some.inj leftLookup)
  obtain ⟨leftDecl, leftType, leftCtor, _, _, leftNameEq, _, _, _, _, _, _, leftTypeEq,
    _, _, _, leftRaw, _⟩ := ordered.projectionShape left
  obtain ⟨rightDecl, rightType, rightCtor, _, _, rightNameEq, _, _, _, _, _, _, rightTypeEq,
    _, _, _, rightRaw, _⟩ := ordered.projectionShape right
  obtain ⟨leftDomains, leftResult, leftShape, _, _, leftHead, leftArity⟩ := leftRaw.forallArity
  obtain ⟨rightDomains, rightResult, rightShape, _, _, rightHead, rightArity⟩ := rightRaw.forallArity
  have ctorEq : leftCtor.type = rightCtor.type := leftTypeEq.trans (typeEq.symm.trans rightTypeEq.symm)
  have lengthEq : leftDomains.length = rightDomains.length := by
    rw [← leftArity, ← rightArity, ctorEq]
  have leftParse := VExpr.takeForalls_wrapForalls leftDomains leftResult
  have rightParse := VExpr.takeForalls_wrapForalls rightDomains rightResult
  rw [← leftShape, ctorEq, lengthEq, rightShape, rightParse] at leftParse
  have resultEq := congrArg Prod.snd (Option.some.inj leftParse)
  have familyEq : leftName = rightName := by
    rw [← leftNameEq, ← rightNameEq]
    exact (VExpr.const.inj (leftHead.symm.trans
      ((congrArg (fun expression => expression.getAppFnArgs.1) resultEq.symm).trans rightHead))).1
  exact ⟨familyEq, ordered.projections_unique (familyEq ▸ left) right⟩

end Lean4Lean.VEnv

namespace Lean4Lean.CanonicalDataHead
open VEnv InductiveSignature
variable {env : VEnv}
set_option Elab.async false

noncomputable def environmentProjections (env : VEnv) (name : Name) : Option VProjectionInfo := by
  classical
  exact if present : ∃ info, env.projections name info then some (Classical.choose present) else none

noncomputable def environmentStructures (env : VEnv) (name : Name) : Option VProjectionEntry := by
  classical
  exact if present : ∃ entry : VProjectionEntry,
      env.projections entry.typeName entry.info ∧ entry.info.ctorName = name then
    some (Classical.choose present) else none

noncomputable def environmentCases (env : VEnv) (block : Name) (owner : Nat) : Option CaseEntry := by
  classical
  exact if present : ∃ entry : CaseEntry, env.eliminators block entry.schema ∧ entry.owner.val = owner ∧
      ∃ header, entry.schema.genericType entry.owner = some header ∧ header.Closed then
    some (Classical.choose present) else none

theorem environmentProjections_sound
    (lookup : environmentProjections env name = some info) : env.projections name info := by
  classical
  unfold environmentProjections at lookup
  split at lookup
  · rename_i present
    cases lookup; exact Classical.choose_spec present
  · cases lookup

theorem environmentProjections_complete (ordered : env.Ordered)
    (present : env.projections name info) : environmentProjections env name = some info := by
  classical
  unfold environmentProjections
  rw [dif_pos ⟨info, present⟩]
  exact congrArg some (ordered.projections_unique (Classical.choose_spec _) present)

theorem environmentStructures_sound
    (lookup : environmentStructures env name = some entry) :
    env.projections entry.typeName entry.info ∧ entry.info.ctorName = name := by
  classical
  unfold environmentStructures at lookup
  split at lookup
  · rename_i present
    cases lookup; exact Classical.choose_spec present
  · cases lookup

theorem environmentStructures_complete (ordered : env.Ordered)
    (present : env.projections name info) :
    environmentStructures env info.ctorName = some ⟨name, info⟩ := by
  classical
  unfold environmentStructures
  rw [dif_pos ⟨⟨name, info⟩, present, rfl⟩]
  apply congrArg some
  have selected := Classical.choose_spec (show ∃ entry : VProjectionEntry,
    env.projections entry.typeName entry.info ∧ entry.info.ctorName = info.ctorName from
      ⟨⟨name, info⟩, present, rfl⟩)
  obtain ⟨nameEq, infoEq⟩ := ordered.projectionConstructor_family selected.1 present selected.2
  generalize choiceEq : Classical.choose _ = chosen at nameEq infoEq ⊢
  cases chosen with
  | mk chosenName chosenInfo =>
    cases nameEq
    cases infoEq
    rfl

theorem environmentCases_sound
    (lookup : environmentCases env block owner = some entry) :
    env.eliminators block entry.schema ∧ entry.owner.val = owner ∧
      ∃ header, entry.schema.genericType entry.owner = some header ∧ header.Closed := by
  classical
  unfold environmentCases at lookup
  split at lookup
  · rename_i present
    cases lookup; exact Classical.choose_spec present
  · cases lookup

theorem environmentCases_complete (formed : env.WF)
    {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    (present : env.eliminators block schema)
    (header : schema.genericType owner = some type) (closed : type.Closed) :
    environmentCases env block owner.val = some ⟨schema, owner⟩ := by
  classical
  unfold environmentCases
  have entryExists : ∃ entry : CaseEntry, env.eliminators block entry.schema ∧
      entry.owner.val = owner.val ∧ ∃ header,
      entry.schema.genericType entry.owner = some header ∧ header.Closed :=
    ⟨⟨schema, owner⟩, present, rfl, type, header, closed⟩
  rw [dif_pos entryExists]
  apply congrArg some
  generalize selectedEq : Classical.choose entryExists = selected
  have selectedData : env.eliminators block selected.schema ∧ selected.owner.val = owner.val ∧
      ∃ header, selected.schema.genericType selected.owner = some header ∧ header.Closed := by
    rw [← selectedEq]
    exact Classical.choose_spec entryExists
  cases selected with
  | mk selectedSchema selectedOwner =>
    obtain ⟨registered, indexEq, _⟩ := selectedData
    cases formed.eliminators_unique registered present
    cases Fin.ext indexEq
    rfl

end Lean4Lean.CanonicalDataHead
