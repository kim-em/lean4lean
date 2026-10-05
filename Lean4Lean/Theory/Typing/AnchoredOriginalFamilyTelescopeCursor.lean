import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyApplyPiChainReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyNormalizationRoute

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

private theorem takeForalls_reconstruct
    (parsed : expression.takeForalls count = some (domains, tail)) :
    expression = VExpr.wrapForalls domains tail := by
  induction count generalizing expression domains with
  | zero =>
    change some ([], expression) = some (domains, tail) at parsed
    cases Option.some.inj parsed
    rfl
  | succ count ih =>
    cases expression <;> simp only [takeForalls] at parsed <;> try contradiction
    case forallE A B =>
      simp only [bind, Option.bind_eq_some_iff] at parsed
      obtain ⟨⟨ds, result⟩, rest, equal⟩ := parsed
      cases equal
      exact congrArg (VExpr.forallE A) (ih rest)

private theorem wrapForalls_levels (domains : List VExpr) (tail : VExpr) (levels : List VLevel) :
    (VExpr.wrapForalls domains tail).instL levels =
      VExpr.wrapForalls (domains.map (·.instL levels)) (tail.instL levels) := by
  induction domains with
  | nil => rfl
  | cons domain domains ih => exact congrArg (VExpr.forallE (domain.instL levels)) ih

/-- The remaining source telescope is retained before any capture
substitution. Its domains therefore still belong to the original header. -/
def FamilyTelescopeCursor (domains : List VExpr) (tail : VExpr) (index : Nat)
    (header : OriginalPiTypeRouteSide U common) : Prop :=
  VExpr.forallE header.A header.B = VExpr.wrapForalls (domains.drop index) tail

theorem FamilyTelescopeCursor.initial
    (packet : OriginalProjectionParameters sourceEnv U name info levels)
    (positive : 0 < info.nparams) (common : List VExpr) :
    FamilyTelescopeCursor (packet.shape.familyParams.map (·.instL levels))
      (packet.shape.familyTail.instL levels) 0 (normalizedFamilyRouteSide packet positive common) := by
  change VExpr.forallE (normalizedFamilyPrefix packet positive).domainExpression
      (normalizedFamilyPrefix packet positive).bodyExpression = _
  rw [← (normalizedFamilyPrefix packet positive).shape,
    takeForalls_reconstruct packet.shape.familyTake, wrapForalls_levels]
  rfl

/-- A nonfinal source parameter exposes the next literal Pi directly from
the parsed header. The exact domain/body equalities returned by the checked
history successor preserve this cursor at the next index. -/
theorem FamilyTelescopeCursor.next
    {header : OriginalPiTypeRouteSide U common}
    (cursor : FamilyTelescopeCursor domains tail index header)
    (remaining : index + 1 < domains.length) :
    ∃ nextDomain nextBody,
      header.B = .forallE nextDomain nextBody ∧
      ∀ nextHeader : OriginalPiTypeRouteSide U common,
        nextHeader.A = nextDomain → nextHeader.B = nextBody →
        FamilyTelescopeCursor domains tail (index+1) nextHeader := by
  have currentBound : index < domains.length := Nat.lt_trans (Nat.lt_succ_self index) remaining
  have splitCurrent : domains.drop index = domains[index] :: domains.drop (index+1) :=
    List.drop_eq_getElem_cons currentBound
  have splitNext : domains.drop (index+1) = domains[index+1] :: domains.drop (index+2) :=
    List.drop_eq_getElem_cons remaining
  unfold FamilyTelescopeCursor at cursor
  rw [splitCurrent] at cursor
  have bodyEq : header.B = VExpr.wrapForalls (domains.drop (index+1)) tail :=
    (VExpr.forallE.inj cursor).2
  refine ⟨domains[index+1], VExpr.wrapForalls (domains.drop (index+2)) tail, ?_, ?_⟩
  · rw [bodyEq, splitNext]
    rfl
  · intro nextHeader domainEq nextBodyEq
    unfold FamilyTelescopeCursor
    rw [domainEq, nextBodyEq, splitNext]
    rfl

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
