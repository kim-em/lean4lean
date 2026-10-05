import Lean4Lean.Theory.Typing.AnchoredDataLaws

/-! Frozen requests compare arbitrary retained endpoints through their common
anchor. Composition needs no injectivity of the constructor's assigned type
and no equality between independently chosen argument representations. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalDataHead.Registry}
  {lower : Relations n}

/-- An existing request supplies its exact anchor at the same retained
support. In particular, eta parameters can use constructor-request anchors
without converting an unrelated family demand into their support. -/
theorem RequestAdmission.anchorDiagonal
    (laws : LowerEquality env U registry lower) (hscoped : registry.Scoped)
    (admitted : RequestAdmission env U lower Γ request left right) :
    RequestAdmission env U lower Γ request request.anchor request.anchor := by
  obtain ⟨anchor, _, typed, formed, code, before, _⟩ := admitted
  have self := laws.trans hscoped before (laws.symm before)
  exact ⟨anchor.hasType.1, anchor.hasType.1, typed, formed, code, self, self⟩

theorem Arguments.anchorDiagonal
    (laws : LowerEquality env U registry lower) (hscoped : registry.Scoped)
    (arguments : Arguments env U lower Γ requests left right) :
    Arguments env U lower Γ requests (requests.map (·.anchor)) (requests.map (·.anchor)) := by
  induction arguments with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.anchorDiagonal laws hscoped) ih

theorem RequestAdmission.joinAnchors
    (laws : LowerEquality env U registry lower) (hscoped : registry.Scoped)
    (first : RequestAdmission env U lower Γ request left firstRight)
    (second : RequestAdmission env U lower Γ request secondLeft right) :
    RequestAdmission env U lower Γ request left right := by
  obtain ⟨anchor, _, typed, formed, code, before, _⟩ := first
  obtain ⟨nextAnchor, nextPair, _, _, _, nextBefore, nextAcross⟩ := second
  exact ⟨anchor, anchor.symm.trans (nextAnchor.trans nextPair), typed, formed, code,
    before, laws.trans hscoped (laws.symm before)
      (laws.trans hscoped nextBefore nextAcross)⟩

theorem Arguments.joinAnchors
    (laws : LowerEquality env U registry lower) (hscoped : registry.Scoped)
    (first : Arguments env U lower Γ requests left firstRight)
    (second : Arguments env U lower Γ requests secondLeft right) :
    Arguments env U lower Γ requests left right := by
  induction first generalizing secondLeft right with
  | nil => cases second; exact .nil
  | cons head tail ih =>
    cases second with
    | cons next rest => exact .cons (head.joinAnchors laws hscoped next) (ih rest)

end Lean4Lean.AnchoredSemantics.RankedData
