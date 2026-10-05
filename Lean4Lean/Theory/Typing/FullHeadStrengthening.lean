import Lean4Lean.Theory.Typing.FullHeadReduction
import Lean4Lean.Theory.Typing.NativePrefixStrengthening
import Lean4Lean.Theory.Typing.QuotPrefixStrengthening

/-! Full head computation strengthens along context renamings. This does
not claim strengthening for structure eta expansion in the full relation. -/

namespace Lean4Lean.VEnv
open VExpr Params
open private native_const_spine_lift'_inv from Lean4Lean.Theory.Typing.NativePrefixStrengthening
open private case_lift'_mkApps from Lean4Lean.Theory.Typing.CaseReduction
variable [Params]

theorem FullWHRed.weak'_inv (hΓ : OnCtx Γ' (env.IsType univs))
    (W : Ctx.Lift' ρ Γ Γ') (H : FullWHRed Γ' (e.lift' ρ) rhs) :
    ∃ smallRhs, rhs = smallRhs.lift' ρ ∧ FullWHRed Γ e smallRhs := by
  generalize he : e.lift' ρ = actual at H
  induction H generalizing e with
  | core H =>
    subst he
    obtain ⟨small, hs, hr⟩ := H.weakU_inv hΓ W
    exact ⟨small, hs, .core hr⟩
  | delta H =>
    obtain ⟨args, rfl, rfl⟩ := native_const_spine_lift'_inv he.symm
    obtain ⟨small, hr, hs⟩ := H.weak'_inv henv hΓ W
    exact ⟨small, hs, .delta hr⟩
  | quotDelta H =>
    obtain ⟨args, rfl, rfl⟩ := native_const_spine_lift'_inv he.symm
    obtain ⟨small, hr, hs⟩ := H.weak'_inv henv hΓ W
    exact ⟨small, hs, .quotDelta hr⟩
  | @projIota family info index levels args type field hl ht hi hf =>
    let .proj family' index' major := e
    injection he with hfamily hindex hmajor
    subst family'
    subst index'
    obtain ⟨smallArgs, rfl, rfl⟩ := native_const_spine_lift'_inv hmajor.symm
    rw [List.getElem?_map] at hi
    obtain ⟨smallField, hsmall, rfl⟩ := Option.map_eq_some_iff.mp hi
    have hlarge : VExpr.WF env univs Γ'
        ((VExpr.proj family index (mkApps (.const info.ctorName levels) smallArgs)).lift' ρ) := by
      simpa only [VExpr.lift', case_lift'_mkApps] using (show VExpr.WF env univs Γ' _ from ⟨_, ht⟩)
    obtain ⟨smallType, hsmallType⟩ := (VExpr.WF.weak'_iff henv hΓ W).1 hlarge
    have hbigType := hsmallType.weak' henv.ordered W
    simp only [VExpr.lift', case_lift'_mkApps] at hbigType
    have hfield := hf.defeqU_r henv hΓ (ht.uniqU henv hΓ hbigType)
    have hsmallField := (HasType.weak'_iff henv hΓ W).1 hfield
    exact ⟨smallField, rfl, .projIota hl hsmallType hsmall hsmallField⟩
  | app H ih =>
    let .app .. := e
    cases he
    obtain ⟨small, hs, hr⟩ := ih rfl
    cases hs
    exact ⟨_, rfl, .app hr⟩
  | proj H ih =>
    let .proj .. := e
    cases he
    obtain ⟨small, hs, hr⟩ := ih rfl
    cases hs
    exact ⟨_, rfl, .proj hr⟩

theorem FullWHRedS.weak'_inv (hΓ : OnCtx Γ' (env.IsType univs))
    (W : Ctx.Lift' ρ Γ Γ') (H : FullWHRedS Γ' (e.lift' ρ) rhs) :
    ∃ smallRhs, rhs = smallRhs.lift' ρ ∧ FullWHRedS Γ e smallRhs := by
  induction H with
  | rfl => exact ⟨_, rfl, .rfl⟩
  | tail _ h ih =>
    obtain ⟨_, rfl, hs⟩ := ih
    obtain ⟨_, rfl, ht⟩ := h.weak'_inv hΓ W
    exact ⟨_, rfl, .tail hs ht⟩

end Lean4Lean.VEnv
