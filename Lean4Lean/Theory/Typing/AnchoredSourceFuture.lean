import Lean4Lean.Theory.Typing.AnchoredSourceBinder

/-! Future target contexts preserve the same finite source demands, with
only their frozen target profiles renamed. Actual source type certificates
and raw substitution evidence are transported together. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

def Valuation.rename (ρ : Lift) (available : Valuation) : Valuation :=
  fun index => (available index).map (Need.rename ρ)

theorem Footprint.Available.rename
    (h : Footprint.Available required available) (ρ : Lift) :
    Footprint.Available (Footprint.rename ρ required) (Valuation.rename ρ available) := by
  intro i need hm
  obtain ⟨⟨j, original⟩, hj, he⟩ := List.mem_map.mp hm
  cases he
  exact List.mem_map_of_mem (h _ _ hj)

theorem Fits.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {source target future : List VExpr} {ρ : Lift}
    (insertion : FutureInsertion env U target future ρ)
    {locals : List Nat} {left right : Subst} {available : Valuation}
    (fits : Fits env U registry source target locals left right available) :
    Fits env U registry source future locals (left.lift_r ρ) (right.lift_r ρ)
      (Valuation.rename ρ available) := by
  constructor
  intro index need hm sourceType lookup
  obtain ⟨original, horiginal, he⟩ := List.mem_map.mp hm
  subst need
  obtain ⟨entry⟩ := fits.entry index original horiginal sourceType lookup
  refine ⟨⟨entry.support.rename ρ, Footprint.rename ρ entry.footprint,
    entry.certificate.future henv insertion, entry.available.rename ρ,
    Profile.rename_hasType_iff.mpr entry.typed, ?_⟩⟩
  simpa only [Need.rename, Subst.lift_r, lift'_subst] using
    entry.related.future henv insertion

end Lean4Lean.AnchoredSource

namespace Lean4Lean.VEnv
open VExpr
set_option backward.isDefEq.respectTransparency false

/-- Rename the target of an actual paired raw substitution; source lookup
annotations and their original formation proofs remain unchanged. -/
theorem Ctx.SubstEq.future
    {env : VEnv} {U : Nat} {source target future : List VExpr} {ρ : Lift}
    (henv : env.Ordered) (insertion : FutureInsertion env U target future ρ)
    {left right : Subst}
    (substitutions : Ctx.SubstEq env U target left right source) :
    Ctx.SubstEq env U future (left.lift_r ρ) (right.lift_r ρ) source := by
  induction substitutions with
  | nil => exact .nil
  | cons _ formation pair ih =>
    apply Ctx.SubstEq.cons ih formation
    simpa only [lift'_subst, Subst.lift_r_tail, Subst.head, Subst.lift_r] using
      pair.weak' henv insertion.weakening

theorem Ctx.SubstEq.symm
    {env : VEnv} {U : Nat} {source target : List VExpr} {left right : Subst}
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source) :
    Ctx.SubstEq env U target right left source := by
  induction substitutions with
  | nil => exact .nil
  | cons tail formation pair ih =>
    apply Ctx.SubstEq.cons ih formation
    have types := formation.substDF henv tail.wf hTarget tail
    simp only [subst_sort] at types
    exact IsDefEq.defeqDF types pair.symm

theorem Ctx.SubstEq.right
    {env : VEnv} {U : Nat} {source target : List VExpr} {left right : Subst}
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source) :
    Ctx.SubstEq env U target right right source :=
  (substitutions.symm henv hTarget).left

end Lean4Lean.VEnv
