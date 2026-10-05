import Lean4Lean.Theory.Typing.AnchoredOriginalSortableTail
import Lean4Lean.Theory.Typing.AnchoredSortableFuture

/-! Target context transport renames the stored certificates, profiles,
realizations and available demands together. The original source formation
spine is preserved literally; no source derivation is weakened or reified.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalTail
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

private theorem cons_future (σ : Subst) (anchor : VExpr) (ρ : Lift) :
    (σ.cons anchor).lift_r ρ = (σ.lift_r ρ).cons (anchor.lift' ρ) := by
  funext i
  cases i <;> rfl

private theorem rename_push (head : List Need) (tail : Valuation) (ρ : Lift) :
    Valuation.rename ρ (Valuation.push head tail) =
      Valuation.push (head.map (Need.rename ρ)) (Valuation.rename ρ tail) := by
  funext i
  cases i <;> rfl

private noncomputable def SortableTailFits.futureWithContext
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {target future : List VExpr} {ρ : Lift}
    (insertion : FutureInsertion env U target future ρ)
    (fits : SortableTailFits sourceEnv env U registry target source locals σ τ available) :
    { shifted : SortableTailFits sourceEnv env U registry future source locals
        (σ.lift_r ρ) (τ.lift_r ρ) (Valuation.rename ρ available) //
      shifted.contextDerivation = fits.contextDerivation } := by
  induction fits with
  | nil => exact ⟨.nil, rfl⟩
  | @push source locals left right available A level N support input footprint x y
      tail originalDomain domain resources typed arguments needs bounded covered ih =>
    rw [cons_future, cons_future, rename_push]
    have renamedCovered : ∀ need ∈ needs.map (Need.rename ρ),
        ∀ atom ∈ (need.atGrade N).atoms, atom ∈ (Profile.rename ρ input).atoms := by
      intro need member atom selected
      obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
      rw [← Need.atGrade_rename] at selected
      obtain ⟨original, originalSelected, rfl⟩ := List.mem_map.mp selected
      exact List.mem_map_of_mem (covered old oldMember original originalSelected)
    refine ⟨.push ih.val originalDomain (domain.future henv insertion)
      (resources.rename ρ) (Profile.rename_hasType_iff.mpr typed) ?_
      (needs.map (Need.rename ρ)) ?_ renamedCovered, ?_⟩
    · simpa only [lift'_subst] using arguments.future henv insertion
    · intro need member
      obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
      exact bounded old oldMember
    · exact congrArg (fun context => ContextDerivation.cons context originalDomain) ih.property

/-- Transport only the target side, retaining the exact original context. -/
noncomputable def SortableTailFits.future
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {target future : List VExpr} {ρ : Lift}
    (insertion : FutureInsertion env U target future ρ)
    (fits : SortableTailFits sourceEnv env U registry target source locals σ τ available) :
    SortableTailFits sourceEnv env U registry future source locals
      (σ.lift_r ρ) (τ.lift_r ρ) (Valuation.rename ρ available) :=
  (fits.futureWithContext henv insertion).val

@[simp] theorem SortableTailFits.contextDerivation_future
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {target future : List VExpr} {ρ : Lift}
    (insertion : FutureInsertion env U target future ρ)
    (fits : SortableTailFits sourceEnv env U registry target source locals σ τ available) :
    (fits.future henv insertion).contextDerivation = fits.contextDerivation :=
  (fits.futureWithContext henv insertion).property

noncomputable def SortableTailPairedFits.future
    {sourceEnv env : VEnv} {U : Nat} {source : List VExpr}
    {context : ContextDerivation sourceEnv U source} (henv : env.Ordered)
    (insertion : FutureInsertion env U target futureTarget ρ)
    (frame : SortableTailPairedFits env registry target context locals σ τ available) :
    SortableTailPairedFits env registry futureTarget context locals
      (σ.lift_r ρ) (τ.lift_r ρ) (Valuation.rename ρ available) :=
  ⟨frame.forward.future henv insertion, frame.backward.future henv insertion,
    (frame.forward.contextDerivation_future henv insertion).trans frame.forwardContext,
    (frame.backward.contextDerivation_future henv insertion).trans frame.backwardContext⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalTail
