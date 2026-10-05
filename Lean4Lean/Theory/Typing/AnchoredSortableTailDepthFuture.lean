import Lean4Lean.Theory.Typing.AnchoredSortableStageBudgets
import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepthFuture
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableFuture

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

private noncomputable def SortableTailFits.futureWithDepth
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {target future : List VExpr} {ρ : Lift}
    (insertion : FutureInsertion env U target future ρ)
    (fits : SortableTailFits sourceEnv env U registry target source locals σ τ available) :
    { shifted : SortableTailFits sourceEnv env U registry future source locals
        (σ.lift_r ρ) (τ.lift_r ρ) (Valuation.rename ρ available) //
      shifted.contextDerivation = fits.contextDerivation ∧
        ∀ current, shifted.nativeDepth current = fits.nativeDepth current } := by
  induction fits with
  | nil => exact ⟨.nil, rfl, fun _ => rfl⟩
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
    · constructor
      · exact congrArg (fun context => ContextDerivation.cons context originalDomain) ih.property.1
      · intro current
        simp only [SortableTailFits.nativeDepth, SortableCert.nativeDepth_future, ih.property.2]


/-- A single future frame retains both original context identities and every
caller depth control. -/
theorem SortableTailPairedFits.future_allDepth
    {sourceEnv env : VEnv} {U : Nat} {source : List VExpr}
    {context : ContextDerivation sourceEnv U source} (henv : env.Ordered)
    (insertion : FutureInsertion env U target futureTarget ρ)
    (frame : SortableTailPairedFits env registry target context locals σ τ available) :
    ∃ shifted : SortableTailPairedFits env registry futureTarget context locals
      (σ.lift_r ρ) (τ.lift_r ρ) (Valuation.rename ρ available),
      ∀ current, shifted.nativeDepth current = frame.nativeDepth current := by
  let forward := frame.forward.futureWithDepth henv insertion
  let backward := frame.backward.futureWithDepth henv insertion
  refine ⟨⟨forward.val, backward.val,
    forward.property.1.trans frame.forwardContext,
    backward.property.1.trans frame.backwardContext⟩, ?_⟩
  intro current
  change max (forward.val.nativeDepth current) (backward.val.nativeDepth current) = _
  rw [forward.property.2, backward.property.2]
  rfl

end Lean4Lean.AnchoredSource.Adapted.OriginalTail
