import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstantBounds

/-! The actual primitive constant header and universe dependency ledger. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

/-- Both actual universe instances survive the primitive dispatcher.
The left constant displays the seed; the right one displays `otherLevels`. -/
structure FamilyParameterLedger
    {sourceEnv : VEnv} {U : Nat} {name : Name} {levels : List VLevel}
    {ordered : sourceEnv.Ordered}
    (selection : RichHeaderSelection sourceEnv U name levels ordered) where
  otherLevels : List VLevel
  otherWF : ∀ level ∈ otherLevels, level.WF U
  equivalent : List.Forall₂ (· ≈ ·) selection.seed otherLevels
  displayed : levels = selection.seed ∨ levels = otherLevels

noncomputable def FamilyParameterLedger.dependencies
    {selection : RichHeaderSelection sourceEnv U name levels ordered}
    (ledger : FamilyParameterLedger selection) : List (SelectedParameterDependency sourceEnv U) :=
  constantParameterDependencies ordered name selection.seedWF ledger.otherWF ledger.equivalent

noncomputable def FamilyParameterLedger.weight
    {selection : RichHeaderSelection sourceEnv U name levels ordered}
    (ledger : FamilyParameterLedger selection) : Nat :=
  (selection.header.original.dependencyOrigin selection.header.ordered).weight +
    (ledger.dependencies.map (fun root => (root.root.original.dependencyOrigin root.ordered).weight)).sum

noncomputable def FamilyParameterLedger.pairWeight
    {selection : RichHeaderSelection sourceEnv U name levels ordered}
    (ledger : FamilyParameterLedger selection) : Nat :=
  (selection.header.original.dependencyOrigin selection.header.ordered).weight +
    2 * (ledger.dependencies.map (fun root => (root.root.original.dependencyOrigin root.ordered).weight)).sum

theorem FamilyParameterLedger.weight_le_pairWeight
    {selection : RichHeaderSelection sourceEnv U name levels ordered}
    (ledger : FamilyParameterLedger selection) : ledger.weight ≤ ledger.pairWeight := by
  simp only [weight, pairWeight]
  omega


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
