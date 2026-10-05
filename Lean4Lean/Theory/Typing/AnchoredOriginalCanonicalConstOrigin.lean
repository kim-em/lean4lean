import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalCodeOwner
import Lean4Lean.Theory.Typing.AnchoredOriginalDisplay

/-! Query-independent provenance for a closed constant subterm in an actual
canonical owner's earlier source. The named owner may differ from the displayed
constant. The shared observation constructor adds its positive recursive query;
this record contains neither a semantic answer nor a caller substitution. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalEndpointFactor OriginalClosureMeasure
set_option Elab.async false

structure CanonicalConstOrigin (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (strata : EquationStratification env)
    (name : Name) (levels : List VLevel) where
  ownerName : Name
  owner : CanonicalCodeOwner env registry strata ownerName
  info : VConstant
  lookup : owner.selected.origin.source.constants name = some info
  assignedLevels : List VLevel
  assignedWF : ∀ level ∈ assignedLevels, level.WF U
  levelsWF : ∀ level ∈ levels, level.WF U
  equivalent : List.Forall₂ (· ≈ ·) assignedLevels levels
  typeClosed : info.type.Closed
  site : EndpointRef owner.selected.origin.source U [] (.const name levels)
    (info.type.instL assignedLevels)

/-- All metadata comes from one actual primitive. The closed reference is
assembled from that primitive's own closed equality premise, used twice. -/
structure ClosedPrimitiveConstant (sourceEnv : VEnv) (U : Nat)
    (name : Name) (levels : List VLevel) (assigned : VExpr) where
  info : VConstant
  lookup : sourceEnv.constants name = some info
  assignedLevels : List VLevel
  assignedWF : ∀ level ∈ assignedLevels, level.WF U
  levelsWF : ∀ level ∈ levels, level.WF U
  equivalent : List.Forall₂ (· ≈ ·) assignedLevels levels
  assignedEq : assigned = info.type.instL assignedLevels
  site : EndpointRef sourceEnv U [] (.const name levels) (info.type.instL assignedLevels)

theorem EndpointRef.closedPrimitiveConstant
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expressionEq : expression = .const name levels) (primitive : reference.Primitive) :
    Nonempty (ClosedPrimitiveConstant sourceEnv U name levels assigned) := by
  cases reference with
  | left original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl otherWF levelWF lookup wf count equiv closed ambient =>
      refine ⟨{
        info := _
        lookup := lookup
        assignedLevels := _
        assignedWF := wf
        levelsWF := wf
        equivalent := ?_
        assignedEq := rfl
        site := .left (.constDF lookup wf otherWF count equiv levelWF closed closed) }⟩
      apply List.Forall₂.rfl
      intros
      rfl
  | right original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl wf count levelWF lookup otherWF equiv closed ambient =>
      exact ⟨{
        info := _
        lookup := lookup
        assignedLevels := _
        assignedWF := wf
        levelsWF := otherWF
        equivalent := equiv
        assignedEq := rfl
        site := .right (.constDF lookup wf otherWF count equiv levelWF closed closed) }⟩


end Lean4Lean.AnchoredSource.Adapted
