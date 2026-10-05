import Lean4Lean.Theory.Typing.AnchoredOriginalParameterSchedules
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyParameterLedger

/-! Select the actual primitive constant's header and parameter ledger
together, before any semantic query or normalization replay. The right
endpoint preserves the original seed and its separate displayed instance. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

theorem primitiveHeaderSelection_retained
    (ordered : sourceEnv.Ordered)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expressionEq : expression = .const name levels) (primitive : reference.Primitive) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      ∃ ledger : FamilyParameterLedger selection,
        assigned = selection.info.type.instL selection.seed ∧
        ledger.pairWeight < (reference.dependencyOrigin ordered).weight := by
  cases reference with
  | left original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl otherWF levelWF lookup wf count equiv closed ambient =>
      let selection : RichHeaderSelection sourceEnv U name levels ordered :=
        ⟨_, lookup, _, wf, Lean4Lean.List.Forall₂.rfl (fun _ _ => by rfl)⟩
      let ledger : FamilyParameterLedger selection := ⟨_, otherWF, equiv, Or.inl rfl⟩
      exact ⟨selection, ledger, rfl,
        Derivation.constantParameters_header_twice_weight_lt ordered lookup wf otherWF count equiv
          levelWF closed ambient⟩
  | right original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl wf count levelWF lookup otherWF equiv closed ambient =>
      let selection : RichHeaderSelection sourceEnv U name levels ordered := ⟨_, lookup, _, wf, equiv⟩
      let ledger : FamilyParameterLedger selection := ⟨_, otherWF, equiv, Or.inr rfl⟩
      exact ⟨selection, ledger, rfl,
        Derivation.constantParameters_header_twice_weight_lt ordered lookup wf otherWF count equiv
          levelWF closed ambient⟩

/-- The same retained primitive packet is paid by its actual exposed
constant occurrence. No interpretation or new choice of a header occurs. -/
theorem constantHeaderSelection_retained
    (ordered : sourceEnv.Ordered)
    (node : EndpointState sourceEnv U source (.const name levels) assigned) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      ∃ ledger : FamilyParameterLedger selection,
        (constantPrefix node).type = selection.info.type.instL selection.seed ∧
        ledger.pairWeight ≤ (node.dependencyOrigin ordered).weight := by
  let head := constantPrefix node
  obtain ⟨selection, ledger, assignedEq, bound⟩ :=
    primitiveHeaderSelection_retained ordered head.reference rfl head.primitive
  exact ⟨selection, ledger, assignedEq,
    Nat.le_trans (Nat.le_of_lt bound) (head.route.dependency_weight_le ordered)⟩

/-- A family constant selected inside a major's assigned formation keeps
its ledger bound under that same original major root. -/
theorem locatedHeaderSelection_retained
    (ordered : sourceEnv.Ordered)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (location : Located root node) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      ∃ ledger : FamilyParameterLedger selection,
        (constantPrefix node).type = selection.info.type.instL selection.seed ∧
        ledger.pairWeight ≤ (node.dependencyOrigin ordered).weight ∧
        ledger.pairWeight ≤ (root.dependencyOrigin ordered).weight := by
  obtain ⟨selection, ledger, assignedEq, bound⟩ := constantHeaderSelection_retained ordered node
  exact ⟨selection, ledger, assignedEq, bound,
    Nat.le_trans bound (location.dependency_weight_le ordered)⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
