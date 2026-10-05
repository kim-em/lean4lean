import Lean4Lean.Theory.Typing.AnchoredOriginalParameterEqualities

namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

/-- The selected declaration cell keeps the actual preceding equality
trace. Its context is not reconstructed from the displayed telescope. -/
structure OriginalParameterCell
    (trace : OriginalContextEquality env U source destination) (index : Nat) (A B : VExpr) where
  tail : OriginalContextEquality env U (source.drop (index + 1)) (destination.drop (index + 1))
  level : VLevel
  original : Derivation env U (source.drop (index + 1)) A B (.sort level)
  retained : (⟨_, tail.context, A, B, .sort level, original⟩ : ParameterEqualityRoot env U) ∈ trace.roots
  tailRetained : ∀ root ∈ tail.roots, root ∈ trace.roots

theorem OriginalContextEquality.cellAt
    (trace : OriginalContextEquality env U source destination) (index : Nat)
    (sourceAt : source[index]? = some A) (destinationAt : destination[index]? = some B) :
    Nonempty (OriginalParameterCell trace index A B) := by
  induction trace generalizing index with
  | nil => simp at sourceAt
  | @cons source destination left right level tail original ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at sourceAt destinationAt
      subst A B
      exact ⟨⟨tail, level, original, List.mem_cons_self, fun _ member => List.mem_cons_of_mem _ member⟩⟩
    | succ index =>
      obtain ⟨cell⟩ := ih index sourceAt destinationAt
      exact ⟨⟨cell.tail, cell.level, cell.original, List.mem_cons_of_mem _ cell.retained,
        fun root member => List.mem_cons_of_mem _ (cell.tailRetained root member)⟩⟩

def OriginalParameterCell.root
    {trace : OriginalContextEquality env U source destination}
    (cell : OriginalParameterCell trace index A B) : ParameterEqualityRoot env U :=
  ⟨_, cell.tail.context, A, B, .sort cell.level, cell.original⟩


/-- A context-equality trace has precisely one closed cell. Retained
membership therefore identifies its original proof, not merely its type. -/
theorem OriginalContextEquality.closedRoot_unique
    (trace : OriginalContextEquality env U source destination)
    (left right : ParameterEqualityRoot env U)
    (leftMember : left ∈ trace.roots) (rightMember : right ∈ trace.roots)
    (leftClosed : left.source = []) (rightClosed : right.source = []) : left = right := by
  induction trace with
  | nil => cases leftMember
  | @cons source destination A B level tail original ih =>
    by_cases empty : source = []
    · subst source
      have destinationEmpty : destination = [] := by
        have lengths := tail.length_eq
        cases destination <;> simp_all
      subst destination
      cases tail
      exact (List.mem_singleton.mp leftMember).trans (List.mem_singleton.mp rightMember).symm
    · have leftTail : left ∈ tail.roots := by
        rcases List.mem_cons.mp leftMember with same | member
        · exact False.elim (empty ((congrArg ParameterEqualityRoot.source same).symm.trans leftClosed))
        · exact member
      have rightTail : right ∈ tail.roots := by
        rcases List.mem_cons.mp rightMember with same | member
        · exact False.elim (empty ((congrArg ParameterEqualityRoot.source same).symm.trans rightClosed))
        · exact member
      exact ih leftTail rightTail


/-- Declaration order and de Bruijn context order are opposite. This
producer selects the actual cell at declaration position `index` and
exposes its exact preceding telescope, including its original proof tree. -/
theorem OriginalContextEquality.declarationCellAt
    {left right : List VExpr}
    (trace : OriginalContextEquality env U left.reverse right.reverse)
    (index : Nat) (bounded : index < left.length)
    (leftAt : left[index]? = some A) (rightAt : right[index]? = some B) :
    ∃ cell : OriginalParameterCell trace (left.length - (index + 1)) A B,
      left.reverse.drop (left.length - (index + 1) + 1) = (left.take index).reverse ∧
      right.reverse.drop (left.length - (index + 1) + 1) = (right.take index).reverse ∧
      ∀ root ∈ cell.tail.roots, root ∈ trace.roots := by
  have lengths : left.length = right.length := by simpa using trace.length_eq
  obtain ⟨cell⟩ := trace.cellAt (left.length - (index + 1))
    ((List.getElem?_reverse' (by omega)).trans leftAt)
    ((List.getElem?_reverse' (by omega)).trans rightAt)
  refine ⟨cell, ?_, ?_, cell.tailRetained⟩
  · rw [List.drop_reverse]
    congr 2
    omega
  · rw [List.drop_reverse]
    congr 2
    omega

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
