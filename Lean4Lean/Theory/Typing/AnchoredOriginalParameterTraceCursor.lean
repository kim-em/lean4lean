import Lean4Lean.Theory.Typing.AnchoredOriginalParameterCells

/-! Deterministic cursors into the retained declaration equality trees.
Each successor uses the original equality cell above the identical stored
prefix, so a generated frame can be extended without changing its context
proof or reconstructing an equality derivation. -/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

namespace OriginalContextEquality

def drop (trace : OriginalContextEquality env U source destination) (count : Nat) :
    OriginalContextEquality env U (source.drop count) (destination.drop count) :=
  match trace, count with
  | .nil, 0 => .nil
  | .nil, count+1 => by simpa using (OriginalContextEquality.nil (env := env) (U := U))
  | .cons tail original, 0 => .cons tail original
  | .cons tail _, count+1 => tail.drop count

@[simp] theorem drop_zero (trace : OriginalContextEquality env U source destination) :
    trace.drop 0 = trace := by cases trace <;> rfl

@[simp] theorem drop_cons_succ
    (tail : OriginalContextEquality env U source destination)
    (original : Derivation env U source A B (.sort level)) (count : Nat) :
    (OriginalContextEquality.cons tail original).drop (count+1) = tail.drop count := rfl

theorem drop_roots_subset (trace : OriginalContextEquality env U source destination) (count : Nat) :
    ∀ root ∈ (trace.drop count).roots, root ∈ trace.roots := by
  induction trace generalizing count with
  | nil => cases count <;> simp [drop, roots]
  | cons tail original ih =>
    cases count with
    | zero => exact fun _ member => member
    | succ count => exact fun root member => List.mem_cons_of_mem _ (ih count root member)

/-- A cell is tied to the deterministic remaining original trace. Its
predecessor and successor are the same proof trees used by the cursor. -/
structure Cell (trace : OriginalContextEquality env U source destination)
    (index : Nat) (A B : VExpr) where
  level : VLevel
  original : Derivation env U (source.drop (index+1)) A B (.sort level)
  next : HEq (trace.drop index) (OriginalContextEquality.cons (trace.drop (index+1)) original)
  next_context : HEq (trace.drop index).context
    (ContextDerivation.cons (trace.drop (index+1)).context (.left original))
  retained : (⟨_, (trace.drop (index+1)).context, A, B, .sort level, original⟩ :
    ParameterEqualityRoot env U) ∈ trace.roots

theorem cell (trace : OriginalContextEquality env U source destination) (index : Nat)
    (sourceAt : source[index]? = some A) (destinationAt : destination[index]? = some B) :
    Nonempty (trace.Cell index A B) := by
  induction trace generalizing index with
  | nil => simp at sourceAt
  | @cons source destination left right level tail original ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at sourceAt destinationAt
      subst A B
      exact ⟨⟨level, original, by simp only [drop, drop_zero]; rfl,
        by simp only [drop, drop_zero, context]; rfl, by cases tail <;> exact List.mem_cons_self⟩⟩
    | succ index =>
      obtain ⟨selected⟩ := ih index sourceAt destinationAt
      exact ⟨⟨selected.level, selected.original, selected.next, selected.next_context,
        List.mem_cons_of_mem _ selected.retained⟩⟩

def Cell.root {trace : OriginalContextEquality env U source destination}
    (selected : Cell trace index A B) : ParameterEqualityRoot env U :=
  ⟨_, (trace.drop (index+1)).context, A, B, .sort selected.level, selected.original⟩

/-- Declaration order is opposite to context order. This selects an actual
cell and fixes both context proofs used by a successive capture. -/
theorem declarationCell
    {left right : List VExpr}
    (trace : OriginalContextEquality env U left.reverse right.reverse)
    (index : Nat) (bounded : index < left.length)
    (leftAt : left[index]? = some A) (rightAt : right[index]? = some B) :
    ∃ selected : trace.Cell (left.length - (index+1)) A B,
      left.reverse.drop (left.length - (index+1)+1) = (left.take index).reverse ∧
      right.reverse.drop (left.length - (index+1)+1) = (right.take index).reverse := by
  have lengths : left.length = right.length := by simpa using trace.length_eq
  obtain ⟨selected⟩ := trace.cell (left.length - (index+1))
    ((List.getElem?_reverse' (by omega)).trans leftAt)
    ((List.getElem?_reverse' (by omega)).trans rightAt)
  refine ⟨selected, ?_, ?_⟩
  · rw [List.drop_reverse]
    congr 2
    omega
  · rw [List.drop_reverse]
    congr 2
    omega

/-- The initial cursor is the actual empty trace. -/
theorem drop_length (trace : OriginalContextEquality env U source destination) :
    HEq (trace.drop source.length) (OriginalContextEquality.nil (env := env) (U := U)) := by
  induction trace with
  | nil => rfl
  | cons tail original ih => exact ih

end OriginalContextEquality
end Lean4Lean.AnchoredSource.OriginalClosureMeasure
