import Lean4Lean.Theory.Typing.EquationControlMeasure

/-! Finite world mass has a genuinely well-founded replacement order: one
world may be replaced by any finite number of strictly smaller worlds.
The list presentation retains multiplicities. Commutative normalization and
idempotent environment joins are separate from this foundational theorem. -/
namespace Lean4Lean.VEnv.EquationWorldPolynomial
set_option Elab.async false

/-- Contextual finite replacement, before quotienting by permutation. -/
inductive Replace (r : α → α → Prop) : List α → List α → Prop where
  | head (smaller : ∀ x ∈ replacement, r x parent) :
      Replace r (replacement ++ tail) (parent :: tail)
  | tail (step : Replace r left right) : Replace r (parent :: left) (parent :: right)

private theorem accessible_cons {r : α → α → Prop} {a : α}
    (ha : Acc r a) : ∀ tail, Acc (Replace r) tail → Acc (Replace r) (a :: tail) := by
  induction ha with
  | intro a predecessors lower =>
    intro tail ht
    induction ht with
    | intro tail predecessorsTail lowerTail =>
      apply Acc.intro
      intro next step
      cases step with
      | head smaller =>
        rename_i replacement
        have tailAcc : Acc (Replace r) tail := .intro tail predecessorsTail
        induction replacement with
        | nil => exact tailAcc
        | cons b bs ih =>
          exact lower b (smaller b (by simp)) (bs ++ tail)
            (ih (fun x hx => smaller x (by simp [hx])))
      | tail step => exact lowerTail _ step

/-- Finite replacement is well founded for every well-founded world order.
No order-completeness, ordinal axioms, or finite branching is assumed. -/
theorem replace_wellFounded {r : α → α → Prop} (wf : WellFounded r) :
    WellFounded (Replace r) := by
  constructor
  intro xs
  induction xs with
  | nil => exact .intro [] (fun _ step => by cases step)
  | cons x xs ih => exact accessible_cons (wf.apply x) xs ih

abbrev Less (r : α → α → Prop) := Relation.TransGen (Replace r)

theorem wellFounded {r : α → α → Prop} (wf : WellFounded r) :
    WellFounded (Less r) := (replace_wellFounded wf).transGen

/-- An arbitrary finite amount of strictly lower-prefix mass fits below
one unit of the selected world, independently of its coefficients. -/
theorem lower_mass {r : α → α → Prop} {world : α} {mass : List α}
    (lower : ∀ x ∈ mass, r x world) : Less r mass [world] := by
  simpa using Relation.TransGen.single (Replace.head (tail := []) lower)

theorem Less.cons {r : α → α → Prop} {xs ys : List α}
    (step : Less r xs ys) (a : α) : Less r (a :: xs) (a :: ys) := by
  induction step with
  | single h => exact .single (.tail h)
  | tail _ h ih => exact .tail ih (.tail h)

private theorem erase_nonempty {r : α → α → Prop} (a : α) (xs : List α) :
    Less r [] (a :: xs) := by
  have one : Replace r xs (a :: xs) := .head (replacement := []) (by simp)
  cases xs with
  | nil => exact .single one
  | cons b bs => exact (erase_nonempty b bs).tail one

/-- Descending expanded coefficients. Equal adjacent keys represent a
coefficient greater than one; the empty list is the zero polynomial. -/
def Descending (r : α → α → Prop) (xs : List α) : Prop :=
  xs.Pairwise (fun a b => r b a ∨ b = a)

abbrev Polynomial (r : α → α → Prop) := { xs : List α // Descending r xs }

def LexLess (r : α → α → Prop) (p q : Polynomial r) : Prop :=
  List.Lex r p.val q.val

private theorem lex_replacement {r : α → α → Prop}
    (transitive : ∀ {a b c}, r a b → r b c → r a c)
    {xs ys : List α} (descending : Descending r xs) (less : List.Lex r xs ys) :
    Less r xs ys := by
  induction less with
  | nil => exact erase_nonempty _ _
  | @rel a xs b ys ab =>
    have lower : ∀ x ∈ a :: xs, r x b := by
      intro x hx
      rcases List.mem_cons.mp hx with same | member
      · subst x; exact ab
      · rcases (List.pairwise_cons.mp descending).1 x member with xa | same
        · exact transitive xa ab
        · subst x; exact ab
    have replace := lower_mass lower
    cases ys with
    | nil => exact replace
    | cons y ys => exact replace.trans ((erase_nonempty y ys).cons b)
  | cons _ ih => exact (ih (List.pairwise_cons.mp descending).2).cons _

/-- Lexicographic comparison of finite descending polynomials is well
founded, despite unbounded degree, length, and coefficients. -/
theorem lex_wellFounded {r : α → α → Prop} (wf : WellFounded r)
    (transitive : ∀ {a b c}, r a b → r b c → r a c) :
    WellFounded (LexLess r) := by
  apply Subrelation.wf (r := InvImage (Less r) Subtype.val)
  · intro p q h
    exact lex_replacement (r := r) transitive p.property h
  · exact InvImage.wf Subtype.val (wellFounded wf)

abbrev Worlds (count : Nat) := List (EquationControlMeasure.Key count)
abbrev WorldLess (count : Nat) := Less (@EquationControlMeasure.Less count)

theorem world_wellFounded (count : Nat) : WellFounded (WorldLess count) :=
  wellFounded (EquationControlMeasure.wellFounded count)

end Lean4Lean.VEnv.EquationWorldPolynomial
