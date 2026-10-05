import Lean4Lean.Theory.Typing.AnchoredProjectionDependencyObstruction

/-! A finite obstruction to rebuilding exact dependency trees from the root
queries of independent same-major observers. This checks the necessary row
coverage implication, not a new source projection grammar. The companion
certificate theorem below connects the surplus query to existing CodeCert
syntax rather than assuming arbitrary row certificates. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics

inductive FieldDependencyTree (n : Nat) where
  | node (selector : Nat) (output : Atom n) (children : List (FieldDependencyTree n))

def FieldDependencyTree.root : FieldDependencyTree n → Nat × Atom n
  | .node selector output _ => (selector, output)

def FieldDependencyTree.queries : FieldDependencyTree n → List (Nat × Atom n)
  | .node selector output children =>
    (selector, output) :: children.flatMap FieldDependencyTree.queries

def FieldDependencyTree.Decreasing : FieldDependencyTree n → Prop
  | .node selector _ children =>
    ∀ child ∈ children, child.root.1 < selector ∧ child.Decreasing

structure FieldDependencyRow (n : Nat) where
  query : Nat × Atom n
  inputs : List (Nat × Atom n)

/-- Every row input is an actual immediate subtree request; each subtree
must have its own selected covering row. There are no hidden admissions. -/
inductive FieldDependencyTree.Covered (rows : List (FieldDependencyRow n)) :
    FieldDependencyTree n → Prop where
  | node (selector : Nat) (output : Atom n) (children : List (FieldDependencyTree n))
      (selected : ⟨(selector, output), children.map FieldDependencyTree.root⟩ ∈ rows)
      (covered : ∀ child ∈ children, Covered rows child) :
      Covered rows (.node selector output children)

private def leaf (selector : Nat) (output : Atom n) : FieldDependencyTree n :=
  .node selector output []

private def rich (a b : Atom n) : FieldDependencyTree n := .node 1 a [leaf 0 b]
private def wanted (a c : Atom n) : FieldDependencyTree n := .node 2 c [leaf 1 a]

private def rows (a b c : Atom n) : List (FieldDependencyRow n) :=
  [⟨(0, b), []⟩, ⟨(1, a), [(0, b)]⟩, ⟨(2, c), []⟩, ⟨(2, c), [(1, a)]⟩]

/-- Strictly decreasing selectors and coverage of every requested root do
not suffice. The selector-1 child has an extra selector-0 dependency; its
retained row cannot cover the requested selector-1 leaf. Even supplying the
exact requested ROOT row for selector 2 does not repair the subtree. -/
theorem FieldDependencyTree.rootQueries_do_not_rebuild
    (a b c : Atom n) :
    (wanted a c).Decreasing ∧ (rich a b).Decreasing ∧ (leaf 2 c).Decreasing ∧
    (rich a b).Covered (rows a b c) ∧ (leaf 2 c).Covered (rows a b c) ∧
    (∀ query ∈ (wanted a c).queries,
      query ∈ (leaf 2 c).queries ++ (rich a b).queries) ∧
    ¬ (wanted a c).Covered (rows a b c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [wanted, leaf, Decreasing, root]
  · simp [rich, leaf, Decreasing, root]
  · simp [leaf, Decreasing]
  · refine .node _ _ _ (by simp [rows, root, leaf]) ?_
    intro child member
    simp only [List.mem_singleton] at member
    subst child
    exact .node _ _ _ (by simp [rows, leaf]) (by simp)
  · exact .node _ _ _ (by simp [rows, leaf]) (by simp)
  · simp [wanted, rich, leaf, queries]
  · intro covered
    cases covered with
    | node _ _ _ _ children =>
      have child := children (leaf 1 a) (List.mem_singleton_self _)
      cases child with
      | node _ _ _ selected _ => simp [rows] at selected

/-- The row mismatch can be produced by genuine current source code
certificates: an ignored earlier field may be observed or omitted without
changing the literal field-domain template or its output support. -/
theorem CodeCert.fieldDependency_surplus
    {env : VEnv} {U n : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst}
    {annotation : VExpr} {key : Key (n + 1)} {support : Profile (n + 1)}
    (domain : CodeCert env U registry target locals σ annotation support [])
    (guard : LambdaGuard env U registry target σ annotation key support)
    (admitted : Admitted env U registry target key (σ 0) (σ 0))
    {extra : Atom (n + 1)} (input : key.input = .singleton extra)
    {level : VLevel} (relevant : Relevant level true) :
    Nonempty (CodeCert env U registry target locals σ
      (.app (.lam annotation (.sort level)) (.bvar 0)) (.sort (n := n + 1) true)
      [(0, ⟨n + 1, .singleton extra⟩)]) ∧
    Nonempty (CodeCert env U registry target locals σ
      (.app (.lam annotation (.sort level)) (.bvar 0)) (.sort (n := n + 1) true) []) ∧
    ¬ Footprint.Available [(0, ⟨n + 1, .singleton extra⟩)] (fun _ => []) := by
  obtain ⟨strong, weak⟩ := CodeCert.fieldTemplate_surplus domain guard admitted relevant
  refine ⟨?_, weak, fun available => ?_⟩
  · simpa only [input] using strong
  · have impossible := available 0 ⟨n + 1, .singleton extra⟩ (List.mem_singleton_self _)
    cases impossible

end Lean4Lean.AnchoredSource.Adapted
