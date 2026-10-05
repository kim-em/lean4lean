import Lean4Lean.Theory.Typing.CanonicalDataHeadRenaming

/-! Forward source substitution for the actual constructor-sensitive
dispatchers. Reflection is deliberately not asserted: a substituted variable
may reveal a new constructor. Source observation factoring must retain that
constructor demand at the variable leaf. -/

namespace Lean4Lean.CanonicalDataHead
open VExpr InductiveSignature
set_option backward.isDefEq.respectTransparency false

def Selected.subst (selected : Selected) (σ : Subst) : Selected :=
  { selected with arguments := selected.arguments.map (·.subst σ) }

private theorem rigid_spine_subst {head expression : VExpr} {arguments : List VExpr}
    (shape : expression.getAppFnArgs = (head, arguments))
    (rigid : head.getAppFnArgs = (head, [])) (fixed : head.subst σ = head) :
    (expression.subst σ).getAppFnArgs = (head, arguments.map (·.subst σ)) := by
  have rebuild := VExpr.mkApps_getAppFnArgs_eq expression
  change mkApps expression.getAppFnArgs.1 expression.getAppFnArgs.2 = expression at rebuild
  rw [shape] at rebuild
  rw [← rebuild, subst_mkApps, fixed]
  exact spine_mkApps_exact _ _ rigid

theorem select_subst (chosen : select registry function = some selected) (σ : Subst) :
    select registry (function.subst σ) = some (selected.subst σ) := by
  unfold select at chosen ⊢
  split at chosen <;> try contradiction
  · rename_i name levels arguments shape
    rw [rigid_spine_subst shape rfl rfl]
    simp only
    split at chosen
    · rename_i data lookup
      split at chosen <;> try contradiction
      rename_i named
      rw [if_pos named]
      cases chosen
      rfl
    · rename_i lookup
      split at chosen <;> try contradiction
      rename_i installed
      rw [if_pos installed]
      cases chosen
      rfl
  · rename_i block owner levels arguments shape
    rw [rigid_spine_subst shape rfl rfl]
    simp only
    split at chosen <;> try contradiction
    rename_i entry lookup
    split at chosen <;> try contradiction
    rename_i owned
    rw [if_pos owned]
    cases chosen
    rfl

/-- Once the major is a constructor spine, substitution preserves both
success and failure of each tag/arity rule check. -/
theorem Rule.run_subst_constructor (rule : Rule) (closed : rule.equation.rhs.Closed)
    (selected : Selected) (σ : Subst)
    (shape : major.getAppFnArgs = (.const name levels, arguments)) :
    rule.run (selected.subst σ) (major.subst σ) =
      (rule.run selected major).map (·.subst σ) := by
  unfold Rule.run
  rw [rigid_spine_subst shape rfl rfl, shape]
  simp only [Selected.subst, List.length_map]
  split
  · simp only [Option.map_some, subst_mkApps,
      (closed.instL (ls := selected.levels)).subst_eq Subst.Fixes.zero,
      Rule.captures, List.map_append, List.map_take, List.map_drop, List.length_map]
  · rfl

theorem Rule.run_constructor {rule : Rule} {selected : Selected} {major result : VExpr}
    (reduced : rule.run selected major = some result) :
    ∃ levels arguments, major.getAppFnArgs = (.const rule.constructor levels, arguments) ∧
      arguments.length = rule.constructorArity := by
  unfold Rule.run at reduced
  split at reduced <;> try contradiction
  rename_i name levels arguments shape
  split at reduced <;> try contradiction
  rename_i checks
  exact ⟨levels, arguments, checks.1 ▸ shape, checks.2.1⟩

/-- Every successful ordinary-iota dispatch survives source substitution,
with the same selected constructor equation and substituted finite captures. -/
theorem directIota_subst (selected : Selected)
    (closed : ∀ rule ∈ selected.rules, rule.equation.rhs.Closed)
    (reduced : directIota selected major = some result) (σ : Subst) :
    directIota (selected.subst σ) (major.subst σ) = some (result.subst σ) := by
  obtain ⟨rule, member, selectedRule⟩ := List.exists_of_findSome?_eq_some reduced
  obtain ⟨levels, arguments, shape, _⟩ := Rule.run_constructor selectedRule
  have allRules : ∀ rules : List Rule, (∀ rule ∈ rules, rule.equation.rhs.Closed) →
      rules.findSome? (fun rule => rule.run (selected.subst σ) (major.subst σ)) =
        (rules.findSome? (fun rule => rule.run selected major)).map (·.subst σ) := by
    intro rules scopes
    induction rules with
    | nil => rfl
    | cons next rest ih =>
      simp only [List.findSome?]
      rw [next.run_subst_constructor (scopes next List.mem_cons_self) selected σ shape]
      cases next.run selected major with
      | some result => rfl
      | none => exact ih (fun r hr => scopes r (List.mem_cons_of_mem _ hr))
  have natural := allRules selected.rules closed
  change directIota (selected.subst σ) (major.subst σ) =
    (directIota selected major).map (·.subst σ) at natural
  simpa only [reduced, Option.map_some] using natural

theorem project_subst (reduced : project registry typeName index major = some result) (σ : Subst) :
    project registry typeName index (major.subst σ) = some (result.subst σ) := by
  unfold project at reduced ⊢
  simp only [bind, Option.bind_eq_some_iff] at reduced
  obtain ⟨info, lookup, reduced⟩ := reduced
  rw [lookup]
  simp only [bind, Option.bind_some]
  split at reduced <;> try contradiction
  rename_i name levels arguments shape
  rw [rigid_spine_subst shape rfl rfl]
  simp only
  split at reduced <;> try contradiction
  rename_i same
  rw [if_pos same, List.getElem?_map, reduced]
  rfl

/-- Structure dispatch uses projections of the exact source major, so it
commutes with arbitrary substitution, including substitution for that major. -/
theorem etaIota_subst (registry : Registry) (selected : Selected)
    (closed : ∀ rule ∈ selected.rules, rule.equation.rhs.Closed)
    (major : VExpr) (σ : Subst) :
    etaIota registry (selected.subst σ) (major.subst σ) =
      (etaIota registry selected major).map (·.subst σ) := by
  cases rules : selected.rules with
  | nil => simp [etaIota, Selected.subst, rules]
  | cons rule rest =>
    cases rest with
    | cons next rest => simp [etaIota, Selected.subst, rules]
    | nil =>
      have rhsClosed := (closed rule (rules ▸ List.mem_singleton_self _)).instL
        (ls := selected.levels)
      simp only [etaIota, Selected.subst, rules, List.length_map]
      cases reverse : registry.structureConstructors rule.constructor with
      | none => rfl
      | some entry =>
        simp only [bind, Option.bind_some]
        cases lookup : registry.projections entry.typeName with
        | none => rfl
        | some info =>
          simp only [Option.bind_some]
          split
          · simp only [Option.map_some, subst_mkApps,
              rhsClosed.subst_eq Subst.Fixes.zero, List.map_append, List.map_take,
              List.map_map, Function.comp_def, subst]
          · rfl

end Lean4Lean.CanonicalDataHead
