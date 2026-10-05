import Lean4Lean.Theory.Typing.AnchoredAtomActionAdapter
import Lean4Lean.Theory.Typing.AnchoredFunctionViewOutput

/-! Function-shaped output actions retain their existing contravariant key
program and a finite action on the result. No inverse code action is used. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles AnchoredSource.Adapted
set_option backward.isDefEq.respectTransparency false

theorem OutputAction.normal_fn_inv
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {a b : Atom (n + 1)} (action : OutputAction env U registry Γ a b)
    {rightKey : Key n} {rightOutput : Atom n}
    (right : AdapterNormal.atom b = .fn rightKey rightOutput) :
    ∃ leftKey leftOutput, AdapterNormal.atom a = .fn leftKey leftOutput ∧
      Nonempty (KeyProgram env U registry Γ leftKey rightKey) ∧
      Nonempty (AtomAction env U registry Γ leftOutput rightOutput) := by
  match n, a, b, action with
  | _, _, _, .view v =>
    have adapter := v.toAdapter henv hscoped hΓ
    change AtomAdapter env U registry Γ _ _ at adapter
    rw [right] at adapter
    obtain ⟨leftKey, leftOutput, left, keys, _⟩ := adapter.fn_inv
    obtain ⟨output⟩ := v.normal_fn_output henv hscoped hΓ left right
    exact ⟨leftKey, leftOutput, left, keys, ⟨.view output⟩⟩
  | _, _, _, .code leaf formed =>
    have sorted := leaf.preservesSort formed
    rw [AdapterNormal.atom_sortable sorted] at right
    cases right
    obtain ⟨cover, member, impossible⟩ := sorted.2.2 _ (List.mem_singleton_self _)
    cases List.mem_singleton.mp member
    contradiction
  | _, _, _, .fn key child =>
    obtain ⟨rfl, rfl⟩ := AtomData.fn.inj right
    exact ⟨AdapterNormal.key key, _, rfl, ⟨.refl _⟩,
      ⟨.comp (.view ((AdapterNormal.view henv _).inverse henv))
        (.comp child.toAction (.view (AdapterNormal.view henv _)))⟩⟩
  | _, _, _, .comp first second =>
    obtain ⟨middleKey, middleOutput, middle, ⟨rightKeys⟩, ⟨rightAction⟩⟩ :=
      second.normal_fn_inv henv hscoped hΓ right
    obtain ⟨leftKey, leftOutput, left, ⟨leftKeys⟩, ⟨leftAction⟩⟩ :=
      first.normal_fn_inv henv hscoped hΓ middle
    exact ⟨leftKey, leftOutput, left, ⟨.comp leftKeys rightKeys⟩,
      ⟨.comp leftAction rightAction⟩⟩
termination_by sizeOf action

theorem AtomAction.normal_fn_inv
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {a b : Atom (n + 1)} (action : AtomAction env U registry Γ a b)
    {rightKey : Key n} {rightOutput : Atom n}
    (right : AdapterNormal.atom b = .fn rightKey rightOutput) :
    ∃ leftKey leftOutput, AdapterNormal.atom a = .fn leftKey leftOutput ∧
      Nonempty (KeyProgram env U registry Γ leftKey rightKey) ∧
      Nonempty (AtomAction env U registry Γ leftOutput rightOutput) :=
  action.outputs.normal_fn_inv henv hscoped hΓ right

end Lean4Lean.AnchoredSemantics
